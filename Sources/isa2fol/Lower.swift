import FolDialect
import Foundation
import IR
import Lowering
import Reader

private let baseDirectory = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
    .deletingLastPathComponent().appendingPathComponent("base")

func lower(_ root: String, emitTo directory: String?) {
    let start = Date()
    var unit: IR.Unit, named: Set<String>
    do {
        var reader = try Reader(try Export(root: root))
        unit = try reader.unit()
        named = Set(try reader.population.map { try claimName(reader.name(of: $0)!) })
    } catch {
        stopped(error)
    }
    let read = Date(), outside = unit.statements.count + unit.refused.count - named.count, definitions = unit.definitions.count
    let lowering: Pipeline, texts: [String]
    do {
        let names = BaseStatement.allCases.map(\.rawValue)
        texts = try baseTexts(baseDirectory)
        lowering = pipeline(try Base(try parse(statements: names, from: texts, in: &unit.table)))
    } catch {
        fail("base: \(error)", 1)
    }
    do {
        try lowering.run(&unit)
    } catch {
        fail("pipeline: \(error)", 1)
    }
    let lowered = unit.statements.filter { named.contains($0.name) }
    print("named theorems, all ZF sessions: \(named.count)")
    print("  with \(outside) theorems they cite outside the ZF sessions and \(definitions) definitions they reach")
    print("lowered to fol-zfc through \(lowering.passes.map(\.name).joined(separator: ", ")): \(lowered.count) — each proof concludes its statement, by ID")
    print("  and \(unit.statements.count - lowered.count) of the theorems cited outside and lemmas")
    print("definitions read by the pass owning their constant: \(unit.definitions.count) of \(definitions)")
    let defs = unit.statements.filter { $0.defines != nil }.count
    let refusedDefs = unit.refused.filter { $0.name.hasSuffix("_DEF") && !named.contains($0.name) }.count
    let refusedLemmas = unit.refused.filter { $0.refusal == .lemmaUnbuilt && !$0.name.hasSuffix("_DEF") }.count
    print("constants' @defs stated: \(defs), refused: \(refusedDefs); lemmas requested and refused, unbuilt: \(refusedLemmas)")
    print("refused, named: \(unit.refused.filter { named.contains($0.name) }.count)")
    var statements: [String: Int] = [:], held: [String: [String: Int]] = [:], nouns: [String: String] = [:]
    for r in unit.refused where named.contains(r.name) {
        let (group, noun, found): (String, String, [String])
        switch r.refusal {
        case let .noOwner(ps): (group, noun, found) = ("no owner", "patterns", ps.map { "\($0)" })
        case let .unbuilt(pass, ps): (group, noun, found) = ("\(pass), unbuilt", "patterns", ps.map { "\($0)" })
        case .lemmaUnbuilt: (group, noun, found) = ("registry, unbuilt", "", [])
        case let .letterOffSpine(ps): (group, noun, found) = ("a letter off its spine", "patterns", ps.map { "\($0)" })
        case let .cites(cited): (group, noun, found) = ("cites a refused statement", "statements", [cited])
        case .unread: (group, noun, found) = ("not read", "", [])
        }
        statements[group, default: 0] += 1
        nouns[group] = noun
        for p in found { held[group, default: [:]][p, default: 0] += 1 }
    }
    let groups = ["no owner"] + lowering.passes.map { "\($0.name), unbuilt" }
        + ["registry, unbuilt", "a letter off its spine", "cites a refused statement", "not read"]
    for group in groups {
        guard let n = statements[group] else { continue }
        let counts = held[group] ?? [:]
        print("  \(group): \(n)" + (counts.isEmpty ? "" : ", naming \(counts.count) \(nouns[group]!)"))
        let ranked = counts.keys.sorted { (counts[$0]!, $1) > (counts[$1]!, $0) }
        for p in ranked.prefix(10) { print("    \(counts[p]!)\t\(p)") }
        if ranked.count > 10 { print("    … \(ranked.count - 10) more") }
    }
    print(String(format: "table: %d nodes; read %.1f s, lowered %.1f s",
                 unit.table.count, read.timeIntervalSince(start), Date().timeIntervalSince(read)))
    guard let directory else { return }
    let emitting = Date(), emission: Emission
    do {
        emission = try emit(unit, to: URL(fileURLWithPath: directory), base: texts)
    } catch {
        fail("emit: \(error)", 1)
    }
    report(emission, unit, directory, Date().timeIntervalSince(emitting))
}

private func report(_ e: Emission, _ unit: IR.Unit, _ directory: String, _ seconds: TimeInterval) {
    let sum = { (f: (EmittedPart) -> Int) in e.parts.map(f).reduce(0, +) }
    print("emitted to \(directory) in \(e.parts.count) parts: \(sum(\.claims)) claims, \(sum(\.schemas)) schemas, "
          + "\(sum(\.definitions)) @defs, \(sum(\.bytes)) bytes, \(String(format: "%.1f", seconds)) s; "
          + "check with scripts/check-unit.sh \(directory)")
    var statements: [String: Statement] = [:]
    for s in unit.statements { statements[s.name] = s }
    var rows: [String: (count: Int, written: Int, tree: Int, dag: Int)] = [:]
    let add = { (a: Int, b: Int) -> Int in
        let (sum, overflow) = a.addingReportingOverflow(b)
        return overflow ? Int.max : sum
    }
    for s in e.statements {
        guard let statement = statements[s.name] else { continue }
        let kind = statement.defines != nil ? "@def" : statement.lemma.map { Lowering.kind(of: $0) } ?? "theorem"
        let r = rows[kind] ?? (0, 0, 0, 0)
        rows[kind] = (r.count + 1, add(r.written, s.written), add(r.tree, s.tree), add(r.dag, s.dag))
    }
    let total = rows.values.reduce((count: 0, written: 0, tree: 0, dag: 0)) {
        ($0.count + $1.count, add($0.written, $1.written), add($0.tree, $1.tree), add($0.dag, $1.dag))
    }
    print("steps by kind: statements, written, as a tree, distinct")
    for kind in rows.keys.sorted(by: { (rows[$0]!.written, $1) > (rows[$1]!.written, $0) }) {
        let r = rows[kind]!
        print("    \(kind): \(r.count), \(r.written), \(r.tree), \(r.dag)")
    }
    print("    all: \(total.count), \(total.written), \(total.tree), \(total.dag)")
}
