import FolDialect
import Foundation
import IR
import Lowering
import Reader

private let baseDirectory = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
    .deletingLastPathComponent().appendingPathComponent("base")

struct Options {
    let emit: String?
    let through: String?
    let theorems: [String]?
    let skip: [String]
    let threads: Int
}

func lower(_ root: String, _ options: Options) {
    let start = Date()
    var unit: IR.Unit
    var named: Set<String>
    var population: Set<String>
    var citedNamed: Set<String>
    do {
        var reader = try Reader(try Export(root: root))
        let names = try reader.population.map { try claimName(reader.name(of: $0)!) }
        var selection = reader.population
        if let theorems = options.theorems {
            let byName = Dictionary(uniqueKeysWithValues: zip(names, reader.population))
            selection = theorems.map { name in
                guard let theorem = byName[name] else { fail("lower: no named theorem \(name)", 2) }
                return theorem
            }
        }
        for s in options.skip where !zfSessions.contains(s) { fail("lower: no session \(s)", 2) }
        selection = selection.filter { !options.skip.contains(session(of: $0.theory)!) }
        unit = try reader.unit(of: selection)
        population = Set(names)
        named = Set(try selection.map { try claimName(reader.name(of: $0)!) })
        citedNamed = Set(try reader.cited.compactMap { try reader.name(of: $0).map(claimName) })
    } catch {
        stopped(error)
    }
    let taken = unit.statements.map(\.name) + unit.refused.map(\.name)
    let beyond = taken.count(where: { !named.contains($0) && population.contains($0) })
    let outside = taken.count(where: { !population.contains($0) && citedNamed.contains($0) })
    let boxes = taken.count(where: { !population.contains($0) && !citedNamed.contains($0) })
    let read = Date()
    let definitions = unit.definitions.count
    let lowering: Pipeline
    let texts: [String]
    do {
        let names = BaseStatement.allCases.map(\.rawValue)
        texts = try baseTexts(baseDirectory)
        lowering = pipeline(try Base(try parse(statements: names, from: texts, in: &unit.table)))
    } catch {
        fail("base: \(error)", 1)
    }
    let complete = options.through == nil || options.through == lowering.passes.last?.name
    if options.emit != nil, !complete { fail(
        "lower: --emit needs a complete run, not one through \(options.through!)",
        2,
    ) }
    let stages: [Stage]
    do {
        stages = try lowering.run(&unit, through: options.through)
    } catch {
        fail("pipeline: \(error)", 1)
    }
    let lowered = unit.statements.filter { named.contains($0.name) }
    if named.count == population.count {
        print("named theorems, all ZF sessions: \(named.count)")
    } else {
        print("named theorems selected: \(named.count) of \(population.count), citing \(beyond) others")
    }
    print("  with \(outside) theorems they cite outside the ZF sessions, \(boxes) boxes binding a proposition and "
        + "\(definitions) definitions they reach")
    if complete {
        print(
            "lowered to fol-zfc through \(lowering.passes.map(\.name).joined(separator: ", ")): \(lowered.count) — each proof concludes its statement, by ID"
        )
        print("  and \(unit.statements.count - lowered.count) of the theorems and boxes cited, and lemmas")
    } else {
        let lemmas = unit.statements.filter { $0.lemma != nil }
        print(
            "through \(options.through!): \(lowered.count) named theorems stand, and \(unit.statements.count - lowered.count) "
                +
                "other statements, \(lemmas.count) of them lemmas requested, \(lemmas.count(where: { $0.proof != nil })) proved"
        )
    }
    print("definitions read by the pass owning their constant: \(unit.definitions.count) of \(definitions)")
    let defs = unit.statements.count(where: { $0.defines != nil })
    let refusedDefs = unit.refused.count(where: { $0.name.hasSuffix("_DEF") && !named.contains($0.name) })
    let refusedLemmas = unit.refused.count(where: { $0.refusal == .lemmaUnbuilt && !$0.name.hasSuffix("_DEF") })
    print(
        "constants' @defs stated: \(defs), refused: \(refusedDefs); lemmas requested and refused, unbuilt: \(refusedLemmas)"
    )
    print("refused, named: \(unit.refused.count(where: { named.contains($0.name) }))")
    var statements = [String: Int]()
    var held = [String: [String: Int]]()
    var nouns = [String: String]()
    for r in unit.refused where named.contains(r.name) {
        let group: String
        let noun: String
        let found: [String]
        switch r.refusal {
        case .noOwner(let ps): (group, noun, found) = ("no owner", "patterns", ps.map { "\($0)" })
        case .unbuilt(let pass, let ps): (group, noun, found) = ("\(pass), unbuilt", "patterns", ps.map { "\($0)" })
        case .lemmaUnbuilt: (group, noun, found) = ("registry, unbuilt", "", [])
        case .letterOffSpine(let ps): (group, noun, found) = ("a letter off its spine", "patterns", ps.map { "\($0)" })
        case .cites(let cited): (group, noun, found) = ("cites a refused statement", "statements", [cited])
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
    print(String(
        format: "table: %d nodes; read %.1f s, lowered %.1f s",
        unit.table.count,
        read.timeIntervalSince(start),
        Date().timeIntervalSince(read),
    ))
    print("  stages: " + stages.map { "\($0.name) \(String(format: "%.1f", $0.seconds)) s" }.joined(separator: ", "))
    guard let directory = options.emit else { return }
    let emitting = Date()
    let emission: Emission
    do {
        emission = try emit(unit, to: URL(fileURLWithPath: directory), base: texts, threads: options.threads)
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
    var statements = [String: Statement]()
    for s in unit.statements { statements[s.name] = s }
    var rows = [String: (count: Int, written: Int, tree: Int, dag: Int)]()
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
