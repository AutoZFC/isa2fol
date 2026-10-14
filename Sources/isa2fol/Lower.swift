import Foundation
import IR
import Lowering
import Reader

func lower(_ root: String) {
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
    do {
        try pipeline.run(&unit)
    } catch {
        fail("pipeline: \(error)", 1)
    }
    let lowered = unit.statements.filter { named.contains($0.name) }
    print("named theorems, all ZF sessions: \(named.count)")
    print("  with \(outside) theorems they cite outside the ZF sessions and \(definitions) definitions they reach")
    print("lowered to fol-zfc through \(pipeline.passes.map(\.name).joined(separator: ", ")): \(lowered.count) — each proof concludes its statement, by ID")
    print("  and \(unit.statements.count - lowered.count) of the theorems cited outside and lemmas")
    print("definitions read by the pass owning their constant: \(unit.definitions.count) of \(definitions)")
    print("refused, named: \(unit.refused.filter { named.contains($0.name) }.count)")
    var statements: [String: Int] = [:], held: [String: [String: Int]] = [:], nouns: [String: String] = [:]
    for r in unit.refused where named.contains(r.name) {
        let (group, noun, found): (String, String, [String])
        switch r.refusal {
        case let .noOwner(ps): (group, noun, found) = ("no owner", "patterns", ps.map { "\($0)" })
        case let .unbuilt(pass, ps): (group, noun, found) = ("\(pass), unbuilt", "patterns", ps.map { "\($0)" })
        case .lemmaUnbuilt: (group, noun, found) = ("registry, unbuilt", "", [])
        case let .cites(cited): (group, noun, found) = ("cites a refused statement", "statements", [cited])
        case .unread: (group, noun, found) = ("not read", "", [])
        }
        statements[group, default: 0] += 1
        nouns[group] = noun
        for p in found { held[group, default: [:]][p, default: 0] += 1 }
    }
    let groups = ["no owner"] + pipeline.passes.map { "\($0.name), unbuilt" }
        + ["registry, unbuilt", "cites a refused statement", "not read"]
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
}
