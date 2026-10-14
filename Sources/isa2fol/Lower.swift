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
    var statements: [String: Int] = [:], held: [String: [Pattern: Int]] = [:]
    for r in unit.refused where named.contains(r.name) {
        let (group, found): (String, [Pattern])
        switch r.refusal {
        case let .noOwner(ps): (group, found) = ("no owner", ps)
        case let .unbuilt(pass, ps): (group, found) = ("\(pass), unbuilt", ps)
        case .lemmaUnbuilt: (group, found) = ("registry, unbuilt", [])
        case .cites: (group, found) = ("cites a refused statement", [])
        case .unread: (group, found) = ("not read", [])
        }
        statements[group, default: 0] += 1
        for p in found { held[group, default: [:]][p, default: 0] += 1 }
    }
    let groups = ["no owner"] + pipeline.passes.map { "\($0.name), unbuilt" }
        + ["registry, unbuilt", "cites a refused statement", "not read"]
    for group in groups {
        guard let n = statements[group] else { continue }
        let counts = held[group] ?? [:]
        print("  \(group): \(n)" + (counts.isEmpty ? "" : ", naming \(counts.count) patterns"))
        let ranked = counts.keys.sorted { (counts[$0]!, "\($1)") > (counts[$1]!, "\($0)") }
        for p in ranked.prefix(10) { print("    \(counts[p]!)\t\(p)") }
        if ranked.count > 10 { print("    … \(ranked.count - 10) more") }
    }
    print(String(format: "table: %d nodes; read %.1f s, lowered %.1f s",
                 unit.table.count, read.timeIntervalSince(start), Date().timeIntervalSince(read)))
}
