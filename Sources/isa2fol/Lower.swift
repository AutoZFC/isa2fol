import Foundation
import IR
import Lowering
import Reader

func lower(_ root: String) {
    let start = Date()
    var unit: IR.Unit
    let notRead: Int
    do {
        (unit, notRead) = try readUnit(root)
    } catch {
        stopped(error)
    }
    let read = Date(), named = unit.statements.count + notRead
    let passes: [Pass] = [Guard()]
    do {
        try Pipeline(passes: passes).run(&unit)
    } catch {
        fail("pipeline: \(error)", 1)
    }
    print("named theorems, all ZF sessions: \(named)")
    print("  not proved by the reader: \(notRead)")
    print("lowered through \(passes.map(\.name).joined(separator: ", ")): \(unit.statements.count) — each proof concludes its statement, by ID")
    var refused: [String: Int] = [:]
    for r in unit.refused { refused["\(r.pass): \(String("\(r.refusal)".prefix { $0 != "(" }))", default: 0] += 1 }
    print("refused: \(unit.refused.count)")
    for key in refused.keys.sorted() { print("  \(key): \(refused[key]!)") }
    print(String(format: "table: %d nodes; read %.1f s, lowered %.1f s",
                 unit.table.count, read.timeIntervalSince(start), Date().timeIntervalSince(read)))
}

private func readUnit(_ root: String) throws -> (IR.Unit, Int) {
    var reader = try Reader(try Export(root: root))
    var statements: [Statement] = [], notRead = 0
    for theorem in reader.population {
        guard case let .proved(statement, proof) = try reader.read(theorem) else {
            notRead += 1
            continue
        }
        guard let name = reader.name(of: theorem) else { fail("\(theorem): in the population but unnamed", 1) }
        statements.append(Statement(name: try claimName(name), root: statement, proof: proof))
    }
    return (IR.Unit(table: reader.table, statements: statements), notRead)
}
