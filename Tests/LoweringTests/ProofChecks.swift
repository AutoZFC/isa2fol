import FolDialect
import Foundation
import IR
import Lowering
import Testing

/// Every `hyp(k, a)` against the assumption it names, shifted by the term binders between: the table computes each
/// step's
/// conclusion but never compares a hypothesis with its binder, so a wrong one would surface only at the kernel.
func misscoped(_ proof: NodeID, in t: Table) throws -> [NodeID] {
    struct Assumed: Hashable { let formula: NodeID
        let depth: Int
    }
    struct Visit: Hashable { let id: NodeID
        let assumed: [Assumed]
        let depth: Int
    }
    var wrong = [NodeID]()
    var seen = Set<Visit>()
    func walk(_ id: NodeID, _ assumed: [Assumed], _ depth: Int, _ t: inout Table) throws {
        guard seen.insert(Visit(id: id, assumed: assumed, depth: depth)).inserted else { return }
        switch t[id] {
        case .hyp(let k, let a):
            guard k < assumed.count else { wrong.append(id)
                return
            }
            let h = assumed[assumed.count - 1 - k]
            if try shift(h.formula, by: depth - h.depth, in: &t) != a { wrong.append(id) }

        case .folImpliesIntro(let a, let body), .folNotIntro(let a, let body):
            try walk(body, assumed + [Assumed(formula: a, depth: depth)], depth, &t)

        case .folClassicalAbsurd(let a, let body):
            try walk(body, assumed + [Assumed(formula: try t.intern(.folNot(a)), depth: depth)], depth, &t)

        case .isaExElim(_, let p, let body), .folExistsElim(let p, let body):
            try walk(p, assumed, depth, &t)
            guard let c = t.conclusion(of: p) else { wrong.append(id)
                return
            }
            switch t[c] {
            case .ifolEx(_, let inner), .folExists(let inner):
                try walk(body, assumed + [Assumed(formula: inner, depth: depth + 1)], depth + 1, &t)
            default: wrong.append(id)
            }

        case .isaAllIntro(_, let body), .folForallIntro(let body):
            try walk(body, assumed, depth + 1, &t)

        case .use:
            return

        default:
            var children = [NodeID]()
            t[id].forEachChild { c, _ in children.append(c) }
            for c in children where t.conclusion(of: c) != nil { try walk(c, assumed, depth, &t) }
        }
    }
    var table = t
    try walk(proof, [], 0, &table)
    return wrong
}

private let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
    .deletingLastPathComponent()

private func script(_ name: String, _ arguments: [String]) throws -> (status: Int32, output: String) {
    let p = Process()
    p.executableURL = URL(fileURLWithPath: "/bin/bash")
    p.arguments = [repo.appendingPathComponent("scripts/\(name)").path] + arguments
    let out = Pipe()
    p.standardOutput = out
    p.standardError = out
    try p.run()
    let text = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    p.waitUntilExit()
    return (p.terminationStatus, text)
}

private struct BaseNotValid: Error { let output: String }

private let baseLibraries = Result { () throws -> URL in
    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-base-\(getpid())")
    let (status, output) = try script("check-base.sh", [dir.path])
    guard status == 0 else { throw BaseNotValid(output: output) }
    return dir
}

/// Each claim, lowered by Fol, and each definition emitted as one part and checked by `check-unit.sh` against base's
/// libraries: valid only when every claim is Proved, exit 0, stderr empty.
func kernelChecks(
    _ claims: [(name: String, root: NodeID, proof: NodeID)],
    definitions: [(Defined, NodeID)] = [],
    in t: inout Table,
) throws {
    var statements = [Statement]()
    let fol = Fol(base: try base(in: &t))
    for (c, root) in definitions {
        statements.append(Statement(defining: c, root: try fol.run([root], [], in: &t)[0]))
    }
    for c in claims {
        let lowered = try fol.run([c.root, c.proof], [], in: &t)
        statements.append(Statement(name: c.name, root: lowered[0], proof: lowered[1], theory: "Test"))
    }
    try kernelChecks(IR.Unit(table: t, statements: statements))
}

/// A unit the pipeline lowered, emitted and checked as `kernelChecks(_:definitions:in:)` checks its claims.
func kernelChecks(_ unit: IR.Unit) throws {
    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-kernel-\(UUID().uuidString)")
    defer { try? FileManager.default.removeItem(at: dir) }
    _ = try emit(unit, to: dir, base: try baseTexts(repo.appendingPathComponent("base")))
    let (status, output) = try script("check-unit.sh", [dir.path, try baseLibraries.get().path])
    #expect(status == 0, "check-unit.sh:\n\(output)")
}
