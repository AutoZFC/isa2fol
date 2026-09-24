import Testing
@testable import IR

@Test func anUnknownOperandIsAnError() throws {
    var b = Builder()
    #expect(throws: IRRefusal.unknownOperand(OpID(raw: 99))) {
        try b.append(.isaTrueprop(OpID(raw: 99)), to: b.graph.root)
    }
}

/// A fixpoint is reached when a walk changes nothing; no count of rewrites bounds it.
@Test func aConvergentPassNeedsNoCap() throws {
    struct ToFol: RewritePattern {
        func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
        func rewrite(_ id: OpID, _ b: inout Builder) throws {
            guard case let .isaFree(n, _) = b.graph.op(id) else { return }
            let new = try b.insert(.folVar(n), before: id)
            b.replaceAllUses(of: id, with: new)
            b.erase(id)
        }
    }
    var b = Builder()
    for i in 0..<1000 { _ = try b.append(.isaFree("v\(i)", .i), to: b.graph.root) }
    try PatternPass(name: "to-fol", patterns: [ToFol()]).run(&b)
    #expect(!b.graph.liveOps.contains { if case .isaFree = b.graph.op($0) { return true }; return false })
    #expect(b.graph.liveOps.count == 1000)
}
