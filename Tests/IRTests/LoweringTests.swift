import Testing
@testable import IR

private struct LowerFree: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaFree(n) = b.graph.op(id) else { return }
        let old = b.graph.node(id).results[0]
        let new = try b.insert(.folVar(n), results: [.i], before: id)[0]
        try b.replaceAllUses(of: old, with: new)
        try b.erase(id)
    }
}

private struct LowerAtom: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaAtom = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaAtom(n) = b.graph.op(id) else { return }
        let node = b.graph.node(id)
        let new = try b.insert(.folPred(n), operands: node.operands,
                               results: [.o], before: id)[0]
        try b.replaceAllUses(of: node.results[0], with: new)
        try b.erase(id)
    }
}

private struct EraseTrueprop: RewritePattern {
    func matches(_ op: Op) -> Bool { op == .isaTrueprop }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        let node = b.graph.node(id)
        try b.replaceAllUses(of: node.results[0], with: node.operands[0])
        try b.erase(id)
    }
}

private struct LowerImp: RewritePattern {
    func matches(_ op: Op) -> Bool { op == .isaImp }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        let node = b.graph.node(id)
        let new = try b.insert(.folImplies, operands: node.operands,
                               results: [.o], before: id)[0]
        try b.replaceAllUses(of: node.results[0], with: new)
        try b.erase(id)
    }
}

private let lowerMeta = PatternPass(
    name: "lower-meta",
    ensures: folZfcOnly,
    patterns: [EraseTrueprop(), LowerImp(), LowerAtom(), LowerFree()])

/// `mem(x, y) ==> mem(x, y)`, stated with Pure's arrow over IFOL atoms.
private func mixedGraph() throws -> Graph {
    var b = Builder()
    let r = b.graph.root
    let x = try b.append(.isaFree("x"), results: [.i], to: r)[0]
    let y = try b.append(.isaFree("y"), results: [.i], to: r)[0]
    let a = try b.append(.isaAtom("mem"), operands: [x, y], results: [.o], to: r)[0]
    let p = try b.append(.isaTrueprop, operands: [a], results: [.prop], to: r)[0]
    try b.append(.isaImp, operands: [p, p], results: [.prop], to: r)
    return b.graph
}

@Test func aMixedGraphIsIllegalUntilLowered() throws {
    let g = try mixedGraph()
    #expect(throws: IRRefusal.self) { try legalize(g) }
}

@Test func loweringMakesItFolZfcOnly() throws {
    let out = try PassManager([lowerMeta]).run(try mixedGraph())
    try legalize(out)
    for id in out.liveOps {
        #expect(out.op(id).dialect == .fol, "\(out.op(id)) survived")
    }
    for v in out.liveValues {
        #expect(!v.isMetaOrFn(in: out), "\(out.type(of: v)) survived")
    }
}

@Test func aPassThatLeavesItsEliminatedShapeBehindIsRejected() throws {
    let partial = PatternPass(name: "partial", ensures: folZfcOnly,
                              patterns: [LowerAtom(), LowerFree()])
    #expect(throws: IRRefusal.self) {
        _ = try PassManager([partial]).run(try mixedGraph())
    }
}

extension ValueID {
    fileprivate func isMetaOrFn(in g: Graph) -> Bool {
        let s = g.type(of: self).shapes
        return s.contains(.prop) || s.contains(.fn)
    }
}
