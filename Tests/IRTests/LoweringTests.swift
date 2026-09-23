import Testing
@testable import IR

private struct LowerFree: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaFree(n, _) = b.graph.op(id) else { return }
        let new = try b.insert(.folVar(n), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

private struct LowerAtom: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaAtom = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaAtom(n, xs) = b.graph.op(id) else { return }
        let new = try b.insert(.folPred(n, xs), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

private struct EraseTrueprop: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaTrueprop = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaTrueprop(a) = b.graph.op(id) else { return }
        b.replaceAllUses(of: id, with: a)
        b.erase(id)
    }
}

private struct LowerImp: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaImp = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaImp(a, c) = b.graph.op(id) else { return }
        let new = try b.insert(.folImplies(a, c), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

private let lowerMeta = PatternPass(
    name: "lower-meta", ensures: folZfcOnly,
    patterns: [EraseTrueprop(), LowerImp(), LowerAtom(), LowerFree()])

/// `mem(x, y) ⟹ mem(x, y)` — Pure's arrow over an IFOL atom.
private func mixedGraph() throws -> Graph {
    var b = Builder()
    let r = b.graph.root
    let x = try b.append(.isaFree("x", .i), to: r)
    let y = try b.append(.isaFree("y", .i), to: r)
    let a = try b.append(.isaAtom("mem", [x, y]), to: r)
    let p = try b.append(.isaTrueprop(a), to: r)
    try b.append(.isaImp(p, p), to: r)
    return b.graph
}

@Test func aMixedGraphIsIllegalUntilLowered() throws {
    #expect(throws: IRRefusal.self) { try legalize(try mixedGraph()) }
}

@Test func loweringMakesItFolZfcOnly() throws {
    let out = try PassManager([lowerMeta]).run(try mixedGraph())
    try legalize(out)
    for id in out.liveOps {
        #expect(out.type(of: id) == .i || out.type(of: id) == .o)
    }
}

@Test func loweringPreservesTheOperandWiring() throws {
    let out = try PassManager([lowerMeta]).run(try mixedGraph())
    let imp = out.liveOps.first { if case .folImplies = out.op($0) { return true }; return false }
    guard case let .folImplies(a, c) = out.op(imp!) else { return }
    #expect(a == c, "both antecedent and consequent are the same atom")
    guard case let .folPred(n, xs) = out.op(a) else { return }
    #expect(n == "mem")
    #expect(xs.allSatisfy { if case .folVar = out.op($0) { return true }; return false },
            "the atom's arguments were rewired to the lowered variables")
}

@Test func aPassThatLeavesItsEliminatedShapeBehindIsRejected() throws {
    let partial = PatternPass(name: "partial", ensures: folZfcOnly,
                              patterns: [LowerAtom(), LowerFree()])
    #expect(throws: IRRefusal.self) {
        _ = try PassManager([partial]).run(try mixedGraph())
    }
}
