import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }
private let mem = "ZF_Base.mem"
private let memT = fn(i, fn(i, o))

private struct NoMatch: Rule {}

private final class DepthLog: Rule {
    var seen: [(Node, Int)] = []
    func before(_ id: NodeID, depth: Depth, in t: inout Table) throws -> NodeID? {
        seen.append((t[id], depth.terms))
        return nil
    }
}

private struct Rename: Rule {
    let from: String, to: String
    func before(_ id: NodeID, depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .isaFree(n, T) = t[id], n == from else { return nil }
        return try t.intern(.isaFree(to, T))
    }
}

private struct DropDoubleNegation: Rule {
    func before(_ id: NodeID, depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .folNot(a) = t[id], case let .folNot(b) = t[a] else { return nil }
        return b
    }
}

private func memOf(_ a: NodeID, _ b: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.isaConst(mem, memT, args: [a, b]))
}

@Test func aRuleThatMatchesNothingReturnsTheSameRoot() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let x = try t.intern(.isaBound(0, i))
    let root = try t.intern(.ifolAll(i, body: try memOf(x, a, &t)))
    #expect(try transform(root, NoMatch(), in: &t) == root)
}

@Test func aRuleSeesTheBinderDepthOfEachNode() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let x = try t.intern(.isaBound(0, i))
    let inner = try t.intern(.isaAbs(i, body: x))
    let collect = try t.intern(.isaConst("ZF_Base.RepFun", fn(i, fn(fn(i, i), i)), args: [x, inner]))
    let root = try t.intern(.ifolAll(i, body: try memOf(collect, a, &t)))
    let log = DepthLog()
    _ = try transform(root, log, in: &t)
    let depthOfBound = log.seen.filter { $0.0 == .isaBound(0, i) }.map(\.1)
    #expect(depthOfBound == [1, 2], "RepFun's first argument is under ∀ only; the λ body under ∀ and λ")
    #expect(log.seen.first.map(\.1) == 0)
}

@Test func rebuildingGoesThroughTheTable() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    let before = try memOf(a, a, &t)
    let expected = try memOf(b, b, &t)
    #expect(try transform(before, Rename(from: "a", to: "b"), in: &t) == expected)
}

@Test func aMatchReplacesTheSubtreeWithoutDescending() throws {
    var t = Table()
    let p = try t.intern(.folBottom)
    let n1 = try t.intern(.folNot(p))
    let n2 = try t.intern(.folNot(n1))
    let n3 = try t.intern(.folNot(n2))
    let n4 = try t.intern(.folNot(n3))
    #expect(try transform(n4, DropDoubleNegation(), in: &t) == n2)
}

@Test func aRulePassRunsToTheFixpoint() throws {
    var t = Table()
    let p = try t.intern(.folBottom)
    var root = p
    for _ in 0..<6 { root = try t.intern(.folNot(root)) }
    let pass = RulePass(name: "drop-double-negation", rule: DropDoubleNegation())
    #expect(try pass.run(root, in: &t) == p)
}

@Test func aPipelineRunsItsPassesInOrderOverEveryStatement() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let s1 = try memOf(a, a, &t)
    let s2 = try t.intern(.folNot(try memOf(a, a, &t)))
    var unit = Unit(table: t, statements: [Statement(serial: 1, name: "s1", root: s1),
                                           Statement(serial: 2, name: nil, root: s2)])
    let pipeline = Pipeline(passes: [RulePass(name: "a-to-b", rule: Rename(from: "a", to: "b")),
                                     RulePass(name: "b-to-c", rule: Rename(from: "b", to: "c"))])
    try pipeline.run(&unit)
    let c = try unit.table.intern(.isaFree("c", i))
    #expect(unit.statements[0].root == (try memOf(c, c, &unit.table)))
    #expect(unit.statements[1].root == (try unit.table.intern(.folNot(try memOf(c, c, &unit.table)))))
}

@Test func legalizeAcceptsATargetOnlyRoot() throws {
    var t = Table()
    let b0 = try t.intern(.folBound(0))
    let root = try t.intern(.folForall(body: try t.intern(.folPred("set", args: [b0]))))
    try legalize(root, in: t)
}

@Test func legalizeRefusesAReachableSourceKindByName() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let atom = try memOf(a, a, &t)
    let root = try t.intern(.folNot(try t.intern(.folAnd(try t.intern(.folBottom), atom))))
    #expect(throws: IRRefusal.sourceKindSurvived(atom)) {
        try legalize(root, in: t)
    }
}
