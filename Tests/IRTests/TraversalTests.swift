import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }
private let mem = Constant.primitive(.zf(.mem))
private let memT = fn(i, fn(i, o))

private struct NoMatch: Rule {}

private final class DepthLog: Rule {
    var seen: [(Node, Int)] = []
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        seen.append((t[id], depth.terms))
        return nil
    }
}

private final class BinderLog: Rule {
    var seen: [(NodeID, [Node])] = []
    var start: [Node] { [] }
    func enter(_ c: [Node], _ binder: Node, _ binds: Binds, in t: Table) -> [Node] { c + [binder] }
    func before(_ id: NodeID, context: [Node], in t: inout Table) throws -> NodeID? {
        seen.append((id, context))
        return nil
    }
}

private final class NarrowedLog: Rule {
    var seen: [(NodeID, [Node])] = []
    var start: [Node] { [] }
    func enter(_ c: [Node], _ binder: Node, _ binds: Binds, in t: Table) -> [Node] { c + [binder] }
    func narrow(_ c: [Node], _ id: NodeID, in t: Table) -> [Node] {
        var terms = t.looseBound(of: id), hyps = t.looseHyps(of: id), k = c.count
        while terms > 0 || hyps > 0 {
            k -= 1
            c[k].forEachChild { _, binds in terms -= binds.terms; hyps -= binds.hyps }
        }
        return Array(c[k...])
    }
    func before(_ id: NodeID, context: [Node], in t: inout Table) throws -> NodeID? {
        seen.append((id, context))
        return nil
    }
}

private final class VisitCount: Rule {
    var visits: [NodeID: Int] = [:]
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        visits[id, default: 0] += 1
        return nil
    }
}

private struct Broken: Error {}

private struct BreakAtBottom: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if case .folBottom = t[id] { throw Broken() }
        return nil
    }
}

private struct Rename: Rule {
    let from: String, to: String
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .isaFree(.named(n), T) = t[id], n == from else { return nil }
        return try t.intern(.isaFree(.named(to), T))
    }
}

private struct DropDoubleNegation: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .folNot(a) = t[id], case let .folNot(b) = t[a] else { return nil }
        return b
    }
}

private func memOf(_ a: NodeID, _ b: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.isaConst(mem, memT, args: [a, b]))
}

@Test func aRuleThatMatchesNothingReturnsTheSameRoot() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let x = try t.intern(.isaBound(0, i))
    let root = try t.intern(.ifolAll(i, body: try memOf(x, a, &t)))
    #expect(try transform(root, NoMatch(), in: &t) == root)
}

@Test func aRuleSeesTheBinderDepthOfEachNode() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let x = try t.intern(.isaBound(0, i))
    let inner = try t.intern(.isaAbs(i, body: x))
    let collect = try t.intern(.isaConst(.defined(Defined(.zf, "ZF_Base.RepFun", .object)), fn(i, fn(fn(i, i), i)), args: [x, inner]))
    let root = try t.intern(.ifolAll(i, body: try memOf(collect, a, &t)))
    let log = DepthLog()
    _ = try transform(root, log, in: &t)
    let depthOfBound = log.seen.filter { $0.0 == .isaBound(0, i) }.map(\.1)
    #expect(depthOfBound == [1, 2], "RepFun's first argument is under ∀ only; the λ body under ∀ and λ")
    #expect(log.seen.first.map(\.1) == 0)
}

/// `folImpliesIntro(A, isaAllIntro(i, folImpliesIntro(B, hyp(1, A))))`: `A` is shared, outside
/// its own hypothesis and under all three binders.
private struct Nested {
    var t = Table()
    let A: NodeID, B: NodeID, hyp: NodeID, assumeB: NodeID, fix: NodeID, assumeA: NodeID

    init() throws {
        let a = try t.intern(.isaFree(.named("a"), i))
        A = try memOf(a, a, &t)
        B = try t.intern(.folBottom)
        hyp = try t.intern(.hyp(1, A))
        assumeB = try t.intern(.folImpliesIntro(B, body: hyp))
        fix = try t.intern(.isaAllIntro(i, body: assumeB))
        assumeA = try t.intern(.folImpliesIntro(A, body: fix))
    }
}

private func contexts(_ seen: [(NodeID, [Node])], _ id: NodeID) -> [[Node]] {
    seen.filter { $0.0 == id }.map(\.1)
}

/// A node's context is what `enter` made of it at every binder above, outermost first. `A` in
/// `folImpliesIntro(A, body)` is not under its own hypothesis, so it sees its parent's.
@Test func aRuleSeesTheContextItsBindersMade() throws {
    var n = try Nested()
    let log = BinderLog()
    _ = try transform(n.assumeA, log, in: &n.t)
    let (t, seen) = (n.t, log.seen)
    #expect(contexts(seen, n.B) == [[t[n.assumeA], t[n.fix]]])
    #expect(contexts(seen, n.hyp) == [[t[n.assumeA], t[n.fix], t[n.assumeB]]])
    #expect(contexts(seen, n.A) == [[], [t[n.assumeA], t[n.fix], t[n.assumeB]]])
}

/// Narrowed to the binders it reaches, a closed node's context is empty wherever it is shared, so
/// `A` is one cache key and rewritten once.
@Test func aNodeSeesOnlyTheContextItsRuleNarrowedTo() throws {
    var n = try Nested()
    let log = NarrowedLog()
    _ = try transform(n.assumeA, log, in: &n.t)
    let (t, seen) = (n.t, log.seen)
    #expect(contexts(seen, n.B) == [[]])
    #expect(contexts(seen, n.hyp) == [[t[n.assumeA], t[n.fix], t[n.assumeB]]])
    #expect(contexts(seen, n.A) == [[]])
}

@Test func aSharedNodeIsRewrittenOncePerContext() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    var p = bottom
    for _ in 0..<20 { p = try t.intern(.folAnd(p, p)) }
    let count = VisitCount()
    _ = try transform(p, count, in: &t)
    #expect(count.visits.values.reduce(0, +) == 21, "not 2^21 - 1")
    #expect(count.visits[bottom] == 1)
}

@Test func oneWalkOverSeveralRootsRewritesASharedNodeOnce() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let shared = try memOf(a, a, &t)
    let r1 = try t.intern(.folNot(shared))
    let r2 = try t.intern(.folAnd(shared, shared))
    let count = VisitCount()
    #expect(try transform([r1, r2], count, in: &t) == [r1, r2])
    #expect(count.visits[shared] == 1)
}

@Test func rebuildingGoesThroughTheTable() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let b = try t.intern(.isaFree(.named("b"), i))
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

@Test func anErrorStopsTheWalk() throws {
    var t = Table()
    let root = try t.intern(.folNot(try t.intern(.folBottom)))
    let other = try t.intern(.isaFree(.named("a"), i))
    #expect(throws: Broken.self) { try transform([root, other], BreakAtBottom(), in: &t) }
}

/// `OFCLASS(T, c)`, "T is in class c": a formula of the isa dialect, the export's own term form.
@Test func aClassMembershipIsAnIsaFormula() throws {
    var t = Table()
    let member = try t.intern(.isaOfClass(.variable("'a"), "IFOL.term"))
    #expect(t.type(of: member) == .o)
    #expect(throws: IRRefusal.sourceKindSurvived(member)) { try legalize(member, in: t) }
}

@Test func legalizeAcceptsATargetOnlyRoot() throws {
    var t = Table()
    let b0 = try t.intern(.folBound(0))
    let root = try t.intern(.folForall(body: try t.intern(.folPred("set", args: [b0]))))
    try legalize(root, in: t)
}

@Test func legalizeRefusesAReachableSourceKindByName() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let atom = try memOf(a, a, &t)
    let root = try t.intern(.folNot(try t.intern(.folAnd(try t.intern(.folBottom), atom))))
    #expect(throws: IRRefusal.sourceKindSurvived(atom)) {
        try legalize(root, in: t)
    }
}

/// `use` is a kind of both dialects, yet fol-zfc cites no Isabelle axiom: legalize reads the pattern.
@Test func legalizeRefusesACitationOfAnIsabelleAxiom() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let cited = try t.intern(.use(.axiom(.pure(.reflexive)), [.o], try t.intern(.folIff(bottom, bottom))))
    let root = try t.intern(.folImpliesIntro(bottom, body: cited))
    #expect(throws: IRRefusal.sourceKindSurvived(cited)) { try legalize(root, in: t) }
}
