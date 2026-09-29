import Testing
import IR
import Lowering

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }

private struct F {
    var t = Table()
    mutating func b(_ k: Int) throws -> NodeID { try t.intern(.isaBound(k, i)) }
    mutating func v(_ k: Int) throws -> NodeID { try t.intern(.folBound(k)) }
    mutating func const(_ n: String, _ T: IRType, _ xs: NodeID...) throws -> NodeID { try t.intern(.isaConst(n, T, args: xs)) }
    mutating func pred(_ n: String, _ x: NodeID) throws -> NodeID { try const(n, fn(i, o), x) }
    mutating func set(_ x: NodeID) throws -> NodeID { try t.intern(.folPred("set", args: [x])) }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try t.intern(.folImplies(a, b)) }
    mutating func all(_ body: NodeID) throws -> NodeID { try t.intern(.ifolAll(i, body: body)) }
    mutating func guardedAll(_ body: NodeID) throws -> NodeID { try all(try imp(try set(try v(0)), body)) }
    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try t.intern(.hyp(k, a)) }
    mutating func use(_ n: String, _ root: NodeID) throws -> NodeID { try t.intern(.use(n, [], root)) }
    mutating func fix(_ body: NodeID) throws -> NodeID { try t.intern(.isaAllIntro(i, body: body)) }
    mutating func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID { try t.intern(.folImpliesIntro(a, body: body)) }
    mutating func mp(_ p: NodeID, _ q: NodeID) throws -> NodeID { try t.intern(.folImpliesElim(p, q)) }
    mutating func elim(_ p: NodeID, _ x: NodeID) throws -> NodeID { try t.intern(.isaAllElim(p, x)) }

    /// `lem : ⋀y. P(y) ⟹ Q(y)`, stated by an axiom it cites.
    mutating func lem() throws -> Statement {
        let root = try all(try imp(try pred("P", try b(0)), try pred("Q", try b(0))))
        return Statement(name: "lem", root: root, proof: try use("lem_ax", root))
    }
}

private func lowered(_ f: F, _ statements: [Statement]) throws -> Unit {
    var unit = Unit(table: f.t, statements: statements)
    try Pipeline(passes: [Guard()]).run(&unit)
    return unit
}

private func statement(_ unit: Unit, _ name: String) throws -> Statement {
    try #require(unit.statements.first { $0.name == name })
}

/// A variable of type `i` becomes a fol variable wherever it is bound, a `λ` included; only a
/// quantifier at `i` gains a guard.
@Test func aQuantifierAtIIsGuardedAndEveryVariableAtIIsAFolVariable() throws {
    var f = F()
    let px = try f.pred("P", try f.b(0))
    let a = try f.const("a", i)
    let allAtI = try f.all(px)
    let exAtI = try f.t.intern(.ifolEx(i, body: px))
    let atO = try f.t.intern(.ifolAll(o, body: try f.t.intern(.isaBound(0, o))))
    let atPredicate = try f.t.intern(.ifolAll(fn(i, o), body: try f.t.intern(
        .isaVarApp(head: try f.t.intern(.isaBound(0, fn(i, o))), args: [a]))))
    let atVariable = try f.t.intern(.ifolAll(.variable("'a"), body: try f.t.intern(.folBottom)))
    let lambda = try f.const("F", fn(fn(i, o), o), try f.t.intern(.isaAbs(i, body: px)))
    let roots = [allAtI, exAtI, atO, atPredicate, atVariable, lambda]
    let out = try Guard().run(roots, in: &f.t).map { r -> NodeID? in
        if case let .rewritten(id) = r { return id }
        return nil
    }
    let pv = try f.pred("P", try f.v(0))
    let guardedEx = try f.t.intern(.ifolEx(i, body: try f.t.intern(.folAnd(try f.set(try f.v(0)), pv))))
    let lambdaOverV = try f.const("F", fn(fn(i, o), o), try f.t.intern(.isaAbs(i, body: pv)))
    #expect(out == [try f.guardedAll(pv), guardedEx, atO, atPredicate, atVariable, lambdaOverV])
}

/// `λx h. lem x h`: the elimination at `x` owes `set(x)`, and `x`'s guard is one assumption
/// back — `P(x)` lies between.
@Test func anEliminationAtAVariableIsDischargedByItsGuard() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(0), px = try f.pred("P", x)
    let proof = try f.fix(try f.assume(px, try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px))))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: lem.root, proof: proof)])
    var g = F(t: unit.table)
    let v = try g.v(0), pv = try g.pred("P", v)
    let lemRoot = try g.guardedAll(try g.imp(pv, try g.pred("Q", v)))
    let discharged = try g.mp(try g.elim(try g.use("lem", lemRoot), v), try g.hyp(1, try g.set(v)))
    let expected = try g.fix(try g.assume(try g.set(v), try g.assume(pv, try g.mp(discharged, try g.hyp(0, pv)))))
    #expect(try statement(unit, "thm").proof == expected)
    #expect(try statement(unit, "thm").root == lemRoot)
}

/// `⋀x y. P(x) ⟹ Q(x)`: between the elimination at `x` and `x`'s guard lie `y`'s guard and `P(x)`.
@Test func anEliminationSkipsTheGuardsOfInnerVariables() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(1), px = try f.pred("P", x), qx = try f.pred("Q", x)
    let root = try f.all(try f.all(try f.imp(px, qx)))
    let proof = try f.fix(try f.fix(try f.assume(px, try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px)))))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: root, proof: proof)])
    var g = F(t: unit.table)
    let v1 = try g.v(1), pv1 = try g.pred("P", v1)
    let lemRoot = try g.guardedAll(try g.imp(try g.pred("P", try g.v(0)), try g.pred("Q", try g.v(0))))
    let discharged = try g.mp(try g.elim(try g.use("lem", lemRoot), v1), try g.hyp(2, try g.set(v1)))
    let body = try g.assume(pv1, try g.mp(discharged, try g.hyp(0, pv1)))
    let expected = try g.fix(try g.assume(try g.set(try g.v(0)), try g.fix(try g.assume(try g.set(try g.v(0)), body))))
    #expect(try statement(unit, "thm").proof == expected)
}

/// `C ⟹ ⋀x. P(x) ⟹ C`: `x`'s guard is inserted between `hyp(1, C)` and `C`'s binder.
@Test func aHypothesisAcrossAGuardIsRenumbered() throws {
    var f = F()
    let c = try f.const("C", o)
    let x = try f.b(0), px = try f.pred("P", x)
    let root = try f.imp(c, try f.all(try f.imp(px, c)))
    let proof = try f.assume(c, try f.fix(try f.assume(px, try f.hyp(1, c))))
    let unit = try lowered(f, [Statement(name: "thm", root: root, proof: proof)])
    var g = F(t: unit.table)
    let pv = try g.pred("P", try g.v(0))
    let expected = try g.assume(c, try g.fix(try g.assume(try g.set(try g.v(0)), try g.assume(pv, try g.hyp(2, c)))))
    #expect(try statement(unit, "thm").proof == expected)
}

/// `C ⟹ ⋀P::o. P ⟹ C`: a fix at `o` brings no guard, so nothing is inserted and nothing renumbered.
@Test func aBinderAtAnotherTypeInsertsNoGuard() throws {
    var f = F()
    let c = try f.const("C", o)
    let p = try f.t.intern(.isaBound(0, o))
    let root = try f.imp(c, try f.t.intern(.ifolAll(o, body: try f.imp(p, c))))
    let proof = try f.assume(c, try f.t.intern(.isaAllIntro(o, body: try f.assume(p, try f.hyp(1, c)))))
    let unit = try lowered(f, [Statement(name: "thm", root: root, proof: proof)])
    #expect(try statement(unit, "thm").root == root)
    #expect(try statement(unit, "thm").proof == proof)
}

@Test func anEliminationAtACompoundTermIsRefusedByName() throws {
    var f = F()
    let lem = try f.lem()
    let pow = try f.const("ZF_Base.Pow", fn(i, i), try f.const("a", i))
    let root = try f.imp(try f.pred("P", pow), try f.pred("Q", pow))
    let proof = try f.elim(try f.use("lem", lem.root), pow)
    let unit = try lowered(f, [lem, Statement(name: "thm", root: root, proof: proof)])
    #expect(unit.statements.map(\.name) == ["lem"])
    #expect(unit.refused.map { [$0.name, $0.pass] } == [["thm", "guard"]])
    #expect(unit.refused.first?.refusal as? GuardRefusal == .compoundInstantiation(pow))
}

/// The walk rewrites a citation's statement and the cited theorem's own statement alike: one node.
@Test func aCitedStatementIsTheCitedTheoremsLoweredStatement() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(0), px = try f.pred("P", x)
    let proof = try f.fix(try f.assume(px, try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px))))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: lem.root, proof: proof)])
    var seen: Set<NodeID> = [], work = [try statement(unit, "thm").proof], cited: [NodeID] = []
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case let .use("lem", _, root) = unit.table[n] { cited.append(root) }
        unit.table[n].forEachChild { c, _ in work.append(c) }
    }
    #expect(cited == [try statement(unit, "lem").root])
}
