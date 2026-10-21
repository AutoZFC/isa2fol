import FolDialect
import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private struct F {
    var t = Table()

    mutating func b(_ k: Int) throws -> NodeID {
        try t.intern(.isaBound(k, i))
    }

    mutating func v(_ k: Int) throws -> NodeID {
        try t.intern(.folBound(k))
    }

    mutating func const(_ c: Constant, _ T: IRType, _ xs: NodeID...) throws -> NodeID {
        try t.intern(.isaConst(
            c,
            T,
            args: xs,
        ))
    }

    mutating func pred(_ n: String, _ x: NodeID) throws -> NodeID {
        try const(.declared(n), fn(i, o), x)
    }

    mutating func set(_ x: NodeID) throws -> NodeID {
        try t.intern(.folPred(.base("set"), args: [x]))
    }

    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try t.intern(.folImplies(a, b))
    }

    mutating func all(_ body: NodeID) throws -> NodeID {
        try t.intern(.ifolAll(i, body: body))
    }

    mutating func guardedAll(_ body: NodeID) throws -> NodeID {
        try t.intern(.folForall(body: try imp(
            try set(try v(0)),
            body,
        )))
    }

    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID {
        try t.intern(.hyp(k, a))
    }

    mutating func use(_ n: String, _ root: NodeID) throws -> NodeID {
        try t.intern(.use(.theorem(n), [], root))
    }

    mutating func fix(_ body: NodeID) throws -> NodeID {
        try t.intern(.isaAllIntro(i, body: body))
    }

    mutating func guardedFix(_ body: NodeID) throws -> NodeID {
        try t.intern(.folForallIntro(body: try assume(try set(try v(0)), body)))
    }

    mutating func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID {
        try t.intern(.folImpliesIntro(a, body: body))
    }

    mutating func mp(_ p: NodeID, _ q: NodeID) throws -> NodeID {
        try t.intern(.folImpliesElim(p, q))
    }

    mutating func elim(_ p: NodeID, _ x: NodeID) throws -> NodeID {
        try t.intern(.isaAllElim(p, x))
    }

    mutating func guardedElim(_ p: NodeID, _ x: NodeID, guard k: Int) throws -> NodeID {
        try mp(try t.intern(.folForallElim(p, x)), try hyp(k, try set(x)))
    }

    /// `lem : ⋀y. P(y) ⟹ Q(y)`, stated by an axiom it cites.
    mutating func lem() throws -> Statement {
        let root = try all(try imp(try pred("P", try b(0)), try pred("Q", try b(0))))
        return Statement(name: "lem", root: root, proof: try use("lem_ax", root))
    }
}

/// Fol alone, each proof checked to conclude its statement BY ID, as the pipeline checks it.
private func lowered(_ f: F, _ statements: [Statement]) throws -> Unit {
    var t = f.t
    let fol = Fol(base: try base(in: &t))
    let out = try run(fol, statements.flatMap { [$0.root, $0.proof!] }, in: &t)
    let lowered = statements.indices.map { k in Statement(
        name: statements[k].name,
        root: out[2 * k],
        proof: out[2 * k + 1],
    ) }
    for s in lowered { #expect(t.conclusion(of: s.proof!) == s.root, "\(s.name)") }
    return Unit(table: t, statements: lowered)
}

private func statement(_ unit: Unit, _ name: String) throws -> Statement {
    try #require(unit.statements.first { $0.name == name })
}

/// A quantifier at an object type is written as fol-zfc's binder over fol-zfc's variable, with the guard Reify gives
/// the
/// type: `set` at `i`, `function` at `i ⇒ i`, none at `i ⇒ o`. At `o` and at a type variable it is unchanged.
@Test
func aQuantifierAtAnObjectTypeTakesItsTypesGuard() throws {
    var f = F()
    let px = try f.pred("P", try f.b(0))
    let allAtI = try f.all(px)
    let exAtI = try f.t.intern(.ifolEx(i, body: px))
    let atO = try f.t.intern(.ifolAll(o, body: try f.t.intern(.isaBound(0, o))))
    let q = { (x: NodeID, f: inout F) in try f.t.intern(.folPred(.base("Q"), args: [x])) }
    let atPredicate = try f.t.intern(.ifolAll(fn(i, o), body: try q(try f.t.intern(.isaBound(0, fn(i, o))), &f)))
    let atFunction = try f.t.intern(.ifolAll(fn(i, i), body: try q(try f.t.intern(.isaBound(0, fn(i, i))), &f)))
    let atVariable = try f.t.intern(.ifolAll(.variable("'a"), body: try f.t.intern(.folBottom)))
    let fol = Fol(base: try base(in: &f.t))
    let out = try run(fol, [allAtI, exAtI, atO, atPredicate, atFunction, atVariable], in: &f.t)
    let v = try f.v(0)
    let pv = try f.pred("P", v)
    let guardedEx = try f.t.intern(.folExists(body: try f.t.intern(.folAnd(try f.set(v), pv))))
    let function = try f.t.intern(.folPred(.base("function"), args: [v]))
    #expect(out == [
        try f.guardedAll(pv),
        guardedEx,
        atO,
        try f.t.intern(.folForall(body: try q(v, &f))),
        try f.t.intern(.folForall(body: try f.imp(function, try q(v, &f)))),
        atVariable,
    ])
}

/// `(∃y. P(y)) ⟹ ∃y. Q(y)` by `lem` at the witness: `∃`-elim at `i` opens `set(y) ∧ P(y)` to the guard and `P(y)` by
/// two cuts of its projections, so the instance at `y` is discharged by `y`'s guard; `∃`-intro at `i` is base's
/// `ex_intro` at its body under the guard, then at the witness and the premise under its guard.
@Test
func anExistentialAtIIsGuardedWhereItIsOpenedAndClosed() throws {
    var f = F()
    let lem = try f.lem()
    let y = try f.b(0)
    let py = try f.pred("P", y)
    let qy = try f.pred("Q", y)
    let someP = try f.t.intern(.ifolEx(i, body: py))
    let someQ = try f.t.intern(.ifolEx(i, body: qy))
    let atY = try f.mp(try f.elim(try f.use("lem", lem.root), y), try f.hyp(0, py))
    let proof = try f.assume(
        someP,
        try f.t.intern(.isaExElim(i, try f.hyp(0, someP), body: try f.t.intern(.isaExIntro(atY, y, body: qy)))),
    )
    let unit = try lowered(f, [lem, Statement(name: "thm", root: try f.imp(someP, someQ), proof: proof)])
    var g = F(t: unit.table)
    let v = try g.v(0)
    let pv = try g.pred("P", v)
    let qv = try g.pred("Q", v)
    let sv = try g.set(v)
    let both = try g.t.intern(.folAnd(sv, pv))
    let guardedP = try g.t.intern(.folExists(body: both))
    let lemRoot = try g.guardedAll(try g.imp(pv, qv))
    let discharged = try g.mp(try g.guardedElim(try g.use("lem", lemRoot), v, guard: 1), try g.hyp(0, pv))
    let exIntro = try base(in: &g.t).cite(.exIntro, in: &g.t)
    let letter = try g.t.intern(.folLetterAbs(body: try g.t.intern(.folAnd(sv, qv))))
    let atV = try g.t.intern(.folForallElim(try g.t.intern(.folSchemaInst(exIntro, letter)), v))
    let intro = try g.mp(atV, try g.t.intern(.folAndIntro(try g.hyp(1, sv), discharged)))
    let body = try g.t.intern(.folCut(
        try g.t.intern(.folAndElimL(try g.hyp(0, both))),
        body: try g.t.intern(.folCut(try g.t.intern(.folAndElimR(try g.hyp(1, both))), body: intro)),
    ))
    #expect(try statement(unit, "thm").proof == (try g.assume(
        guardedP,
        try g.t.intern(.folExistsElim(try g.hyp(0, guardedP), body: body)),
    )))
}

/// `(∃b::i ⇒ i. R(b)) ⟹ ⊥` by `c`: `∃`-elim at a function type opens `function(b) ∧ R(b)`, its guard and its body, by
/// two cuts of its projections, as at `i`.
@Test
func anExistentialAtAFunctionTypeIsOpenedByItsGuard() throws {
    var f = F()
    let fun = fn(i, i)
    let rb = try f.t.intern(.folPred(.base("R"), args: [try f.t.intern(.isaBound(0, fun))]))
    let someR = try f.t.intern(.ifolEx(fun, body: rb))
    let bottom = try f.t.intern(.folBottom)
    let c = Statement(name: "c", root: bottom, proof: try f.use("c_ax", bottom))
    let proof = try f.assume(
        someR,
        try f.t.intern(.isaExElim(fun, try f.hyp(0, someR), body: try f.use("c", bottom))),
    )
    let unit = try lowered(f, [c, Statement(name: "thm", root: try f.imp(someR, bottom), proof: proof)])
    var g = F(t: unit.table)
    let v = try g.v(0)
    let rv = try g.t.intern(.folPred(.base("R"), args: [v]))
    let both = try g.t.intern(.folAnd(try g.t.intern(.folPred(.base("function"), args: [v])), rv))
    let guarded = try g.t.intern(.folExists(body: both))
    let body = try g.t.intern(.folCut(
        try g.t.intern(.folAndElimL(try g.hyp(0, both))),
        body: try g.t.intern(.folCut(try g.t.intern(.folAndElimR(try g.hyp(1, both))), body: try g.use("c", bottom))),
    ))
    #expect(try statement(unit, "thm").proof == (try g.assume(
        guarded,
        try g.t.intern(.folExistsElim(try g.hyp(0, guarded), body: body)),
    )))
}

/// `λx h. lem x h`: the elimination at `x` owes `set(x)`, and `x`'s guard is one assumption
/// back — `P(x)` lies between.
@Test
func anEliminationAtAVariableIsDischargedByItsGuard() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(0)
    let px = try f.pred("P", x)
    let proof = try f.fix(try f.assume(px, try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px))))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: lem.root, proof: proof)])
    var g = F(t: unit.table)
    let v = try g.v(0)
    let pv = try g.pred("P", v)
    let lemRoot = try g.guardedAll(try g.imp(pv, try g.pred("Q", v)))
    let discharged = try g.guardedElim(try g.use("lem", lemRoot), v, guard: 1)
    let expected = try g.guardedFix(try g.assume(pv, try g.mp(discharged, try g.hyp(0, pv))))
    #expect(try statement(unit, "thm").proof == expected)
    #expect(try statement(unit, "thm").root == lemRoot)
}

/// `⋀x y. P(x) ⟹ Q(x)`: between the elimination at `x` and `x`'s guard lie `y`'s guard and `P(x)`.
@Test
func anEliminationSkipsTheGuardsOfInnerVariables() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(1)
    let px = try f.pred("P", x)
    let qx = try f.pred("Q", x)
    let root = try f.all(try f.all(try f.imp(px, qx)))
    let proof = try f.fix(try f.fix(try f.assume(
        px,
        try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px)),
    )))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: root, proof: proof)])
    var g = F(t: unit.table)
    let v1 = try g.v(1)
    let pv1 = try g.pred("P", v1)
    let lemRoot = try g.guardedAll(try g.imp(try g.pred("P", try g.v(0)), try g.pred("Q", try g.v(0))))
    let discharged = try g.guardedElim(try g.use("lem", lemRoot), v1, guard: 2)
    let body = try g.assume(pv1, try g.mp(discharged, try g.hyp(0, pv1)))
    let expected = try g.guardedFix(try g.guardedFix(body))
    #expect(try statement(unit, "thm").proof == expected)
}

/// `C ⟹ ⋀x. P(x) ⟹ C`: `x`'s guard is inserted between `hyp(1, C)` and `C`'s binder.
@Test
func aHypothesisAcrossAGuardIsRenumbered() throws {
    var f = F()
    let c = try f.const(.declared("C"), o)
    let x = try f.b(0)
    let px = try f.pred("P", x)
    let root = try f.imp(c, try f.all(try f.imp(px, c)))
    let proof = try f.assume(c, try f.fix(try f.assume(px, try f.hyp(1, c))))
    let unit = try lowered(f, [Statement(name: "thm", root: root, proof: proof)])
    var g = F(t: unit.table)
    let pv = try g.pred("P", try g.v(0))
    let expected = try g.assume(c, try g.guardedFix(try g.assume(pv, try g.hyp(2, c))))
    #expect(try statement(unit, "thm").proof == expected)
}

/// `C ⟹ ⋀P::o. P ⟹ C`: a fix at `o` brings no guard, so nothing is inserted and nothing renumbered.
@Test
func aBinderAtAnotherTypeInsertsNoGuard() throws {
    var f = F()
    let c = try f.const(.declared("C"), o)
    let p = try f.t.intern(.isaBound(0, o))
    let root = try f.imp(c, try f.t.intern(.ifolAll(o, body: try f.imp(p, c))))
    let proof = try f.assume(c, try f.t.intern(.isaAllIntro(o, body: try f.assume(p, try f.hyp(1, c)))))
    let unit = try lowered(f, [Statement(name: "thm", root: root, proof: proof)])
    #expect(try statement(unit, "thm").root == root)
    #expect(try statement(unit, "thm").proof == proof)
}

/// The walk rewrites a citation's statement and the cited theorem's own statement alike: one node.
@Test
func aCitedStatementIsTheCitedTheoremsLoweredStatement() throws {
    var f = F()
    let lem = try f.lem()
    let x = try f.b(0)
    let px = try f.pred("P", x)
    let proof = try f.fix(try f.assume(px, try f.mp(try f.elim(try f.use("lem", lem.root), x), try f.hyp(0, px))))
    let unit = try lowered(f, [lem, Statement(name: "thm", root: lem.root, proof: proof)])
    var seen = Set<NodeID>()
    var work = [try #require(try statement(unit, "thm").proof)]
    var cited = [NodeID]()
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .use(.theorem("lem"), _, let root) = unit.table[n] { cited.append(root) }
        unit.table[n].forEachChild { c, _ in work.append(c) }
    }
    #expect(cited == [try statement(unit, "lem").root])
}

/// `⋀x. ⊥ ⟹ set(x)`, proved by the guard of `x`: Fol makes it the assumption it writes at `x`'s binder, as for an
/// instance at `x`.
@Test
func theGuardOfAVariableIsTheAssumptionFolWritesAtItsBinder() throws {
    var f = F()
    let bottom = try f.t.intern(.folBottom)
    let x = try f.b(0)
    let sx = try f.set(x)
    let root = try f.all(try f.imp(bottom, sx))
    let proof = try f.fix(try f.assume(bottom, try f.t.intern(.isaGuard(x, sx))))
    let unit = try lowered(f, [Statement(name: "thm", root: root, proof: proof)])
    var g = F(t: unit.table)
    let sv = try g.set(try g.v(0))
    let expected = try g.guardedFix(try g.assume(bottom, try g.hyp(1, sv)))
    #expect(try statement(unit, "thm").proof == expected)
}

/// A variable that fol-zfc's own `∀`-intro binds brings no guard; one at `i` brings `set`, and nothing else.
@Test
func aGuardOfAVariableItsBinderDoesNotBringIsMalformed() throws {
    var f = F()
    let x = try f.b(0)
    let sx = try f.set(x)
    let unguarded = try f.t.intern(.folForallIntro(body: try f.t.intern(.isaGuard(x, sx))))
    let v0 = try f.v(0)
    let fol = Fol(base: try base(in: &f.t))
    #expect(throws: FolError.unguardedBinder(v0)) { _ = try run(fol, [unguarded], in: &f.t) }
    let px = try f.pred("P", x)
    let other = try f.fix(try f.t.intern(.folImpliesIntro(px, body: try f.t.intern(.isaGuard(x, px)))))
    let wrong = try f.pred("P", v0)
    #expect(throws: FolError.notItsGuard(wrong)) { _ = try run(fol, [other], in: &f.t) }
}

/// Base's guarded quantifiers parse as set binders, and Fol writes each guard back: a parsed claim lowered is its text.
@Test
func aParsedBaseClaimLoweredByFolIsItsText() throws {
    var f = F()
    let (_, root) = try parse(
        claim: "claim apply_EX: forall F. (forall t. (set(t) -> (exists r. (set(r) & apply(t,r,F)))))",
        in: &f.t,
    )
    let fol = Fol(base: try base(in: &f.t))
    let lowered = try run(fol, [root], in: &f.t)[0]
    let apply = try f.t.intern(.folPred(.base("apply"), args: [try f.v(1), try f.v(0), try f.v(2)]))
    let witness = try f.t.intern(.folExists(body: try f.t.intern(.folAnd(try f.set(try f.v(0)), apply))))
    #expect(lowered == (try f.t.intern(.folForall(body: try f.guardedAll(witness)))))
}
