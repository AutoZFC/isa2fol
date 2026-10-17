import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private let F = IRType.fn(.i, .i)

private func lowered(_ l: LogicTable, _ statements: [Statement]) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements)
    try pipeline(b).run(&unit)
    return unit
}

/// `⋀x. ∃y. φ(y, x)` from `x = x` at `x`, as `body` says: `y = x` or `y = y` (DESIGN "An ∃-intro carrying its body").
private func someEqual(_ name: String, _ body: NodeID, _ l: inout LogicTable) throws -> Statement {
    let x = try l.bound(0, i)
    let intro = try l.t.intern(.isaExIntro(try l.t.intern(.isaReflexive(x)), x, body: body))
    return Statement(
        name: name,
        root: try l.all(i, try l.t.intern(.ifolEx(i, body: body))),
        proof: try l.t.intern(.isaAllIntro(i, body: intro)),
        theory: "Test",
    )
}

/// One premise, two bodies: the step concludes the body it is given, never the one its witness's occurrences make.
/// Base's `ex_intro` at each body, then at `x`; the kernel proves both.
@Test
func anExistentialIntroAtAVariableIsBasesExIntroAtItsBody() throws {
    var l = LogicTable()
    let toX = try someEqual("T.someEqual", try l.equal(i, try l.bound(0, i), try l.bound(1, i)), &l)
    let toItself = try someEqual("T.someItself", try l.equal(i, try l.bound(0, i), try l.bound(0, i)), &l)
    let unit = try lowered(l, [toX, toItself])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀f x. ∃y. y = f(x)` from `f(x) = f(x)` at `f(x)`: Reify takes the step at `f(x)`'s EX witness, which the conclusion
/// does not mention.
@Test
func anExistentialIntroAtACompoundTermIsTakenAtItsWitness() throws {
    var l = LogicTable()
    let fx = try l.t.intern(.isaVarApp(head: try l.bound(1, F), args: [try l.bound(0, i)]))
    let body = try l.equal(
        i,
        try l.bound(0, i),
        try l.t.intern(.isaVarApp(head: try l.bound(2, F), args: [try l.bound(1, i)])),
    )
    let intro = try l.t.intern(.isaExIntro(try l.t.intern(.isaReflexive(fx)), fx, body: body))
    let thm = Statement(
        name: "T.someValue",
        root: try l.all(F, try l.all(i, try l.t.intern(.ifolEx(i, body: body)))),
        proof: try l.t.intern(.isaAllIntro(F, body: try l.t.intern(.isaAllIntro(i, body: intro)))),
        theory: "Test",
    )
    let unit = try lowered(l, [thm])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀x a. (⋀F. x ∈ F(a)) ⟹ x ∈ x` at `F := λy. x`: β's back direction closes the source's value level at `x`, which
/// stands elsewhere in the atom, by the level's own formula (`equalities.Sigma_succ2`'s case).
@Test
func aLambdasBackDirectionClosesItsValuesLevelByItsFormula() throws {
    var l = LogicTable()
    let premise = try l.all(
        F,
        try l.mem(try l.bound(2, i), try l.t.intern(.isaVarApp(head: try l.bound(0, F), args: [try l.bound(1, i)]))),
    )
    let xx = try l.mem(try l.bound(1, i), try l.bound(1, i))
    let lambda = try l.lam(i, try l.bound(2, i))
    let proof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(
        i,
        body: try l.t.intern(.folImpliesIntro(
            premise,
            body: try l.t.intern(.isaAllElim(try l.t.intern(.hyp(0, premise)), lambda)),
        )),
    ))))
    let thm = Statement(
        name: "T.local",
        root: try l.all(i, try l.all(i, try l.imp(premise, xx))),
        proof: proof,
        theory: "Test",
    )
    let unit = try lowered(l, [thm])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
