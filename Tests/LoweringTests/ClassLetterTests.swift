import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private let P = IRType.fn(.i, .o)
/// A relativized predicate, its class first: ZF-Constructible's `bool_of_o_reflection` takes `P` at this type.
private let B = IRType.fn(P, P)

private func lowered(_ l: LogicTable, _ statements: [Statement]) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements)
    try pipeline(b).run(&unit)
    return unit
}

/// `B(λu. u ∈ x, x)`, `B` the bound variable `k` and `x` the bound variable `j` where it stands.
private func relativized(_ k: Int, _ j: Int, _ l: inout LogicTable) throws -> NodeID {
    let cls = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(j + 1, i)))
    return try l.t.intern(.isaVarApp(head: try l.bound(k, B), args: [cls, try l.bound(j, i)]))
}

/// `T.thm: ⋀P a. P(a) ⟶ P(a)`, by its hypothesis.
private func classTheorem(_ l: inout LogicTable) throws -> Statement {
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [try l.bound(0, i)]))
    let root = try l.all(P, try l.all(i, try l.imp(applied, applied)))
    let proof = try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
        .folImpliesIntro(applied, body: try l.t.intern(.hyp(0, applied)))
    )))))
    return Statement(name: "T.thm", root: root, proof: proof, theory: "Test")
}

/// `T.letter: ⋀B a. B(λu. u ∈ a, a) ⟶ B(λu. u ∈ a, a)`, by `T.thm · (λx. B(λu. u ∈ x, x)) · a`: Lambda's instance
/// cites the class of a λ holding the letter, its class argument varying with the λ's own variable, as
/// `bool_of_o_reflection`'s proof cites `And_reflection` at `λa x. P(##Lset(a), x)`.
private func letterTheorem(_ thm: Statement, _ l: inout LogicTable) throws -> Statement {
    let phi = try relativized(1, 0, &l)
    let root = try l.all(B, try l.all(i, try l.imp(phi, phi)))
    let atLambda = try l.t.intern(.isaAllElim(
        try l.t.intern(.use(.theorem(thm.name), [], thm.root)),
        try l.lam(i, try relativized(2, 0, &l)),
    ))
    let proof = try l.t.intern(.isaAllIntro(B, body: try l.t.intern(.isaAllIntro(
        i,
        body: try l.t.intern(.isaAllElim(atLambda, try l.bound(0, i))),
    ))))
    return Statement(name: "T.letter", root: root, proof: proof, theory: "Test")
}

/// `T.letter · λ · a`, closed by `⋀a`, and by `⋀B` first when the λ holds the citer's own letter.
private func citing(
    _ name: String,
    _ letter: Statement,
    _ lambda: NodeID,
    _ phi: NodeID,
    own: Bool,
    _ l: inout LogicTable,
) throws -> Statement {
    let atLambda = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem(letter.name), [], letter.root)), lambda))
    var proof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllElim(atLambda, try l.bound(0, i)))))
    var root = try l.all(i, try l.imp(phi, phi))
    if own { (root, proof) = (try l.all(B, root), try l.t.intern(.isaAllIntro(B, body: proof))) }
    return Statement(name: name, root: root, proof: proof, theory: "Test")
}

/// A statement's variable taking a class to a proposition is a schema letter of its arity, `A0(2)`, its lift the
/// statement's premise below it; the class of `λx. B(λu. u ∈ x, x)` is read through that lift (DESIGN
/// "ZF-Constructible's reflection", 2 and 3). The kernel proves the unit.
@Test
func aVariableTakingAClassIsALetterItsLiftAPremise() throws {
    var l = LogicTable()
    let thm = try classTheorem(&l)
    let letter = try letterTheorem(thm, &l)
    #expect(l.t.conclusion(of: try #require(letter.proof)) == letter.root)
    let unit = try lowered(l, [thm, letter])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    let stated = try #require(unit.statements.first { $0.name == "T.letter" })
    guard case .folLetterAll(2, let body) = unit.table[stated.root], case .folImplies = unit.table[body] else {
        Issue.record("T.letter is not a schema at a letter of arity 2 under its lift: \(unit.table[stated.root])")
        return
    }
    #expect(unit.statements.contains { $0.name.hasPrefix("CLASS_") })
    try kernelChecks(unit)
}

/// `⋀a. a ∈ a ⟶ a ∈ a` by `T.letter · (λM y. M(y)) · a`: `schema_inst` at the λ, its lift discharged by `LIFT ⟨λ⟩`,
/// which the class prover proves from the λ's body, and `⟨a⟩ ∈ k` met to `a ∈ a` by `BETA_<fp>_L`. The kernel proves
/// the unit.
@Test
func aLetterCitedAtALambdaIsDischargedByTheLambdasLift() throws {
    var l = LogicTable()
    let thm = try classTheorem(&l)
    let letter = try letterTheorem(thm, &l)
    let lambda = try l.lam(P, try l.lam(i, try l.t.intern(.isaVarApp(
        head: try l.bound(1, P),
        args: [try l.bound(0, i)],
    ))))
    let phi = try l.mem(try l.bound(0, i), try l.bound(0, i))
    let use = try citing("T.atLambda", letter, lambda, phi, own: false, &l)
    #expect(l.t.conclusion(of: try #require(use.proof)) == use.root)
    let unit = try lowered(l, [thm, letter, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(unit.statements.contains { $0.name.hasPrefix("LIFT_") })
    #expect(unit.statements.contains { $0.name.hasPrefix("BETA_") && $0.name.hasSuffix("_L") })
    try kernelChecks(unit)
}

/// `⋀B a. B(λz. z ∈ a, Pow(a)) ⟶ …` by `T.letter · (λM y. B(λz. M(z), Pow(y))) · a`, as `is_wfrec_reflection` cites
/// `is_recfun_reflection` at `λM y. MH(M, fst(y))`: the class parameter passed to the citer's own letter beside a term
/// of the set parameter, met by `BETA_<fp>_L`, its lift `LIFT ⟨λ⟩` closed over the citer's letter. The kernel proves
/// the unit.
@Test
func aLetterCitedAtALambdaHoldingTheCitersLetterIsMetByItsBeta() throws {
    var l = LogicTable()
    let thm = try classTheorem(&l)
    let letter = try letterTheorem(thm, &l)
    let atZ = try l.lam(i, try l.t.intern(.isaVarApp(head: try l.bound(2, P), args: [try l.bound(0, i)])))
    let pow = { (x: NodeID, l: inout LogicTable) throws -> NodeID in
        try l.const(.primitive(.zf(.pow)), .fn(i, i), x)
    }
    let lambda = try l.lam(P, try l.lam(i, try l.t.intern(.isaVarApp(
        head: try l.bound(3, B),
        args: [atZ, try pow(try l.bound(0, i), &l)],
    ))))
    let cls = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(1, i)))
    let phi = try l.t.intern(.isaVarApp(head: try l.bound(1, B), args: [cls, try pow(try l.bound(0, i), &l)]))
    let use = try citing("T.atOwnLambda", letter, lambda, phi, own: true, &l)
    #expect(l.t.conclusion(of: try #require(use.proof)) == use.root)
    let unit = try lowered(l, [thm, letter, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(unit.statements.contains { $0.name.hasPrefix("LIFT_") })
    #expect(unit.statements.contains { $0.name.hasPrefix("BETA_") && $0.name.hasSuffix("_L") })
    try kernelChecks(unit)
}

/// `⋀B a. B(λu. u ∈ a, a) ⟶ …` by `T.letter · (λM y. B(λz. M(z), y)) · a`, the citer's own letter η-long: its lift
/// discharged by the citer's own premise, no `LIFT ⟨λ⟩` — one there would need that same lift. The kernel proves the
/// unit.
@Test
func aLetterCitedAtTheCitersOwnLetterIsDischargedByItsPremise() throws {
    var l = LogicTable()
    let thm = try classTheorem(&l)
    let letter = try letterTheorem(thm, &l)
    let atZ = try l.lam(i, try l.t.intern(.isaVarApp(head: try l.bound(2, P), args: [try l.bound(0, i)])))
    let lambda = try l.lam(P, try l.lam(i, try l.t.intern(.isaVarApp(
        head: try l.bound(3, B),
        args: [atZ, try l.bound(0, i)],
    ))))
    let use = try citing("T.atOwn", letter, lambda, try relativized(1, 0, &l), own: true, &l)
    #expect(l.t.conclusion(of: try #require(use.proof)) == use.root)
    let unit = try lowered(l, [thm, letter, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(!unit.statements.contains { $0.name.hasPrefix("LIFT_") })
    try kernelChecks(unit)
}
