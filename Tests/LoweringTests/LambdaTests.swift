import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private let P = IRType.fn(.i, .o)
private let F = IRType.fn(.i, .i)
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private func lowered(_ l: LogicTable, _ statements: [Statement], _ definitions: [Definition] = []) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements, definitions: definitions)
    try pipeline(b).run(&unit)
    return unit
}

private func pow(_ x: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.const(.primitive(.zf(.pow)), fn(i, i), x)
}

/// `PrimReplace(A, R)`, `R` a relation λ.
private func replaced(_ a: NodeID, _ relation: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.const(.primitive(.zf(.primReplace)), fn(i, fn(fn(i, fn(i, o)), i)), a, relation)
}

/// `⋀P a. P(t(a)) ⟶ P(t(a))`, proved by its hypothesis; `t` gives the class variable's argument under `⋀P a`.
private func theorem(
    _ name: String,
    _ l: inout LogicTable,
    _ argument: (NodeID, inout LogicTable) throws -> NodeID,
) throws -> Statement {
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [try argument(try l.bound(0, i), &l)]))
    let root = try l.all(P, try l.all(i, try l.imp(applied, applied)))
    let proof = try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
        .folImpliesIntro(applied, body: try l.t.intern(.hyp(0, applied)))
    )))))
    return Statement(name: name, root: root, proof: proof, theory: "Test")
}

/// `⋀A b. φ ⟶ φ` by `cited · λ · b`, `λ` and `φ` under `⋀A b`.
private func user(
    _ name: String,
    _ cited: Statement,
    _ lambda: NodeID,
    _ phi: NodeID,
    _ l: inout LogicTable,
) throws -> Statement {
    let atLambda = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem(cited.name), [], cited.root)), lambda))
    let proof = try l.t.intern(.isaAllElim(atLambda, try l.bound(0, i)))
    return Statement(
        name: name,
        root: try l.all(i, try l.all(i, try l.imp(phi, phi))),
        proof: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(i, body: proof)))),
        theory: "Test",
    )
}

/// `thm · (λx. x ∈ A)`: the λ's class opened by its existence, `thm`'s class binder eliminated at it, and the formula's
/// `BETA_<fp>` lemma reading the class at `⟨b⟩` as the λ's body at `b`. The kernel proves the unit.
@Test
func anInstanceAtALambdaIsItsClassThenBeta() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, _ in x }
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let use = try user("T.use", thm, lambda, try l.mem(try l.bound(0, i), try l.bound(1, i)), &l)
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.contains { $0.name.hasPrefix("BETA_") })
    try kernelChecks(unit)
}

/// `⋀Q b. Q ⟶ Q` by `thm · (λx. Q) · b`: the λ closes over the letter `Q`, as iprover's `allE` at `λx. P` in
/// `quant_simps` does; its class a schema at the letter, read by base's `row_letter` (DESIGN "The class of a λ
/// holding a proposition"). The kernel proves the unit.
@Test
func anInstanceAtALambdaHoldingALetterIsItsClassThenBeta() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, _ in x }
    let q = try l.bound(1, o)
    let atLambda = try l.t.intern(.isaAllElim(
        try l.t.intern(.use(.theorem(thm.name), [], thm.root)),
        try l.lam(i, try l.bound(2, o)),
    ))
    let proof = try l.t.intern(.isaAllElim(atLambda, try l.bound(0, i)))
    let root = try l.all(o, try l.all(i, try l.imp(q, q)))
    let closed = try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(i, body: proof))))
    #expect(l.t.conclusion(of: closed) == root)
    let unit = try lowered(l, [thm, Statement(name: "T.use", root: root, proof: closed, theory: "Test")])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(unit.statements.contains { $0.name.hasPrefix("CLASS_") })
    try kernelChecks(unit)
}

/// `⋀P a. P(Pow(a)) ⟶ …` at `λx. x ∈ A`: β at `Pow(b)`'s value, under its naming, is Isabelle's `Pow(b) ∈ A` by ID. At
/// `λx. x = x` the body names `Pow(b)` twice, and EX and UNIQ of `Pow(b)` convert.
@Test
func anInstanceAtACompoundArgumentIsBetaAtItsValue() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, l in try pow(x, &l) }
    let member = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let once = try user("T.once", thm, member, try l.mem(try pow(try l.bound(0, i), &l), try l.bound(1, i)), &l)
    let selfEqual = try l.lam(i, try l.equal(i, try l.bound(0, i), try l.bound(0, i)))
    let powB = try pow(try l.bound(0, i), &l)
    let twice = try user("T.twice", thm, selfEqual, try l.equal(i, powB, powB), &l)
    let unit = try lowered(l, [thm, once, twice])
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `⋀P. (∀x. P(Pow(x))) ⟶ (∀x. P(Pow(x)))` at `λy. c = c ⟶ y ∈ A`: `Pow(x)` holds the formula's own `x`, and the λ's
/// body names it below its implication; β is at its value, fixed at the atom (DESIGN "β at values").
@Test
func aSharedArgumentTheBodyNamesBelowAConnectiveIsBetaAtItsValue() throws {
    var l = LogicTable()
    let stated = try l.all(
        i,
        try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [try pow(try l.bound(0, i), &l)])),
    )
    let root = try l.all(P, try l.imp(stated, stated))
    let thmProof = try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.folImpliesIntro(
        stated,
        body: try l.t.intern(.hyp(0, stated)),
    ))))
    let thm = Statement(name: "T.thm", root: root, proof: thmProof, theory: "Test")
    let lambda = try l.lam(i, try l.imp(try l.equal(i, try l.bound(2, i), try l.bound(2, i)), try l.mem(
        try l.bound(0, i),
        try l.bound(1, i),
    )))
    let phi = try l.all(i, try l.imp(try l.equal(i, try l.bound(2, i), try l.bound(2, i)), try l.mem(
        try pow(try l.bound(0, i), &l),
        try l.bound(1, i),
    )))
    let instance = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], root)), lambda))
    let useRoot = try l.all(i, try l.all(i, try l.imp(phi, phi)))
    let useProof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(i, body: instance))))
    #expect(l.t.conclusion(of: useProof) == useRoot)
    let unit = try lowered(l, [thm, Statement(name: "T.use", root: useRoot, proof: useProof, theory: "Test")])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀F a⃗ B. t ∈ B ⟶ t ∈ B`, `t` built from `F` and `a⃗`, proved by its hypothesis; and its use at `λ`, concluding `used`
/// under `⋀a⃗ B`.
private func functional(
    _ F: IRType,
    _ n: Int,
    _ lambda: NodeID,
    _ used: NodeID,
    _ l: inout LogicTable,
    _ term: (NodeID, [NodeID], inout LogicTable) throws -> NodeID,
) throws -> [Statement] {
    let args = try (0..<n).map { try l.bound(n - $0, i) }
    let member = try l.mem(try term(try l.bound(n + 1, F), args, &l), try l.bound(0, i))
    var root = try l.imp(member, member)
    var proof = try l.t.intern(.folImpliesIntro(member, body: try l.t.intern(.hyp(0, member))))
    for _ in 0...n { (root, proof) = (try l.all(i, root), try l.t.intern(.isaAllIntro(i, body: proof))) }
    root = try l.all(F, root)
    let thm = Statement(name: "T.thm", root: root, proof: try l.t.intern(.isaAllIntro(F, body: proof)), theory: "Test")
    var instance = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], root)), lambda))
    for k in (0...n).reversed() { instance = try l.t.intern(.isaAllElim(instance, try l.bound(k, i))) }
    var usedRoot = try l.imp(used, used)
    for _ in 0...n { (usedRoot, instance) = (try l.all(i, usedRoot), try l.t.intern(.isaAllIntro(i, body: instance))) }
    return [thm, Statement(name: "T.use", root: usedRoot, proof: instance, theory: "Test")]
}

/// `⋀F a B. F(a) ∈ B ⟶ F(a) ∈ B` at `λx. Pow(x)`: `F(a)` is read through `apply`; the λ's class at `a` has `Pow(a)`'s
/// value,
/// and its guard, `function(K)`, is the lemma's own.
@Test
func anInstanceAtAFunctionLambdaIsBetaAtItsValue() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try pow(try l.bound(0, i), &l))
    let used = try l.mem(try pow(try l.bound(1, i), &l), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { F, a, l in try l.t.intern(.isaVarApp(head: F, args: a)) }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `F(a)` at `λx. x`: the body a variable, its value itself, whose EX the λ's lemma cites as any term's.
@Test
func anIdentityFunctionLambdaIsBetaAtItsArgument() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try l.bound(0, i))
    let used = try l.mem(try l.bound(1, i), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { F, a, l in try l.t.intern(.isaVarApp(head: F, args: a)) }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `F(a, b, c)` at `λx y z. y`: a projection, the body a variable among three.
@Test
func aProjectionLambdaOfThreeArgumentsIsBetaAtItsArgument() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try l.lam(i, try l.lam(i, try l.bound(1, i))))
    let used = try l.mem(try l.bound(2, i), try l.bound(0, i))
    let statements = try functional(fn(i, fn(i, fn(i, i))), 3, lambda, used, &l) { F, abc, l in
        try l.t.intern(.isaVarApp(
            head: F,
            args: abc,
        ))
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `F(F(a))` at `λx. Pow(x)`: the inner application at the variable `a`, the outer at `Pow(a)`, a compound argument,
/// which
/// Reify's instance converts.
@Test
func aNestedApplicationOfAFunctionLambdaIsBetaAtEachValue() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try pow(try l.bound(0, i), &l))
    let used = try l.mem(try pow(try pow(try l.bound(1, i), &l), &l), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { F, a, l in
        try l.t.intern(.isaVarApp(head: F, args: [try l.t.intern(.isaVarApp(head: F, args: a))]))
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `F(Pow(a)) ∈ B` at `λx. Pow(x)`: `Pow(a)` holds the formula's own `a`; β is at its value, fixed at the atom, and
/// `Pow(Pow(a))` is the value of `F`'s application there (DESIGN "β at values").
@Test
func anApplicationAtACompoundArgumentOverABoundVariableIsBetaAtItsValue() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try pow(try l.bound(0, i), &l))
    let used = try l.mem(try pow(try pow(try l.bound(1, i), &l), &l), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { F, a, l in
        try l.t.intern(.isaVarApp(head: F, args: [try pow(a[0], &l)]))
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀P a. P(Pow(a)) ⟶ …` at `λy. Pow(y) = y`: the body names `Pow(a)` again, inside `Pow(Pow(a))`; β is at its value.
@Test
func aBodyNamingItsArgumentAgainInsideAnotherTermIsBetaAtItsValue() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, l in try pow(x, &l) }
    let lambda = try l.lam(i, try l.equal(i, try pow(try l.bound(0, i), &l), try l.bound(0, i)))
    let powB = try pow(try l.bound(0, i), &l)
    let use = try user("T.use", thm, lambda, try l.equal(i, try pow(powB, &l), powB), &l)
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀P a. P(Pow(a)) ⟶ …` at `λy. PrimReplace(A, λu v. v = y) ∈ A`: the body names `Pow(a)` inside a λ, its slot's
/// class definition; β is at its value.
@Test
func aBodyNamingItsArgumentInsideALambdaIsBetaAtItsValue() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, l in try pow(x, &l) }
    let slot = try l.lam(i, try l.lam(i, try l.equal(i, try l.bound(0, i), try l.bound(2, i))))
    let lambda = try l.lam(i, try l.mem(try replaced(try l.bound(2, i), slot, &l), try l.bound(2, i)))
    let reduced = try l.lam(i, try l.lam(i, try l.equal(i, try l.bound(0, i), try pow(try l.bound(2, i), &l))))
    let phi = try l.mem(try replaced(try l.bound(1, i), reduced, &l), try l.bound(1, i))
    let use = try user("T.use", thm, lambda, phi, &l)
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `F(Pow(a)) ∈ B` at `λy. PrimReplace(y, λu v. v = y)`: the body holds its variable twice, once inside a λ; β is at
/// `Pow(a)`'s value, and the application's value the body's there.
@Test
func aFunctionLambdaHoldingItsVariableTwiceIsBetaAtItsValue() throws {
    var l = LogicTable()
    let slot = try l.lam(i, try l.lam(i, try l.equal(i, try l.bound(0, i), try l.bound(2, i))))
    let lambda = try l.lam(i, try replaced(try l.bound(0, i), slot, &l))
    let reduced = try l.lam(i, try l.lam(i, try l.equal(i, try l.bound(0, i), try pow(try l.bound(3, i), &l))))
    let used = try l.mem(try replaced(try pow(try l.bound(1, i), &l), reduced, &l), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { F, a, l in
        try l.t.intern(.isaVarApp(head: F, args: [try pow(a[0], &l)]))
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `F(Pow(a), b) ∈ B` at `λy z. Pow(z)`: the body does not hold `y`, so `Pow(a)` stands in no form of the target; β is
/// at the arguments' values all the same.
@Test
func aFunctionLambdaDroppingAnArgumentIsBetaAtItsValues() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try l.lam(i, try pow(try l.bound(0, i), &l)))
    let used = try l.mem(try pow(try l.bound(1, i), &l), try l.bound(0, i))
    let statements = try functional(fn(i, fn(i, i)), 2, lambda, used, &l) { F, ab, l in
        try l.t.intern(.isaVarApp(head: F, args: [try pow(ab[0], &l), ab[1]]))
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀P a. P(PrimReplace(0, λu v. P(v))) ⟶ …` at `λy. y ∈ A`: the argument holds the class variable, named in one form
/// and its reduced form's value in the other; β is at that value, the slot's class kept and its definition converted.
@Test
func anArgumentHoldingTheClassVariableIsBetaAtItsReducedValue() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { _, l in
        let slot = try l.lam(i, try l.lam(i, try l.t.intern(.isaVarApp(
            head: try l.bound(3, P),
            args: [try l.bound(0, i)],
        ))))
        return try replaced(try l.const(.primitive(.zf(.zero)), i), slot, &l)
    }
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let reduced = try l.lam(i, try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(3, i))))
    let phi = try l.mem(try replaced(try l.const(.primitive(.zf(.zero)), i), reduced, &l), try l.bound(1, i))
    let use = try user("T.use", thm, lambda, phi, &l)
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀P a. P(PrimReplace(0, λu v. P(v))) ⟶ …` at `λy. A ∈ A`: the body drops the argument, so its reduced form's value
/// stands in no form the lemma premises; it is fixed at the atom.
@Test
func anArgumentHoldingTheClassVariableTheBodyDropsIsFixedAtItsAtom() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { _, l in
        let slot = try l.lam(i, try l.lam(i, try l.t.intern(.isaVarApp(
            head: try l.bound(3, P),
            args: [try l.bound(0, i)],
        ))))
        return try replaced(try l.const(.primitive(.zf(.zero)), i), slot, &l)
    }
    let lambda = try l.lam(i, try l.mem(try l.bound(2, i), try l.bound(2, i)))
    let use = try user("T.use", thm, lambda, try l.mem(try l.bound(1, i), try l.bound(1, i)), &l)
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `PrimReplace(F(a), λu v. v = F(Pow(a))) ∈ B` at `λy. Pow(y)`: the atom applies `F`, and so does the slot inside it,
/// at a term over the walk's `a`; the slot's atom meets the values the outer atom fixes, and fixes none of them again.
@Test
func anApplicationInASlotOfAnAtomApplyingTheClassVariableMeetsTheAtomsValues() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try pow(try l.bound(0, i), &l))
    let reduced = try l.lam(
        i,
        try l.lam(i, try l.equal(i, try l.bound(0, i), try pow(try pow(try l.bound(3, i), &l), &l))),
    )
    let used = try l.mem(try replaced(try pow(try l.bound(1, i), &l), reduced, &l), try l.bound(0, i))
    let statements = try functional(F, 1, lambda, used, &l) { head, a, l in
        let inner = try l.t.intern(.isaVarApp(head: try l.bound(4, F), args: [try pow(try l.bound(3, i), &l)]))
        let slot = try l.lam(i, try l.lam(i, try l.equal(i, try l.bound(0, i), inner)))
        return try replaced(try l.t.intern(.isaVarApp(head: head, args: a)), slot, &l)
    }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `F(a, b)` at `λx y. Pow(y)`: the λ's class at a pair.
@Test
func aFunctionLambdaOfTwoArgumentsIsBetaAtItsPair() throws {
    var l = LogicTable()
    let lambda = try l.lam(i, try l.lam(i, try pow(try l.bound(0, i), &l)))
    let used = try l.mem(try pow(try l.bound(1, i), &l), try l.bound(0, i))
    let statements = try functional(fn(i, fn(i, i)), 2, lambda, used, &l) { F, ab, l in try l.t.intern(.isaVarApp(
        head: F,
        args: ab,
    )) }
    let unit = try lowered(l, statements)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `⋀A a B. T.app(A, a) ∈ B ⟶ …` by `thm · (λx. T.app(A, x))`: a function λ holding a free variable, its body a defined
/// constant's value.
@Test
func aFunctionLambdaHoldingAVariableIsBetaAtItsValue() throws {
    var l = LogicTable()
    let app = try l.definition(
        Defined(.zf, "T.app", .object),
        fn(i, fn(i, i)),
        try l.lam(i, try l.lam(i, try pow(try l.bound(1, i), &l))),
    )
    let applied = { (a: NodeID, b: NodeID, l: inout LogicTable) throws -> NodeID in try l.const(
        .defined(app.constant),
        fn(i, fn(i, i)),
        a,
        b,
    ) }
    let member = try l.mem(
        try l.t.intern(.isaVarApp(head: try l.bound(2, F), args: [try l.bound(1, i)])),
        try l.bound(0, i),
    )
    let root = try l.all(F, try l.all(i, try l.all(i, try l.imp(member, member))))
    let proof = try l.t.intern(.isaAllIntro(
        F,
        body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
            .folImpliesIntro(member, body: try l.t.intern(.hyp(0, member)))
        ))))),
    ))
    let thm = Statement(name: "T.thm", root: root, proof: proof, theory: "Test")
    let lambda = try l.lam(i, try applied(try l.bound(3, i), try l.bound(0, i), &l))
    let atLambda = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], root)), lambda))
    let instance = try l.t.intern(.isaAllElim(
        try l.t.intern(.isaAllElim(atLambda, try l.bound(1, i))),
        try l.bound(0, i),
    ))
    let used = try l.mem(try applied(try l.bound(2, i), try l.bound(1, i), &l), try l.bound(0, i))
    let use = Statement(
        name: "T.use",
        root: try l.all(i, try l.all(i, try l.all(i, try l.imp(used, used)))),
        proof: try l.t.intern(.isaAllIntro(
            i,
            body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(i, body: instance)))),
        )),
        theory: "Test",
    )
    let unit = try lowered(l, [thm, use], [app])
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `⋀P A. T.ball(A, λx. P(x)) ⟶ …` at `λy. y ∈ B`: the class variable stands in `T.ball`'s class slot; the slot's class
/// is
/// kept and its definition converted, β inside it at the slot's own variable.
@Test
func aClassVariableInAClassSlotKeepsTheSlotsClass() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let ball = try l.definition(
        Defined(.zf, "T.ball", .object),
        fn(i, fn(P, o)),
        try l.lam(i, try l.lam(P, try l.all(i, try l.imp(
            try l.mem(x, try l.bound(2, i)),
            try l.t.intern(.isaVarApp(
                head: try l.bound(1, P),
                args: [x],
            )),
        )))),
    )
    let slot = try l.lam(i, try l.t.intern(.isaVarApp(head: try l.bound(2, P), args: [try l.bound(0, i)])))
    let atom = try l.const(.defined(ball.constant), fn(i, fn(P, o)), try l.bound(0, i), slot)
    let root = try l.all(P, try l.all(i, try l.imp(atom, atom)))
    let proof = try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
        .folImpliesIntro(atom, body: try l.t.intern(.hyp(0, atom)))
    )))))
    let thm = Statement(name: "T.thm", root: root, proof: proof, theory: "Test")
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let reduced = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let used = try l.const(.defined(ball.constant), fn(i, fn(P, o)), try l.bound(0, i), reduced)
    let use = try user("T.use", thm, lambda, used, &l)
    let unit = try lowered(l, [thm, use], [ball])
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `thm · (λx. Q(x))`, `Q` the user's own class variable: an instance like any other, one rule for the piece.
@Test
func anEtaExpandedClassVariableIsAnInstanceLikeAnyOther() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, _ in x }
    let eta = try l.lam(i, try l.t.intern(.isaVarApp(head: try l.bound(2, P), args: [try l.bound(0, i)])))
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [try l.bound(0, i)]))
    let atLambda = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], thm.root)), eta))
    let proof = try l.t.intern(.isaAllElim(atLambda, try l.bound(0, i)))
    let use = Statement(
        name: "T.use",
        root: try l.all(P, try l.all(i, try l.imp(applied, applied))),
        proof: try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.isaAllIntro(i, body: proof)))),
        theory: "Test",
    )
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// `⋀Q A b. (b ∈ A ∧ Q) ⟶ …` by `thm · (λx. x ∈ A ∧ Q)`: the λ holds the statement's letter `Q`, so its lemmas are
/// schemas in it, cited by `schema_inst` at `Q`, its class read by base's `row_letter`. The kernel proves the unit.
@Test
func aLambdaHoldingALetterIsASchemaInIt() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, _ in x }
    let Q = { (k: Int, l: inout LogicTable) throws -> NodeID in try l.bound(k, o) }
    let lambda = try l.lam(i, try l.t.intern(.folAnd(try l.mem(try l.bound(0, i), try l.bound(2, i)), try Q(3, &l))))
    let phi = try l.t.intern(.folAnd(try l.mem(try l.bound(0, i), try l.bound(1, i)), try Q(2, &l)))
    let use = try user("T.use", thm, lambda, phi, &l)
    let schematic = Statement(
        name: "T.use",
        root: try l.all(o, use.root),
        proof: try l.t.intern(.isaAllIntro(o, body: try #require(use.proof))),
        theory: "Test",
    )
    let unit = try lowered(l, [thm, schematic])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀A b. ⋀P::prop. (b ∈ A ∧ P) ⟶ …` by `thm · (λx. x ∈ A ∧ P)`, `P` bound below the statement's top: a truth-set
/// variable, which the λ's lemma takes as a letter, cited at `holds(E)`. The kernel proves the unit.
@Test
func aLambdaHoldingATruthSetVariableIsASchemaCitedAtItsTruth() throws {
    var l = LogicTable()
    let thm = try theorem("T.thm", &l) { x, _ in x }
    let lambda = try l.lam(
        i,
        try l.t.intern(.folAnd(try l.mem(try l.bound(0, i), try l.bound(3, i)), try l.t.intern(.isaPropBound(1)))),
    )
    let phi = try l.t.intern(.folAnd(try l.mem(try l.bound(1, i), try l.bound(2, i)), try l.t.intern(.isaPropBound(0))))
    let atLambda = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem(thm.name), [], thm.root)), lambda))
    let instance = try l.t.intern(.isaAllElim(atLambda, try l.bound(1, i)))
    let root = try l.all(i, try l.all(i, try l.t.intern(.isaPropAll(body: try l.imp(phi, phi)))))
    let proof = try l.t.intern(.isaAllIntro(
        i,
        body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaPropIntro(body: instance)))),
    ))
    let unit = try lowered(l, [thm, Statement(name: "T.use", root: root, proof: proof, theory: "Test")])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `⋀P Q::o a. (P(a) ∧ Q) ⟶ …` at `λx. x ∈ A`, then at `Q`: the formula the λ meets binds the letter `Q` below its
/// top, which no first-order lemma states — its `BETA_<fp>` is refused unbuilt, and the use with it.
@Test
func aLetterTheCitedTheoremBindsBelowTheInstantiatedClassFallsWithItsLemma() throws {
    var l = LogicTable()
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(2, P), args: [try l.bound(0, i)]))
    let phi = try l.t.intern(.folAnd(applied, try l.bound(1, o)))
    let root = try l.all(P, try l.all(o, try l.all(i, try l.imp(phi, phi))))
    let proof = try l.t.intern(.isaAllIntro(
        P,
        body: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
            .folImpliesIntro(phi, body: try l.t.intern(.hyp(0, phi)))
        ))))),
    ))
    let thm = Statement(name: "T.thm", root: root, proof: proof, theory: "Test")
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(3, i)))
    let atQ = try l.t.intern(.isaAllElim(
        try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], root)), lambda)),
        try l.bound(1, o),
    ))
    let instance = try l.t.intern(.isaAllElim(atQ, try l.bound(0, i)))
    let used = try l.t.intern(.folAnd(try l.mem(try l.bound(0, i), try l.bound(2, i)), try l.bound(1, o)))
    let use = Statement(
        name: "T.use",
        root: try l.all(i, try l.all(o, try l.all(i, try l.imp(used, used)))),
        proof: try l.t.intern(.isaAllIntro(
            i,
            body: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(i, body: instance)))),
        )),
        theory: "Test",
    )
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.contains { $0.name.hasPrefix("BETA_") && $0.refusal == .lemmaUnbuilt })
    #expect(unit.refused.contains { $0.name == "T.use" })
}

/// The theorem above with its letter first, as the reader reads it (DESIGN "Letters first"): `schema_inst` at `Q` on
/// the citation, then the instance at the λ walks no binder over a proposition. The kernel proves the unit.
@Test
func aLetterInstantiatedFirstLeavesTheInstanceNoLetterToWalk() throws {
    var l = LogicTable()
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [try l.bound(0, i)]))
    let phi = try l.t.intern(.folAnd(applied, try l.bound(2, o)))
    let root = try l.all(o, try l.all(P, try l.all(i, try l.imp(phi, phi))))
    let proof = try l.t.intern(.isaAllIntro(
        o,
        body: try l.t.intern(.isaAllIntro(P, body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(
            .folImpliesIntro(phi, body: try l.t.intern(.hyp(0, phi)))
        ))))),
    ))
    let thm = Statement(name: "T.thm", root: root, proof: proof, theory: "Test")
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(2, i)))
    let atQ = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.thm"), [], root)), try l.bound(2, o)))
    let instance = try l.t.intern(.isaAllElim(try l.t.intern(.isaAllElim(atQ, lambda)), try l.bound(0, i)))
    let used = try l.t.intern(.folAnd(try l.mem(try l.bound(0, i), try l.bound(1, i)), try l.bound(2, o)))
    let use = Statement(
        name: "T.use",
        root: try l.all(o, try l.all(i, try l.all(i, try l.imp(used, used)))),
        proof: try l.t.intern(.isaAllIntro(
            o,
            body: try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.isaAllIntro(i, body: instance)))),
        )),
        theory: "Test",
    )
    let unit = try lowered(l, [thm, use])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
