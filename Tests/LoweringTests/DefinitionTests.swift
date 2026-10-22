import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private let P = IRType.fn(.i, .o)
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private func lowered(_ l: LogicTable, _ statements: [Statement], _ definitions: [Definition]) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements, definitions: definitions)
    try pipeline(b).run(&unit)
    return unit
}

private func pow(_ x: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.const(.primitive(.zf(.pow)), fn(i, i), x)
}

private func zero(_ l: inout LogicTable) throws -> NodeID {
    try l.const(.primitive(.zf(.zero)), i)
}

private func applied(_ head: NodeID, _ x: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.t.intern(.isaVarApp(head: head, args: [x]))
}

/// The definition axiom of `d` cited at `args`, its statement `stated`.
private func cited(_ d: Definition, _ stated: NodeID, _ args: [NodeID], _ l: inout LogicTable) throws -> NodeID {
    try l.t.intern(.isaDefinition(d.constant.name + "_def_raw", of: d.defines, [], stated, args: args))
}

/// The definition command's axiom `c ≡ λx⃗. b`, its left side `c` read η-long as `eta`.
private func raw(_ d: Definition, eta: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.equal(d.type, eta, d.definiens)
}

private func checked(_ unit: Unit, holding names: Set<String>) throws {
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(names.isSubset(of: Set(unit.statements.map(\.name))), "\(unit.statements.map(\.name))")
    try kernelChecks(unit)
}

/// `T.s ≡ λx. Pow(x)` at no terms, as `succ_def`'s proof cites `succ_def_raw`: `transitive (reflexive T.s)`, an
/// equation
/// between functions read pointwise, its leaf `T.s_UNFOLD`.
@Test
func aFunctionsDefinitionAtNoTermsIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let s = try l.definition(Defined(.zf, "T.s", .object), fn(i, i), try l.lam(i, try pow(x, &l)))
    let eta = try l.lam(i, try l.const(.defined(s.constant), fn(i, i), x))
    let stated = try raw(s, eta: eta, &l)
    let proof = try l.t.intern(.isaTransitive(
        fn(i, i),
        try l.t.intern(.isaReflexive(eta)),
        try cited(s, stated, [], &l),
    ))
    let unit = try lowered(l, [Statement(name: "T.s_def", root: stated, proof: proof, theory: "Test")], [s])
    try checked(unit, holding: ["T.s_def", "T.s_UNFOLD", "T.s_DEF"])
}

/// A package's `⋀x. T.s(x) ≡ Pow(x)` at a variable and at the compound term `Pow(0)`: the lemma instantiated by
/// `forall_elim` at the one and by Reify's instance at the other.
@Test
func aPackagesDefinitionAtItsTermsIsItsUnfoldingLemmaInstantiated() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let s = try l.definition(Defined(.zf, "T.s", .object), fn(i, i), parameters: 1, try l.lam(i, try pow(x, &l)))
    let stated = try l.all(i, try l.equal(i, try l.const(.defined(s.constant), fn(i, i), x), try pow(x, &l)))
    let atVariable = Statement(
        name: "T.at_variable",
        root: stated,
        proof: try l.t.intern(.isaAllIntro(i, body: try cited(s, stated, [x], &l))),
        theory: "Test",
    )
    let term = try pow(try zero(&l), &l)
    let atTerm = Statement(
        name: "T.at_term",
        root: try l.equal(i, try l.const(.defined(s.constant), fn(i, i), term), try pow(term, &l)),
        proof: try cited(s, stated, [term], &l),
        theory: "Test",
    )
    let unit = try lowered(l, [atVariable, atTerm], [s])
    try checked(unit, holding: ["T.at_variable", "T.at_term", "T.s_UNFOLD"])
}

/// `T.p ≡ λx. 0 ∈ x`, a predicate: `≡` at its value is `↔`, both ways through `T.p`'s class.
@Test
func aPredicatesDefinitionIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let p = try l.definition(Defined(.zf, "T.p", .object), fn(i, o), try l.lam(i, try l.mem(try zero(&l), x)))
    let stated = try raw(p, eta: try l.lam(i, try l.const(.defined(p.constant), fn(i, o), x)), &l)
    let proof = try cited(p, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.p_def", root: stated, proof: proof, theory: "Test")], [p])
    try checked(unit, holding: ["T.p_def", "T.p_UNFOLD"])
}

/// `T.e ≡ Pow(0)`, a set constant: `T.e`'s value by `T.e_EX`, no tuple.
@Test
func aSetConstantsDefinitionIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let e = try l.definition(Defined(.zf, "T.e", .object), i, try pow(try zero(&l), &l))
    let stated = try raw(e, eta: try l.const(.defined(e.constant), i), &l)
    let proof = try cited(e, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.e_def", root: stated, proof: proof, theory: "Test")], [e])
    try checked(unit, holding: ["T.e_def", "T.e_UNFOLD"])
}

/// `T.q ≡ 0 ∈ Pow(0)`, a proposition of no arguments: `≡` at its value is `↔`, through `T.q`'s class of the empty
/// tuple, S4's truth set.
@Test
func aPropositionsDefinitionOfNoArgumentsIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let q = try l.definition(Defined(.zf, "T.q", .object), o, try l.mem(try zero(&l), try pow(try zero(&l), &l)))
    let stated = try raw(q, eta: try l.const(.defined(q.constant), o), &l)
    let proof = try cited(q, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.q_def", root: stated, proof: proof, theory: "Test")], [q])
    try checked(unit, holding: ["T.q_def", "T.q_UNFOLD", "T.q_DEF"])
}

/// `T.q ≡ ∀x. x ∈ x ⟶ x ∈ x` and `T.r ≡ T.q`, as `AC_Equiv`'s propositions: `T.q` proved through its definition, and
/// `T.q ⟹ T.r` through `T.r`'s, whose class holds `T.q`'s atom.
@Test
func aPropositionOfNoArgumentsIsProvedThroughItsDefinition() throws {
    var l = LogicTable()
    let member = try l.mem(try l.bound(0, i), try l.bound(0, i))
    let q = try l.definition(Defined(.zf, "T.q", .object), o, try l.all(i, try l.imp(member, member)))
    let atQ = try l.const(.defined(q.constant), o)
    let r = try l.definition(Defined(.zf, "T.r", .object), o, atQ)
    let atR = try l.const(.defined(r.constant), o)
    let reflexivity = try l.t.intern(.isaAllIntro(
        i,
        body: try l.t.intern(.folImpliesIntro(member, body: try l.t.intern(.hyp(0, member)))),
    ))
    let holds = try l.t.intern(.folIffElimL(
        try l.t.intern(.isaSymmetric(o, try cited(q, try raw(q, eta: atQ, &l), [], &l))),
        reflexivity,
    ))
    let implied = try l.t.intern(.folImpliesIntro(atQ, body: try l.t.intern(.folIffElimL(
        try l.t.intern(.isaSymmetric(o, try cited(r, try raw(r, eta: atR, &l), [], &l))),
        try l.t.intern(.hyp(0, atQ)),
    ))))
    let unit = try lowered(l, [
        Statement(name: "T.q_holds", root: atQ, proof: holds, theory: "Test"),
        Statement(name: "T.q_r", root: try l.imp(atQ, atR), proof: implied, theory: "Test"),
    ], [q, r])
    try checked(unit, holding: ["T.q_holds", "T.q_r"])
}

/// `T.ball ≡ λA P. ∀x. x ∈ A ⟶ P(x)`, a predicate taking a class: its slot holds `λx. P(x)`, named by its class, and
/// the
/// `@def`'s applications of that class are read back as `P`'s.
@Test
func aDefinitionTakingAClassIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let ball = try l.definition(
        Defined(.zf, "T.ball", .object),
        fn(i, fn(P, o)),
        try l.lam(i, try l.lam(P, try l.all(i, try l.imp(
            try l.mem(x, try l.bound(2, i)),
            try applied(try l.bound(1, P), x, &l),
        )))),
    )
    let slot = try l.lam(i, try applied(try l.bound(1, P), x, &l))
    let eta = try l.lam(i, try l.lam(P, try l.const(.defined(ball.constant), fn(i, fn(P, o)), try l.bound(1, i), slot)))
    let stated = try raw(ball, eta: eta, &l)
    let proof = try cited(ball, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.ball_def", root: stated, proof: proof, theory: "Test")], [ball])
    try checked(unit, holding: ["T.ball_def", "T.ball_UNFOLD"])
}

/// `T.ap ≡ λF x. F(x)`, a function taking a function: its slot holds `λy. F(y)`, and the value read back through
/// `apply`.
@Test
func aDefinitionTakingAFunctionIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let F = fn(i, i)
    let x = try l.bound(0, i)
    let ap = try l.definition(
        Defined(.zf, "T.ap", .object),
        fn(F, fn(i, i)),
        try l.lam(F, try l.lam(i, try applied(try l.bound(1, F), x, &l))),
    )
    let slot = try l.lam(i, try applied(try l.bound(2, F), x, &l))
    let eta = try l.lam(F, try l.lam(i, try l.const(.defined(ap.constant), fn(F, fn(i, i)), slot, x)))
    let stated = try raw(ap, eta: eta, &l)
    let proof = try cited(ap, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.ap_def", root: stated, proof: proof, theory: "Test")], [ap])
    try checked(unit, holding: ["T.ap_def", "T.ap_UNFOLD"])
}

/// `T.two ≡ λA P F. ∀x. x ∈ A ⟶ P(F(x))`, two class parameters: each read back in turn, the later one still at its
/// class, and `F`'s guard discharged where it is instantiated.
@Test
func aDefinitionTakingTwoClassesIsItsUnfoldingLemma() throws {
    var l = LogicTable()
    let F = fn(i, i)
    let x = try l.bound(0, i)
    let type = fn(i, fn(P, fn(F, o)))
    let image = try applied(try l.bound(2, P), try applied(try l.bound(1, F), x, &l), &l)
    let two = try l.definition(
        Defined(.zf, "T.two", .object),
        type,
        try l.lam(i, try l.lam(P, try l.lam(F, try l.all(i, try l.imp(try l.mem(x, try l.bound(3, i)), image))))),
    )
    let slotP = try l.lam(i, try applied(try l.bound(2, P), x, &l))
    let slotF = try l.lam(i, try applied(try l.bound(1, F), x, &l))
    let eta = try l.lam(i, try l.lam(P, try l.lam(F, try l.const(
        .defined(two.constant),
        type,
        try l.bound(2, i),
        slotP,
        slotF,
    ))))
    let stated = try raw(two, eta: eta, &l)
    let proof = try cited(two, stated, [], &l)
    let unit = try lowered(l, [Statement(name: "T.two_def", root: stated, proof: proof, theory: "Test")], [two])
    try checked(unit, holding: ["T.two_def", "T.two_UNFOLD"])
}

/// `T.cmp ≡ λF A. ∀x. x ∈ A ⟶ F(Pow(x)) ∈ A` at its terms `λy. G(y)` and `B`, as `measure_def` applies `f` to `fst(p)`:
/// `Pow(x)` holds the formula's own `x`, so β reads `F`'s application at its name, in the unfolding's read-back and in
/// the instance at `G` (DESIGN "Linear proof size", 5).
@Test
func aDefinitionApplyingItsFunctionToACompoundArgumentIsItsUnfoldingAtItsTerms() throws {
    var l = LogicTable()
    let F = fn(i, i)
    let type = fn(F, fn(i, o))
    let x = try l.bound(0, i)
    let body = { (f: NodeID, a: NodeID, l: inout LogicTable) throws -> NodeID in
        try l.all(i, try l.imp(try l.mem(x, a), try l.mem(try applied(f, try pow(x, &l), &l), a)))
    }
    let cmp = try l.definition(
        Defined(.zf, "T.cmp", .object),
        type,
        parameters: 2,
        try l.lam(F, try l.lam(i, try body(try l.bound(2, F), try l.bound(1, i), &l))),
    )
    let eta = { (k: Int, l: inout LogicTable) throws -> NodeID in
        try l.lam(i, try applied(try l.bound(k + 1, F), try l.bound(0, i), &l))
    }
    let atom = try l.const(.defined(cmp.constant), type, try eta(1, &l), try l.bound(0, i))
    let pointwise = try l.equal(o, atom, try body(try l.bound(2, F), try l.bound(1, i), &l))
    let stated = try l.all(F, try l.all(i, pointwise))
    let proof = try l.t.intern(.isaAllIntro(F, body: try l.t.intern(.isaAllIntro(
        i,
        body: try cited(cmp, stated, [try eta(1, &l), try l.bound(0, i)], &l),
    ))))
    let unit = try lowered(l, [Statement(name: "T.cmp_def", root: stated, proof: proof, theory: "Test")], [cmp])
    try checked(unit, holding: ["T.cmp_def", "T.cmp_UNFOLD"])
}
