import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

/// Expand alone, each proof checked to conclude its statement BY ID, as the pipeline checks it.
private func expanded(_ l: LogicTable, _ statements: [Statement], _ definitions: [Definition]) throws -> Unit {
    var t = l.t
    let out = try run(Expand(), statements.flatMap { [$0.root, $0.proof!] }, definitions, in: &t)
    let expanded = statements.indices.map { k in Statement(
        name: statements[k].name,
        root: out[2 * k],
        proof: out[2 * k + 1],
    ) }
    for s in expanded { #expect(t.conclusion(of: s.proof!) == s.root, "\(s.name)") }
    return Unit(table: t, statements: expanded)
}

/// `¬C ⟹ ¬C` by its hypothesis: `¬` unfolds by `Not ≡ λP. P ⟶ ⊥` in the statement and the proof alike.
@Test
func aDefinedConstantOfTheLogicUnfoldsInAStatementAndItsProof() throws {
    var l = LogicTable()
    let not = try l.not()
    let c = try l.const(.declared("C"), o)
    let notC = try l.const(.defined(not.constant), fn(o, o), c)
    let proof = try l.t.intern(.folImpliesIntro(notC, body: try l.t.intern(.hyp(0, notC))))
    let unit = try expanded(l, [Statement(name: "thm", root: try l.imp(notC, notC), proof: proof)], [not])
    var m = LogicTable(t: unit.table)
    let unfolded = try m.imp(c, try m.bottom())
    #expect(unit.statements[0].root == (try m.imp(unfolded, unfolded)))
    #expect(unit.statements[0].proof == (try m.t.intern(.folImpliesIntro(
        unfolded,
        body: try m.t.intern(.hyp(0, unfolded)),
    ))))
}

/// `∃!x. x ∈ A`: the `λ` reduces into `Ex1`'s body. `True`, of no arguments, is its definiens.
@Test
func anArgumentAtAFunctionTypeReducesIntoTheBodyAndAConstantOfNoArgumentsIsItsDefiniens() throws {
    var l = LogicTable()
    let ex1 = try l.ex1()
    let truth = try l.truth()
    let a = try l.const(.declared("A"), i)
    let inA = try l.lam(i, try l.mem(try l.bound(0, i), a))
    let unique = try l.const(.defined(ex1.constant), fn(fn(i, o), o), inA)
    let isTrue = try l.const(.defined(truth.constant), o)
    let out = try run(Expand(), [unique, isTrue], [ex1, truth], in: &l.t)
    let x = try l.bound(1, i)
    let y = try l.bound(0, i)
    let only = try l.all(i, try l.imp(try l.mem(y, a), try l.equal(i, y, x)))
    let exists = try l.t.intern(.ifolEx(i, body: try l.and(try l.mem(try l.bound(0, i), a), only)))
    #expect(out == [exists, try l.imp(try l.bottom(), try l.bottom())])
}

/// `nand(C, C)`, `nand ≡ λP Q. ¬(P ∧ Q)` using `¬`: both unfold, whichever definition comes first.
@Test
func aDefinitionUsingAnotherUnfoldsThroughBoth() throws {
    var l = LogicTable()
    let not = try l.not()
    let nandConstant = Defined(.ifol, "IFOL.nand", .object)
    let both = try l.and(try l.bound(1, o), try l.bound(0, o))
    let body = try l.const(.defined(not.constant), fn(o, o), both)
    let nand = try l.definition(nandConstant, fn(o, fn(o, o)), try l.lam(o, try l.lam(o, body)))
    let c = try l.const(.declared("C"), o)
    let used = try l.const(.defined(nandConstant), fn(o, fn(o, o)), c, c)
    #expect(try run(Expand(), [used], [nand, not], in: &l.t) == [try l.imp(
        try l.and(c, c),
        try l.bottom(),
    )])
}

/// `Not ≡ λP. P ⟶ ⊥`, cited at no terms: unfolded it says `(λP. P ⟶ ⊥) ≡ (λP. P ⟶ ⊥)`, Pure's `reflexive` step at the
/// definiens.
@Test
func aDefinitionAtNoTermsBecomesReflexivityAtItsDefiniens() throws {
    var l = LogicTable()
    let not = try l.not()
    let applied = try l.lam(o, try l.const(.defined(not.constant), fn(o, o), try l.bound(0, o)))
    let root = try l.equal(fn(o, o), applied, not.definiens)
    let proof = try l.t.intern(.isaDefinition("IFOL.not_def_raw", of: not.defines, [], root, args: []))
    let unit = try expanded(l, [Statement(name: "IFOL.not_def", root: root, proof: proof)], [not])
    var m = LogicTable(t: unit.table)
    #expect(unit.statements[0].root == (try m.equal(fn(o, o), not.definiens, not.definiens)))
    #expect(unit.statements[0].proof == (try m.t.intern(.isaReflexive(not.definiens))))
}

/// `⋀A B. conjunction(A, B) ≡ b`, Pure's applied form, at its terms `C` and `D`: unfolded it says `b[C, D] ≡ b[C, D]`,
/// the `reflexive` step there, no binder. A parameter the application leaves is bound as before: at `C` alone,
/// `⋀B. b[C, B] ≡ b[C, B]` under one `⋀`-intro; at no terms, under both.
@Test
func anAppliedDefinitionAtItsTermsIsReflexivityThere() throws {
    var l = LogicTable()
    let conjunction = try l.conjunction()
    let body = try l.conjunctionBody()
    let applied = try l.const(.defined(conjunction.constant), fn(o, fn(o, o)), try l.bound(1, o), try l.bound(0, o))
    let root = try l.all(o, try l.all(o, try l.equal(o, applied, body)))
    let c = try l.const(.declared("C"), o)
    let d = try l.const(.declared("D"), o)
    let cited = { (args: [NodeID], t: inout Table) in
        try t.intern(.isaDefinition("Pure.conjunction_def", of: conjunction.defines, [], root, args: args))
    }
    let both = try cited([c, d], &l.t)
    let one = try cited([c], &l.t)
    let none = try cited([], &l.t)
    let statements = [both, one, none].enumerated().map { k, p in Statement(
        name: "s\(k)",
        root: l.t.conclusion(of: p)!,
        proof: p,
    ) }
    let unit = try expanded(l, statements, [conjunction])
    var m = LogicTable(t: unit.table)
    let atCD = try beta(try m.lam(o, try m.lam(o, body)), [c, d], in: &m.t)
    #expect(unit.statements[0].proof == (try m.t.intern(.isaReflexive(atCD))))
    let atC = try beta(try m.lam(o, try m.lam(o, body)), [try shift(c, by: 1, in: &m.t), try m.bound(0, o)], in: &m.t)
    #expect(unit.statements[1].proof == (try m.t.intern(.isaAllIntro(o, body: try m.t.intern(.isaReflexive(atC))))))
    let instance = try m.t.intern(.isaReflexive(body))
    #expect(unit.statements[2].root == (try m.all(o, try m.all(o, try m.equal(o, body, body)))))
    #expect(unit.statements[2].proof == (try m.t.intern(.isaAllIntro(
        o,
        body: try m.t.intern(.isaAllIntro(o, body: instance)),
    ))))
}

/// The walk unfolds every citation's statement: a cited theorem's stays the theorem's own statement, one node, and
/// the axiom `iff_reflection`, `(P ↔ Q) ⟹ (P ≡ Q)`, is cited at its statement with `↔` unfolded.
@Test
func aCitationsStatementUnfoldsAsEveryFormula() throws {
    var l = LogicTable()
    let not = try l.not()
    let iff = try l.iff()
    let c = try l.const(.declared("C"), o)
    let notC = try l.const(.defined(not.constant), fn(o, o), c)
    let lemRoot = try l.imp(notC, notC)
    let lem = Statement(
        name: "lem",
        root: lemRoot,
        proof: try l.t.intern(.folImpliesIntro(notC, body: try l.t.intern(.hyp(0, notC)))),
    )
    let thm = Statement(name: "thm", root: lemRoot, proof: try l.t.intern(.use(.theorem("lem"), [], lemRoot)))
    let p = try l.bound(1, o)
    let q = try l.bound(0, o)
    let pIffQ = try l.const(.defined(iff.constant), fn(o, fn(o, o)), p, q)
    let reflection = try l.all(o, try l.all(o, try l.imp(pIffQ, try l.equal(o, p, q))))
    let cites = Statement(
        name: "cites",
        root: reflection,
        proof: try l.t.intern(.use(.axiom(.ifol(.iffReflection)), [], reflection)),
    )
    let unit = try expanded(l, [lem, thm, cites], [not, iff])
    var m = LogicTable(t: unit.table)
    #expect(unit.statements[1].proof == (try m.t.intern(.use(.theorem("lem"), [], unit.statements[0].root))))
    let unfolded = try m.all(
        o,
        try m.all(o, try m.imp(try m.and(try m.imp(p, q), try m.imp(q, p)), try m.equal(o, p, q))),
    )
    #expect(unit.statements[2].proof == (try m.t.intern(.use(.axiom(.ifol(.iffReflection)), [], unfolded))))
}

/// `OFCLASS(i, term)` is its class's definition at `i`, `⋀P. P ⟹ P`: a proposition bound in a formula. The definition
/// cited at `[i]` says `OFCLASS(i, term) ≡ ⋀P. P ⟹ P`; unfolded, the `reflexive` step at that definiens.
@Test
func aClassMembershipUnfoldsByItsClassDefinitionAndACitationOfItIsReflexive() throws {
    var l = LogicTable()
    let term = TypeClass(.ifol, "IFOL.term")
    let p = try l.t.intern(.isaPropBound(0))
    let definiens = try l.t.intern(.isaPropAll(body: try l.imp(p, p)))
    let definition = Definition(defines: .ofClass(term), type: o, axiomTypes: [i], parameters: 0, definiens: definiens)
    let root = try l.equal(o, try l.t.intern(.isaOfClass(i, term)), definiens)
    let proof = try l.t.intern(.isaDefinition("IFOL.term_class_def", of: .ofClass(term), [i], root, args: []))
    let unit = try expanded(l, [Statement(name: "IFOL.term_class_def", root: root, proof: proof)], [definition])
    var m = LogicTable(t: unit.table)
    #expect(unit.statements[0].root == (try m.equal(o, definiens, definiens)))
    #expect(unit.statements[0].proof == (try m.t.intern(.isaReflexive(definiens))))
}

/// A constant Expand owns, with no definition handed: the reader or the pipeline broke its row, and the run stops.
@Test
func aConstantWithNoDefinitionStopsTheRun() throws {
    var l = LogicTable()
    let c = try l.const(.declared("C"), o)
    let not = Constant.defined(Defined(.ifol, "IFOL.Not", .object))
    let notC = try l.const(not, fn(o, o), c)
    #expect(throws: ExpandError.noDefinition(.isaConst(not, fn(o, o), args: [c]))) {
        _ = try run(Expand(), [notC], in: &l.t)
    }
}

/// FOUNDATION S1: `split ≡ λc p. c(p, p)`, declared at `'a`, is a meta-level definition, unfolded as the logic's are:
/// `split(λx y. x ∈ y, A)` at `'a := o` is `A ∈ A`, and a citation of its definition at `[o]` is reflexivity. An
/// object-level ZF constant is Reify's, and Expand leaves it.
@Test
func aZFDefinitionAtTheMetaLevelUnfoldsAsTheLogicsDo() throws {
    var l = LogicTable()
    let F = fn(i, fn(i, o))
    let T = fn(F, fn(i, o))
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, F), args: [try l.bound(0, i), try l.bound(0, i)]))
    let split = try l.definition(
        Defined(.zf, "ZF_Base.split", .meta),
        T,
        axiomTypes: [o],
        try l.lam(F, try l.lam(i, applied)),
    )
    let a = try l.const(.declared("A"), i)
    let member = try l.lam(i, try l.lam(i, try l.mem(try l.bound(1, i), try l.bound(0, i))))
    let used = try l.const(.defined(split.constant), T, member, a)
    let ball = try l.const(
        .defined(Defined(.zf, "ZF_Base.Ball", .object)),
        fn(i, fn(fn(i, o), o)),
        a,
        try l.lam(i, try l.mem(try l.bound(0, i), a)),
    )
    #expect(try run(Expand(), [used, ball], [split], in: &l.t) == [try l.mem(a, a), ball])

    let c = try l.t.intern(.isaVarApp(head: try l.bound(3, F), args: [try l.bound(1, i), try l.bound(0, i)]))
    let eta = try l.lam(
        F,
        try l.lam(i, try l.const(.defined(split.constant), T, try l.lam(i, try l.lam(i, c)), try l.bound(0, i))),
    )
    let root = try l.equal(T, eta, split.definiens)
    let proof = try l.t.intern(.isaDefinition("ZF_Base.split_def_raw", of: split.defines, [o], root, args: []))
    let unit = try expanded(l, [Statement(name: "ZF_Base.split_def", root: root, proof: proof)], [split])
    var m = LogicTable(t: unit.table)
    #expect(unit.statements[0].root == (try m.equal(T, split.definiens, split.definiens)))
    #expect(unit.statements[0].proof == (try m.t.intern(.isaReflexive(split.definiens))))
}

private let takesAFunction = fn(fn(i, o), o)

/// `λP. c(λz. P z)`, the constant `c` at `(i ⇒ o) ⇒ o` read η-long.
private func etaConstant(_ name: String, _ l: inout LogicTable) throws -> NodeID {
    let atZ = try l.t.intern(.isaVarApp(head: try l.bound(1, fn(i, o)), args: [try l.bound(0, i)]))
    return try l.lam(fn(i, o), try l.const(.declared(name), takesAFunction, try l.lam(i, atZ)))
}

/// `λP. f(λz. P z)`, the variable `f` at `(i ⇒ o) ⇒ o`, `k` binders out, read η-long.
private func etaVariable(_ k: Int, _ l: inout LogicTable) throws -> NodeID {
    let atZ = try l.t.intern(.isaVarApp(head: try l.bound(1, fn(i, o)), args: [try l.bound(0, i)]))
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(k + 1, takesAFunction), args: [try l.lam(i, atZ)]))
    return try l.lam(fn(i, o), applied)
}

/// `λP. c(P)`, the constant `c` at `o ⇒ o` read η-long.
private func connective(_ name: String, _ l: inout LogicTable) throws -> NodeID {
    try l.lam(o, try l.const(.declared(name), fn(o, o), try l.bound(0, o)))
}

/// `λP. f(P)`, the variable `f` at `o ⇒ o`, `k` binders out, read η-long.
private func connectiveVariable(_ k: Int, _ l: inout LogicTable) throws -> NodeID {
    try l.lam(o, try l.t.intern(.isaVarApp(head: try l.bound(k + 1, fn(o, o)), args: [try l.bound(0, o)])))
}

/// `≡`'s congruence at `T`, the definition command's rewriting under `h : c ≡ e`:
/// `combination (combination (reflexive (λf g. f ≡ g)) h) (reflexive d)` is Logic's, read whole from its head, and
/// Expand leaves it. `symmetric` at `T ⇒ o` is Expand's: of `(λg. c ≡ g) ≡ (λg. c ≡ g)` it is `reflexive`, of
/// `(λg. c ≡ g) ≡ (λg. e ≡ g)` it has no reading.
private func onlySymmetryIsExpands(
    _ T: IRType,
    constant: (String, inout LogicTable) throws -> NodeID,
    variable: (Int, inout LogicTable) throws -> NodeID,
) throws {
    var l = LogicTable()
    let c = try constant("c", &l)
    let d = try constant("d", &l)
    let e = try constant("e", &l)
    let equality = try l.lam(T, try l.lam(T, try l.equal(T, try variable(1, &l), try variable(0, &l))))
    let ce = try l.equal(T, c, e)
    let inner = try l.t.intern(.isaCombination(
        fn(T, fn(T, o)),
        try l.t.intern(.isaReflexive(equality)),
        try l.t.intern(.hyp(0, ce)),
    ))
    let outer = try l.t.intern(.isaCombination(fn(T, o), inner, try l.t.intern(.isaReflexive(d))))
    #expect(try run(Expand(), [outer], in: &l.t) == [outer])
    let u = try l.lam(T, try l.equal(T, c, try variable(0, &l)))
    let w = try l.lam(T, try l.equal(T, e, try variable(0, &l)))
    let same = try l.t.intern(.isaSymmetric(fn(T, o), try l.t.intern(.hyp(0, try l.equal(fn(T, o), u, u)))))
    #expect(try run(Expand(), [same], in: &l.t) == [try l.t.intern(.isaReflexive(u))])
    let apart = try l.t.intern(.isaSymmetric(fn(T, o), try l.t.intern(.hyp(0, try l.equal(fn(T, o), u, w)))))
    #expect(throws: ExpandError.noReading(l.t[apart])) { _ = try run(Expand(), [apart], in: &l.t) }
}

/// At a type taking a function, `T = (i ⇒ o) ⇒ o`.
@Test
func atATypeTakingAFunctionCombinationIsLogicsAndSymmetryReflexivity() throws {
    try onlySymmetryIsExpands(takesAFunction, constant: etaConstant, variable: etaVariable)
}

/// At a type taking a proposition, `T = o ⇒ o`: the definition command's rewriting at a connective.
@Test
func atATypeTakingAPropositionCombinationIsLogicsAndSymmetryReflexivity() throws {
    try onlySymmetryIsExpands(fn(o, o), constant: connective, variable: connectiveVariable)
}
