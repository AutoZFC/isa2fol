import IR
import Testing
@testable import Lowering

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private let when = Defined(.zf, "T.when", .object)
private let selectConstant = Defined(.zf, "T.select", .object)
private let pick = Defined(.zf, "T.pick", .object)
private let replaceType = fn(i, fn(fn(i, fn(i, o)), i))

/// DESIGN "Step 6": a proposition as an argument, its truth set an entry of the argument tuple.
private struct Q {
    var t = Table()

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func x(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, i))
    }

    mutating func v(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, o))
    }

    mutating func c(_ k: Int) throws -> NodeID {
        try n(.folBound(k))
    }

    mutating func p(_ name: String, _ xs: NodeID...) throws -> NodeID {
        try n(.folPred(.base(name), args: xs))
    }

    mutating func k(_ c: Defined, _ xs: NodeID...) throws -> NodeID {
        try n(.folPred(.constant(.defined(c)), args: xs))
    }

    mutating func and(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folAnd(a, b))
    }

    mutating func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folIff(a, b))
    }

    mutating func some(_ body: NodeID) throws -> NodeID {
        try n(.ifolEx(i, body: body))
    }

    mutating func every(_ body: NodeID) throws -> NodeID {
        try n(.ifolAll(i, body: body))
    }

    mutating func lam(_ T: IRType, _ body: NodeID) throws -> NodeID {
        try n(.isaAbs(T, body: body))
    }

    mutating func mem(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [a, b]))
    }

    mutating func eq(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [a, b]))
    }

    mutating func pow(_ a: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.pow)), fn(i, i), args: [a]))
    }

    mutating func applied(_ c: Defined, _ T: IRType, _ xs: NodeID...) throws -> NodeID {
        try n(.isaConst(.defined(c), T, args: xs))
    }

    /// `⟨a, b⟩ = τ`, each at the index it stands at outside the tuple's three binders.
    mutating func pair(_ a: Int, _ b: Int, _ tau: Int) throws -> NodeID {
        try some(try and(try p("zero", try x(0)), try some(try and(
            try p("nsucc", try x(1), try x(0)),
            try some(try and(
                try p("snoc", try x(2), try x(2), try x(a + 3), try x(0)),
                try p("snoc", try x(0), try x(1), try x(b + 3), try x(tau + 3)),
            )),
        ))))
    }

    func definition(_ c: Defined, _ T: IRType, _ definiens: NodeID) -> Definition {
        Definition(defines: .constant(c), type: T, axiomTypes: [], parameters: 0, definiens: definiens)
    }

    /// `T.when ≡ λP a. P ∧ a ∈ a`: a predicate taking a proposition.
    mutating func whenDefinition() throws -> Definition {
        definition(when, fn(o, fn(i, o)), try lam(o, try lam(i, try and(try v(1), try mem(try x(0), try x(0))))))
    }

    /// `T.select ≡ λP a. PrimReplace(a, λx y. P ∧ x = y)`: `a` where `P`, `0` where not.
    mutating func selectDefinition() throws -> Definition {
        let chosen = try lam(i, try lam(i, try and(try v(3), try eq(try x(1), try x(0)))))
        let body = try n(.isaConst(.primitive(.zf(.primReplace)), replaceType, args: [try x(0), chosen]))
        return definition(selectConstant, fn(o, fn(i, i)), try lam(o, try lam(i, body)))
    }

    /// `T.pick ≡ λP a. Pow(a)`: a function taking a proposition it does not read.
    mutating func pickDefinition() throws -> Definition {
        definition(pick, fn(o, fn(i, i)), try lam(o, try lam(i, try pow(try x(0)))))
    }

    /// `λP a. c(P, a)`, η-long at `o ⇒ i ⇒ T`.
    mutating func eta(_ c: Defined, _ T: IRType) throws -> NodeID {
        try lam(o, try lam(i, try applied(c, fn(o, fn(i, T)), try v(1), try x(0))))
    }
}

/// `y ∈ T.select(z ∈ z, z)`: the proposition named first, a set `E` with `truth(E) ∧ (holds(E) ↔ z ∈ z)`, then the
/// constant's class, the tuple `⟨E, z⟩` and its value, by ID.
@Test
func aPropositionArgumentIsNamedByItsTruthSetAnEntryOfItsTuple() throws {
    var q = Q()
    let b = try base(in: &q.t)
    let term = try q.applied(selectConstant, fn(o, fn(i, i)), try q.mem(try q.x(0), try q.x(0)), try q.x(0))
    let out = try Logic(base: b).run([try q.mem(try q.x(1), term)], [], in: &q.t)
    let truthSet = try q.and(
        try q.p("truth", try q.x(0)),
        try q.iff(try q.p("holds", try q.x(0)), try q.p("elem", try q.x(1), try q.x(1))),
    )
    let value = try q.some(try q.and(
        try q.p("pmem", try q.x(1), try q.x(0), try q.c(2)),
        try q.p("elem", try q.x(5), try q.x(0)),
    ))
    let named = try q.some(try q.and(truthSet, try q.n(.folExists(body: try q.and(
        try q.k(selectConstant, try q.c(0)),
        try q.some(try q.and(try q.pair(2, 3, 0), value)),
    )))))
    #expect(out == [named])
}

/// `T.when ≡ λP a. P ∧ a ∈ a`: its class is over the tuples `⟨E, a⟩`, its proposition read `holds(E)` at its entry.
@Test
func aConstantTakingAPropositionReadsItAtItsEntry() throws {
    var q = Q()
    let b = try base(in: &q.t)
    let d = try q.whenDefinition()
    let stated = try ReifyProver(base: b).define(when, [d], in: &q.t)
    let member = try q.and(try q.p("holds", try q.x(1)), try q.p("elem", try q.x(0), try q.x(0)))
    let body = try q.every(try q.iff(
        try q.p("elem", try q.x(0), try q.c(1)),
        try q.some(try q.some(try q.and(try q.pair(1, 0, 2), member))),
    ))
    #expect(stated == (try q.n(.folForall(body: try q.iff(try q.k(when, try q.c(0)), body)))))
}

/// `T.select(z ∈ z, z)`: EX by base's `truth_set_EX`, UNIQ by `truth_UNIQ`, the constant's facts over tuples whose
/// first entry is a truth set — proved to the end, nothing unbuilt, and the kernel checks each.
@Test
func exAndUniqOfAConstantTakingAPropositionAreProvedToTheEnd() throws {
    var q = Q()
    let d = try q.selectDefinition()
    let term = try q.applied(selectConstant, fn(o, fn(i, i)), try q.mem(try q.x(0), try q.x(0)), try q.x(0))
    var r = Terms(t: q.t)
    let (proved, unbuilt) = try proveAll(try r.requests(term), [d], in: &r.t)
    let names = Set(proved.map(\.name))
    #expect(names.isSuperset(of: ["T.select_CLASS", "T.select_TOTAL", "T.select_AGREE", "T.select_FUNC"]))
    #expect(names.contains { $0.hasPrefix("EX_") } && names.contains { $0.hasPrefix("UNIQ_") })
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, definitions: [(selectConstant, try atDefinition(selectConstant, [d], in: &r.t))], in: &r.t)
}

/// `T.wrap ≡ λa. T.select(a ∈ Pow(a), a)`, as `natify` holds `if a = succ(pred(a)) then …`: the class prover reads the
/// truth set's proposition from its own formula, `Pow`'s class among its pieces, and the kernel checks EX and UNIQ.
@Test
func aDefinitionApplyingAConstantToAPropositionHoldingATermHasItsClass() throws {
    var q = Q()
    let select = try q.selectDefinition()
    let wrap = Defined(.zf, "T.wrap", .object)
    let inner = try q.applied(
        selectConstant,
        fn(o, fn(i, i)),
        try q.mem(try q.x(0), try q.pow(try q.x(0))),
        try q.x(0),
    )
    let d = q.definition(wrap, fn(i, i), try q.lam(i, inner))
    let term = try q.applied(wrap, fn(i, i), try q.x(0))
    var r = Terms(t: q.t)
    let (proved, unbuilt) = try proveAll(try r.requests(term), [select, d], in: &r.t)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["T.wrap_CLASS", "T.select_CLASS"]))
    #expect(unbuilt.isEmpty)
    try kernelChecks(
        proved,
        definitions: [
            (selectConstant, try atDefinition(selectConstant, [select, d], in: &r.t)),
            (wrap, try atDefinition(wrap, [select, d], in: &r.t)),
        ],
        in: &r.t,
    )
}

/// `T.select ≡ λP a. …` cited is its unfolding, pointwise over a truth set and an object:
/// `∀E. truth(E) → ∀a. T.select(holds(E), a) = PrimReplace(a, λx y. holds(E) ∧ x = y)`, proved from the `@def`.
@Test
func theUnfoldingOfAConstantTakingAPropositionIsPointwiseOverItsTruthSet() throws {
    var q = Q()
    let d = try q.selectDefinition()
    let b = try base(in: &q.t)
    let eta = try q.eta(selectConstant, i)
    let stated = try walked(try q.t.equation(fn(o, fn(i, i)), eta, d.definiens), base: b, in: &q.t)
    guard
        case .folForall(let guarded) = q.t[stated], case .folImplies(let premise, let rest) = q.t[guarded],
        case .ifolAll(.i, _) = q.t[rest]
    else {
        Issue.record("not pointwise over a truth set and an object: \(q.t[stated])")
        return
    }
    #expect(premise == (try q.p("truth", try q.c(0))))
    let request = Unfolding(constant: selectConstant, statement: stated)
    let (proved, unbuilt) = try proveAll([(Lemma(request), stated)], [d], in: &q.t)
    #expect(Set(proved.map(\.name)).contains("T.select_UNFOLD"))
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, definitions: [(selectConstant, try atDefinition(selectConstant, [d], in: &q.t))], in: &q.t)
}

/// `⋀Q. Q ⟶ (∃x. Q)`, its witness `f(Q)` and `f :: o ⇒ i` a variable only the proof uses: `f` the witness of
/// `function_inhabited`, `f(Q)` its `apply` at `⟨E⟩`, `E` the truth set of `Q`. The kernel proves it.
@Test
func aVariableOnlyTheProofUsesTakingAPropositionIsAClassOfTruthSetTuples() throws {
    var q = Q()
    let b = try base(in: &q.t)
    let root = try q.n(.ifolAll(o, body: try q.n(.folImplies(try q.v(0), try q.n(.ifolEx(i, body: try q.v(1)))))))
    let letter = try q.v(1)
    let witness = try q.n(.isaVarApp(head: try q.n(.isaBound(0, fn(o, i))), args: [letter]))
    let introduced = try q.n(.isaExIntro(try q.n(.hyp(0, letter)), witness, body: try q.v(2)))
    let proof = try q.n(.isaAllIntro(o, body: try q.n(.isaHidden(
        fn(o, i),
        body: try q.n(.folImpliesIntro(letter, body: introduced)),
    ))))
    #expect(q.t.conclusion(of: proof) == root)
    var unit = Unit(table: q.t, statements: [Statement(name: "T.witness", root: root, proof: proof, theory: "Test")])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// Pure's equality at `o ⇒ i ⇒ i`: pointwise over a truth set and an object, `reflexive` and `transitive` under the
/// binders, and `combination` at the proposition its truth instance then β — `⋀A B. (A ↔ B) ⟹ T.pick(A) ≡ T.pick(B)`.
/// The kernel proves the unit.
@Test
func pureEqualityAtAFunctionTakingAPropositionAndAnObjectIsPointwise() throws {
    var q = Q()
    let b = try base(in: &q.t)
    let d = try q.pickDefinition()
    let F = fn(o, fn(i, i))
    let eta = try q.eta(pick, i)
    let same = try q.t.equation(F, eta, eta)
    let read = try Logic(base: b).run([same], [], in: &q.t)[0]
    guard
        case .folForall(let guarded) = q.t[read], case .folImplies(let premise, let rest) = q.t[guarded],
        case .ifolAll(.i, _) = q.t[rest]
    else {
        Issue.record("not pointwise over a truth set and an object: \(q.t[read])")
        return
    }
    #expect(premise == (try q.p("truth", try q.c(0))))
    let reflexive = try q.n(.isaReflexive(eta))
    let transitive = try q.n(.isaTransitive(F, reflexive, reflexive))
    let A = try q.v(1)
    let B = try q.v(0)
    let atA = try q.lam(i, try q.applied(pick, F, try q.v(2), try q.x(0)))
    let atB = try q.lam(i, try q.applied(pick, F, try q.v(1), try q.x(0)))
    let ab = try q.iff(A, B)
    let combined = try q.n(.isaCombination(F, reflexive, try q.n(.hyp(0, ab))))
    let comb = try q.n(.ifolAll(o, body: try q.n(.ifolAll(o, body: try q.n(.folImplies(
        ab,
        try q.t.equation(fn(i, i), atA, atB),
    ))))))
    let combProof = try q.n(.isaAllIntro(o, body: try q.n(.isaAllIntro(o, body: try q.n(.folImpliesIntro(
        ab,
        body: combined,
    ))))))
    #expect(q.t.conclusion(of: combProof) == comb)
    var unit = Unit(table: q.t, statements: [
        Statement(name: "T.refl", root: same, proof: reflexive, theory: "Test"),
        Statement(name: "T.trans", root: same, proof: transitive, theory: "Test"),
        Statement(name: "T.comb", root: comb, proof: combProof, theory: "Test"),
    ], definitions: [d])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
