import Testing
import IR
import Lowering

private let i = IRType.i
private let o = IRType.o
private let a = IRType.variable("'a")
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }

private let oo = IRType.fn(.o, .o)

private func fixture() throws -> [Pass] {
    var t = Table()
    return plan(try base(in: &t))
}

private func owners(_ p: Pattern) throws -> [String] { try fixture().filter { $0.owns(p) != nil }.map(\.name) }

/// The unit's table holds base's schemas, parsed before the pipeline runs, as `lower` parses them.
private func lowered(_ t: Table, _ statements: [Statement]) throws -> Unit {
    var t = t
    let b = try base(in: &t)
    var unit = Unit(table: t, statements: statements)
    try pipeline(b).run(&unit)
    return unit
}

/// Reify is no pass: its code is called in logic's walk, and the registry proves between logic and fol.
@Test func thePlanIsTheDesignsOrder() throws {
    var t = Table()
    let b = try base(in: &t)
    #expect(plan(b).map(\.name) == ["expand", "logic", "fol"])
    #expect(pipeline(b).passes.map(\.name) == plan(b).map(\.name))
    #expect(pipeline(b).provingAfter == "logic")
}

/// Reify has no pass: the logic pass owns its pieces as Reify's own switch answers them, and Reify's switch claims none of
/// Logic's.
@Test func reifysPiecesAreTheLogicPasss() throws {
    var t = Table()
    let b = try base(in: &t)
    let reifys: [Pattern] = [
        .isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [i, i]),
        .isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [i, i]),
        .isaConst(.defined(.zf, .object), fn(i, i), args: [i]),
        .isaVarApp(head: fn(i, o), args: [i]),
        .isaAbs(i, body: o),
    ]
    let logics: [Pattern] = [
        .isaCombination(oo, o, o),
        .isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [fn(i, i), fn(i, i)]),
        .isaAllElim(o, o),
        .isaAbs(o, body: o),
    ]
    for p in reifys {
        #expect(try owners(p) == ["logic"], "\(p)")
        #expect(Reify().owns(p) == .rule && Logic(base: b).owns(p) == .rule, "\(p)")
    }
    for p in logics { #expect(Reify().owns(p) == nil, "\(p)") }
}

/// DESIGN §4a, "Lowering's components" and "Logic": each of the reader's patterns has the owner the division gives it,
/// and one at most. A pattern at a type variable, the hidden variable and a citation fol-zfc lacks have none yet; a
/// binder, its intro and its variable at `o` are fol-zfc's schema letter, no pass's.
@Test func eachPatternHasTheOwnerTheDivisionGivesIt() throws {
    let expected: [(Pattern, String?, Owned?)] = [
        (.isaConst(.defined(.ifol, .object), fn(o, fn(o, o)), args: [o, o]), "expand", .rule),
        (.isaConst(.defined(.pure, .meta), fn(o, o), args: [o]), "expand", .rule),
        (.use(.isaDefinition(.fol, .object), [], o), "expand", .rule),
        (.isaConst(.defined(.zf, .meta), fn(fn(i, fn(i, o)), fn(i, o)), args: [fn(i, fn(i, o)), i]), "expand", .rule),
        (.use(.isaDefinition(.zf, .meta), [o], o), "expand", .rule),
        (.use(.axiom(.ifol(.conjI)), [], o), "logic", .rule),
        (.use(.axiom(.fol(.classical)), [], o), "logic", .rule),
        (.isaAllElim(o, o), "logic", .rule),
        (.isaReflexive(o), "logic", .rule),
        (.isaReflexive(oo), "logic", .rule),
        (.isaReflexive(fn(o, oo)), "logic", .rule),
        (.isaSymmetric(o, o), "logic", .rule),
        (.isaSymmetric(oo, o), "logic", .rule),
        (.isaTransitive(o, o, o), "logic", .rule),
        (.isaTransitive(oo, o, o), "logic", .rule),
        (.isaCombination(oo, o, o), "logic", .rule),
        (.isaCombination(fn(o, oo), o, o), "logic", .rule),
        (.isaAbs(o, body: o), "logic", .rule),
        (.isaReflexive(i), "logic", .unbuilt),
        (.isaReflexive(fn(i, i)), "logic", .unbuilt),
        (.isaSymmetric(i, o), "logic", .unbuilt),
        (.isaTransitive(fn(i, o), o, o), "logic", .unbuilt),
        (.isaCombination(fn(i, o), o, o), "logic", .unbuilt),
        (.isaCombination(fn(oo, o), o, o), "logic", .unbuilt),
        (.isaAbstract(fn(i, o), o), "logic", .unbuilt),
        (.isaAbstract(oo, o), "logic", .unbuilt),
        (.isaAbs(fn(i, o), body: o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.spec)), [i], o), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [fn(i, i), fn(i, i)]), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(o, o), fn(fn(o, o), o)), args: [fn(o, o), fn(o, o)]), "logic", .unbuilt),
        (.isaReflexive(a), nil, nil),
        (.ifolAll(fn(o, o), body: o), "logic", .unbuilt),
        (.isaAllElim(o, fn(o, o)), "logic", .unbuilt),
        (.isaAllElim(o, fn(i, fn(i, i))), "logic", .unbuilt),
        (.isaAllElim(o, fn(i, o)), "logic", .unbuilt),
        (.ifolAll(o, body: o), nil, nil),
        (.isaAllIntro(o, body: o), nil, nil),
        (.isaBound(o), nil, nil),
        (.ifolEx(o, body: o), nil, nil),
        (.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [i, i]), "logic", .rule),
        (.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [i, i]), "logic", .rule),
        (.isaConst(.primitive(.zf(.zero)), i, args: []), "logic", .rule),
        (.isaConst(.primitive(.zf(.primReplace)), fn(i, fn(fn(i, fn(i, o)), i)), args: [i, fn(i, fn(i, o))]), "logic", .rule),
        (.isaConst(.defined(.zf, .object), fn(i, i), args: [i]), "logic", .rule),
        (.isaConst(.defined(.zf, .object), i, args: []), "logic", .rule),
        (.isaConst(.defined(.zf, .object), fn(i, o), args: [i]), "logic", .rule),
        (.isaConst(.defined(.zf, .object), fn(fn(i, o), i), args: [fn(i, o)]), "logic", .rule),
        (.isaConst(.defined(.zf, .object), o, args: []), "logic", .unbuilt),
        (.isaConst(.defined(.zf, .object), fn(o, fn(i, fn(i, i))), args: [o, i, i]), "logic", .unbuilt),
        (.isaConst(.declared, i, args: []), "logic", .unbuilt),
        (.isaVarApp(head: fn(i, o), args: [i]), "logic", .rule),
        (.isaVarApp(head: fn(i, i), args: [i]), "logic", .rule),
        (.isaVarApp(head: fn(o, o), args: [o]), "logic", .unbuilt),
        (.isaAbs(i, body: o), "logic", .rule),
        (.isaAbs(i, body: fn(i, o)), "logic", .rule),
        (.isaAbs(i, body: i), "logic", .rule),
        (.isaAbs(a, body: o), nil, nil),
        (.ifolAll(i, body: o), "fol", .rule),
        (.ifolEx(i, body: o), "fol", .rule),
        (.isaAllIntro(i, body: o), "fol", .rule),
        (.isaAllElim(o, i), "fol", .rule),
        (.ifolAll(fn(i, o), body: o), "fol", .rule),
        (.ifolAll(fn(i, i), body: o), "fol", .rule),
        (.isaAllIntro(fn(i, fn(i, i)), body: o), "fol", .rule),
        (.isaBound(i), "fol", .rule),
        (.isaBound(fn(i, o)), "fol", .rule),
        (.isaBound(fn(i, i)), "fol", .rule),
        (.isaBound(fn(fn(i, o), o)), "fol", .unbuilt),
        (.isaBound(fn(o, o)), "fol", .unbuilt),
        (.isaGuard(i, o), "fol", .rule),
        (.isaGuard(fn(i, i), o), "fol", .rule),
        (.isaExIntro(o, i), "fol", .rule),
        (.isaExElim(i, o, body: o), "fol", .rule),
        (.use(.lemma, [], o), nil, nil),
        (.folImplies(o, o), nil, nil),
        (.hyp(o), nil, nil),
        (.use(.theorem, [], o), nil, nil),
        (.ifolAll(a, body: o), nil, nil),
        (.isaBound(a), nil, nil),
        (.isaConst(.defined(.zf, .object), fn(a, a), args: [a]), nil, nil),
        (.isaConst(.defined(.zf, .meta), fn(a, a), args: [a]), nil, nil),
        (.use(.axiom(.ifol(.refl)), [a], o), nil, nil),
        (.isaOfClass(i), nil, nil),
        (.isaFree(i), nil, nil),
        (.use(.theorem, [i], o), nil, nil),
        (.use(.axiom(.zf(.replacement)), [], o), nil, nil),
        (.use(.theoryAxiom, [], o), nil, nil),
        (.use(.isaDefinition(.zf, .object), [], o), nil, nil),
    ]
    for (p, owner, owned) in expected {
        #expect(try owners(p) == (owner.map { [$0] } ?? []), "\(p)")
        #expect(try fixture().compactMap { $0.owns(p) }.first == owned, "\(p)")
    }
}

/// `⋀x. ⊥ ⟶ ⊥`: expand and logic own nothing in it, and Fol writes its binder as fol-zfc's, guarded.
@Test func aStatementOfABinderAtIAloneReachesFolZfc() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let root = try t.intern(.ifolAll(i, body: try t.intern(.folImplies(bottom, bottom))))
    let proof = try t.intern(.isaAllIntro(i, body: try t.intern(.folImpliesIntro(bottom, body: try t.intern(.hyp(0, bottom))))))
    var unit = try lowered(t, [Statement(name: "thm", root: root, proof: proof)])
    let set = try unit.table.intern(.folPred(.base("set"), args: [try unit.table.intern(.folBound(0))]))
    let guarded = try unit.table.intern(.folForall(body: try unit.table.intern(.folImplies(set, try unit.table.intern(.folImplies(bottom, bottom))))))
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.root) == [guarded])
}

private func compoundElimination(_ t: inout Table) throws -> [Statement] {
    let memT = fn(i, fn(i, o))
    let x = try t.intern(.isaBound(0, i))
    let selfMember = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, x]))
    let lemRoot = try t.intern(.ifolAll(i, body: try t.intern(.folImplies(selfMember, selfMember))))
    let lem = Statement(name: "lem", root: lemRoot, proof: try t.intern(.isaAllIntro(i, body: try t.intern(
        .folImpliesIntro(selfMember, body: try t.intern(.hyp(0, selfMember)))))))
    let pow = try t.intern(.isaConst(.primitive(.zf(.pow)), fn(i, i), args: [try t.intern(.isaConst(.primitive(.zf(.zero)), i, args: []))]))
    let atPow = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [pow, pow]))
    let proof = try t.intern(.isaAllElim(try t.intern(.use(.theorem("lem"), [], lemRoot)), pow))
    return [lem, Statement(name: "thm", root: try t.intern(.folImplies(atPow, atPow)), proof: proof)]
}

/// `lem : ⋀x. x ∈ x ⟶ x ∈ x` at `Pow(0)`: the logic pass proves the instance, citing EX and UNIQ of `Pow(0)`, both proved —
/// UNIQ by `Pow`'s facts from base, EX by `Pow`'s class — and the statement lowers. The cited theorem is lowered whole.
@Test func anEliminationAtACompoundTermCitesItsTermsLemmas() throws {
    var t = Table()
    let statements = try compoundElimination(&t)
    let unit = try lowered(t, statements)
    #expect(unit.refused.isEmpty)
    let kept = Set(unit.statements.map(\.name))
    #expect(kept.isSuperset(of: ["lem", "thm", "ZF_Base.Pow_CLASS", "ZF_Base.Pow_AGREE", "ZF_Base.Pow_FUNC", "ZF_Base.Pow_TOTAL",
                                 "TUPLE_UNIQ_1", "TUPLE_INJ_1"]))
    #expect(kept.contains { $0.hasPrefix("UNIQ_") } && kept.contains { $0.hasPrefix("EX_") })
}

private struct Unbuilt: Prover {
    let name = "unbuilt"
    func owns(_ l: Lemma) -> Owned? { l.name.hasSuffix("_CLASS") ? .unbuilt : nil }
    func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID { statement }
    func defines(_ c: Defined) -> Owned? { nil }
    func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID { try t.intern(.folBottom) }
}

/// The same, a registry answering class existence unbuilt: `Pow`'s class is refused at the registry, EX citing it falls,
/// and the statement with it; what it does not cite stays.
@Test func aStatementFallsWithAnUnbuiltLemmaItsProofCites() throws {
    var t = Table()
    let b = try base(in: &t)
    let statements = try compoundElimination(&t)
    var unit = Unit(table: t, statements: statements)
    let registry = Provers([ReifyProver(base: b), TupleProver(base: b), Unbuilt()])
    try Pipeline(passes: plan(b), registry: registry, provingAfter: "logic").run(&unit)
    let refused = Dictionary(uniqueKeysWithValues: unit.refused.map { ($0.name, $0.refusal) })
    let ex = try #require(refused.keys.first { $0.hasPrefix("EX_") })
    #expect(refused.count == 3)
    #expect(refused["ZF_Base.Pow_CLASS"] == .lemmaUnbuilt)
    #expect(refused[ex] == .cites("ZF_Base.Pow_CLASS"))
    #expect(refused["thm"] == .cites(ex))
    let kept = Set(unit.statements.map(\.name))
    #expect(kept.isSuperset(of: ["lem", "ZF_Base.Pow_AGREE", "ZF_Base.Pow_FUNC", "ZF_Base.Pow_TOTAL", "TUPLE_UNIQ_1", "TUPLE_INJ_1"]))
    #expect(kept.contains { $0.hasPrefix("UNIQ_") })
}

/// An elimination at the reader's hidden variable: no pass owns it yet, so the statement stops before the first.
@Test func aPatternNoPassOwnsStopsTheStatementBeforeThePlan() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let root = try t.intern(.folImplies(bottom, bottom))
    let hidden = try t.intern(.isaFree(.hidden, i))
    let proof = try t.intern(.isaAllElim(try t.intern(.use(.theorem("lem"), [], try t.intern(.ifolAll(i, body: root)))), hidden))
    let unit = try lowered(t, [Statement(name: "thm", root: root, proof: proof)])
    #expect(unit.refused.map(\.refusal) == [.noOwner([.isaFree(i)])])
}

/// `¬⊥ ⟹ ¬⊥` by its hypothesis: once Expand unfolds `¬`, nothing is left that fol-zfc lacks, and the plan lowers it
/// whole.
@Test func aStatementWhoseOnlyIsaPieceIsALogicConstantIsLoweredWhole() throws {
    var l = LogicTable()
    let not = try l.not()
    let bottom = try l.bottom()
    let notBottom = try l.const(.defined(not.constant), fn(o, o), bottom)
    let proof = try l.t.intern(.folImpliesIntro(notBottom, body: try l.t.intern(.hyp(0, notBottom))))
    let statement = Statement(name: "thm", root: try l.imp(notBottom, notBottom), proof: proof)
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [statement], definitions: [not])
    try pipeline(b).run(&unit)
    let unfolded = try unit.table.intern(.folImplies(bottom, bottom))
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.root) == [try unit.table.intern(.folImplies(unfolded, unfolded))])
}

/// `T.d ≡ λx. ¬(x ∈ x)` is Reify's: it passes Expand, which unfolds its `¬`, and reaches the logic pass so.
@Test func aDefinitionOwnedByALaterPassReachesItUnfolded() throws {
    var l = LogicTable()
    let not = try l.not()
    let x = try l.bound(0, i)
    let member = try l.mem(x, x)
    let d = try l.definition(Defined(.zf, "T.d", .object), fn(i, o), try l.lam(i, try l.const(.defined(not.constant), fn(o, o), member)))
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [], definitions: [not, d])
    try pipeline(b).run(&unit)
    var reached = d
    reached.definiens = try unit.table.intern(.isaAbs(i, body: try unit.table.intern(.folImplies(member, try unit.table.intern(.folBottom)))))
    #expect(unit.definitions == [not, reached])
}

/// `IFOL.conjI`, the theorem: `⋀P Q. P ⟹ Q ⟹ P ∧ Q`, proved by the axiom at its own letters. Logic makes its proof the
/// kernel's `and_intro` over the letters, and the plan keeps it whole: a schema.
@Test func theLogicsOwnTheoremIsLoweredAsASchemaProvedByTheKernelsStep() throws {
    var t = Table()
    let p = try t.intern(.isaBound(1, o)), q = try t.intern(.isaBound(0, o))
    let body = try t.intern(.folImplies(p, try t.intern(.folImplies(q, try t.intern(.folAnd(p, q))))))
    let root = try t.intern(.ifolAll(o, body: try t.intern(.ifolAll(o, body: body))))
    let axiom = try t.intern(.use(.axiom(.ifol(.conjI)), [], root))
    let instance = try t.intern(.isaAllElim(try t.intern(.isaAllElim(axiom, p)), q))
    let proof = try t.intern(.isaAllIntro(o, body: try t.intern(.isaAllIntro(o, body: instance))))
    var unit = try lowered(t, [Statement(name: "IFOL.conjI", root: root, proof: proof)])
    let both = try unit.table.intern(.folAndIntro(try unit.table.intern(.hyp(1, p)), try unit.table.intern(.hyp(0, q))))
    let kernel = try unit.table.intern(.folImpliesIntro(p, body: try unit.table.intern(.folImpliesIntro(q, body: both))))
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.root) == [root])
    #expect(unit.statements.map(\.proof) == [try unit.table.intern(.isaAllIntro(o, body: try unit.table.intern(.isaAllIntro(o, body: kernel))))])
}

/// `⋀Q. Q ⟹ Q`, proved by instantiating the schema `id : ⋀P. P ⟹ P` at its own letter: `schema_inst` on a citation,
/// both lowered whole.
@Test func aSchemaAndAStatementInstantiatingItAreLoweredWhole() throws {
    var t = Table()
    let p = try t.intern(.isaBound(0, o))
    let root = try t.intern(.ifolAll(o, body: try t.intern(.folImplies(p, p))))
    let id = Statement(name: "id", root: root, proof: try t.intern(.isaAllIntro(o, body: try t.intern(
        .folImpliesIntro(p, body: try t.intern(.hyp(0, p)))))))
    let cited = try t.intern(.use(.theorem("id"), [], root))
    let user = Statement(name: "user", root: root, proof: try t.intern(.isaAllIntro(o, body: try t.intern(.isaAllElim(cited, p)))))
    var unit = try lowered(t, [id, user])
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["id", "user"])
    #expect(unit.statements[1].proof == (try unit.table.intern(.isaAllIntro(o, body: try unit.table.intern(.folSchemaInst(cited, p))))))
}

/// The simplifier's rewrite, `⋀A B. (A ↔ B) ⟹ B ⟹ A` by `equal_elim (symmetric (combination (reflexive Trueprop) q))
/// fact`, as the reader reads it: Logic makes it base's `iff_symm` at the identity's congruence, and the plan keeps it
/// whole.
@Test func theSimplifiersRewriteIsLoweredWhole() throws {
    var t = Table()
    let (A, B) = (try t.intern(.isaBound(1, o)), try t.intern(.isaBound(0, o)))
    let AB = try t.intern(.folIff(A, B))
    let identity = try t.intern(.isaAbs(o, body: try t.intern(.isaBound(0, o))))
    let combined = try t.intern(.isaCombination(oo, try t.intern(.isaReflexive(identity)), try t.intern(.hyp(1, AB))))
    let body = try t.intern(.folIffElimL(try t.intern(.isaSymmetric(o, combined)), try t.intern(.hyp(0, B))))
    let proof = try t.intern(.isaAllIntro(o, body: try t.intern(.isaAllIntro(o, body: try t.intern(.folImpliesIntro(AB,
        body: try t.intern(.folImpliesIntro(B, body: body))))))))
    let root = try t.intern(.ifolAll(o, body: try t.intern(.ifolAll(o, body: try t.intern(.folImplies(AB, try t.intern(.folImplies(B, A))))))))
    let unit = try lowered(t, [Statement(name: "T.rewrite", root: root, proof: proof)])
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["T.rewrite"])
}

/// `¬A ⟹ (A ⟶ ⊥)` unfolded by `combination (not_def) (reflexive A)`: the citation's statement is an equation between
/// functions of propositions, which no rule translates, yet it reaches Expand, which makes it the `reflexive` step at
/// the definiens, and Logic lowers the congruence.
@Test func aDefinitionsCitationAtAFunctionOfPropositionsIsLoweredWhole() throws {
    var l = LogicTable()
    let not = try l.not()
    let a = try l.bound(0, o)
    let eta = try l.lam(o, try l.const(.defined(not.constant), oo, try l.bound(0, o)))
    let cited = try l.t.intern(.use(.isaDefinition("IFOL.not_def_raw", of: not.constant), [], try l.equal(oo, eta, not.definiens)))
    let notA = try l.const(.defined(not.constant), oo, a)
    let unfolded = try l.imp(a, try l.bottom())
    let combined = try l.t.intern(.isaCombination(oo, cited, try l.t.intern(.isaReflexive(a))))
    let body = try l.t.intern(.folImpliesIntro(notA, body: try l.t.intern(.folIffElimL(combined, try l.t.intern(.hyp(0, notA))))))
    let statement = Statement(name: "T.notE", root: try l.all(o, try l.imp(notA, unfolded)),
                              proof: try l.t.intern(.isaAllIntro(o, body: body)))
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [statement], definitions: [not])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["T.notE"])
}

/// `⋀x. T.d(x) ⟶ T.d(x)`, `T.d ≡ λx. x ∈ x`: the logic pass names `T.d(x)` by `T.d`'s class, the registry states the
/// class's `@def` from the definition, and the unit holds both, linked.
@Test func aStatementNamingAConstantIsLoweredWithTheConstantsDefinition() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let d = try l.definition(Defined(.zf, "T.d", .object), fn(i, o), try l.lam(i, try l.mem(x, x)))
    let atom = try l.const(.defined(d.constant), fn(i, o), x)
    let proof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.folImpliesIntro(atom, body: try l.t.intern(.hyp(0, atom))))))
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [Statement(name: "thm", root: try l.all(i, try l.imp(atom, atom)), proof: proof)],
                    definitions: [d])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["thm", "T.d_DEF"])
    #expect(unit.statements.last?.defines == d.constant)
}

/// `T.e ≡ λx. x ∈ a`, `a` a declared constant: no `@def` names it, so the `@def` is refused at the logic pass, and the
/// statement naming `T.e` with it.
@Test func aDefinitionHoldingAPieceNotBuiltRefusesItsUsers() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let declared = try l.const(.declared("T.a"), i)
    let e = try l.definition(Defined(.zf, "T.e", .object), fn(i, o), try l.lam(i, try l.mem(x, declared)))
    let atom = try l.const(.defined(e.constant), fn(i, o), x)
    let proof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.folImpliesIntro(atom, body: try l.t.intern(.hyp(0, atom))))))
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [Statement(name: "thm", root: try l.all(i, try l.imp(atom, atom)), proof: proof)],
                    definitions: [e])
    try pipeline(b).run(&unit)
    #expect(unit.statements.isEmpty)
    #expect(unit.refused.map(\.name) == ["T.e_DEF", "thm"])
    #expect(unit.refused.map(\.refusal) == [.unbuilt(pass: "logic", [.isaConst(.declared, i, args: [])]), .cites("T.e_DEF")])
}

/// `T.ball ≡ λA P. ∀x. x ∈ A ⟶ P(x)`: the abstraction over the class parameter `P` is the `@def`'s own variable, no λ
/// of its body, so the `@def` is stated and `⋀A. T.ball(A, λx. x ∈ A) ⟶ T.ball(A, λx. x ∈ A)` lowered with it.
@Test func aDefinitionsClassParameterIsItsDefinitionsVariable() throws {
    var l = LogicTable()
    let P = fn(i, o), x = try l.bound(0, i)
    let applied = try l.t.intern(.isaVarApp(head: try l.bound(1, P), args: [x]))
    let ball = try l.definition(Defined(.zf, "T.ball", .object), fn(i, fn(P, o)),
                                try l.lam(i, try l.lam(P, try l.all(i, try l.imp(try l.mem(x, try l.bound(2, i)), applied)))))
    let lambda = try l.lam(i, try l.mem(try l.bound(0, i), try l.bound(1, i)))
    let atom = try l.const(.defined(ball.constant), fn(i, fn(P, o)), try l.bound(0, i), lambda)
    let proof = try l.t.intern(.isaAllIntro(i, body: try l.t.intern(.folImpliesIntro(atom, body: try l.t.intern(.hyp(0, atom))))))
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [Statement(name: "thm", root: try l.all(i, try l.imp(atom, atom)), proof: proof)],
                    definitions: [ball])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["thm", "T.ball_DEF"])
}
