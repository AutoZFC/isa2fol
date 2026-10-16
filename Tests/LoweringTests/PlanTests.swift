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
/// binder, its intro and its variable at `o` are fol-zfc's schema letter, no pass's; Pure's `⋀` over a proposition is
/// Logic's, a truth set.
@Test func eachPatternHasTheOwnerTheDivisionGivesIt() throws {
    let expected: [(Pattern, String?, Owned?)] = [
        (.isaConst(.defined(.ifol, .object), fn(o, fn(o, o)), args: [o, o]), "expand", .rule),
        (.isaConst(.defined(.pure, .meta), fn(o, o), args: [o]), "expand", .rule),
        (.use(.isaDefinition(.fol, .object), [], o), "expand", .rule),
        (.isaConst(.defined(.zf, .meta), fn(fn(i, fn(i, o)), fn(i, o)), args: [fn(i, fn(i, o)), i]), "expand", .rule),
        (.use(.isaDefinition(.zf, .meta), [o], o), "expand", .rule),
        (.use(.axiom(.ifol(.conjI)), [], o), "logic", .unbuilt),
        (.use(.axiom(.fol(.classical)), [], o), "logic", .unbuilt),
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
        (.isaAbs(o, body: oo), "logic", .rule),
        (.isaAbs(oo, body: o), "logic", .unbuilt),
        (.isaReflexive(i), "logic", .rule),
        (.isaReflexive(fn(i, i)), "logic", .unbuilt),
        (.isaSymmetric(i, o), "logic", .rule),
        (.isaTransitive(i, o, o), "logic", .rule),
        (.isaTransitive(fn(i, o), o, o), "logic", .unbuilt),
        (.isaCombination(fn(i, o), o, o), "logic", .unbuilt),
        (.isaCombination(fn(oo, o), o, o), "logic", .unbuilt),
        (.isaAbstract(fn(i, o), o), "logic", .unbuilt),
        (.isaAbstract(oo, o), "logic", .unbuilt),
        (.isaAbs(fn(i, o), body: o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.spec)), [i], o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.subst)), [i], o), "logic", .rule),
        (.use(.axiom(.ifol(.exE)), [i], o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.refl)), [i], o), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [fn(i, i), fn(i, i)]), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(o, o), fn(fn(o, o), o)), args: [fn(o, o), fn(o, o)]), "logic", .rule),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(oo, o), fn(fn(oo, o), o)), args: [fn(oo, o), fn(oo, o)]), "logic", .unbuilt),
        (.isaReflexive(a), nil, nil),
        (.ifolAll(fn(o, o), body: o), "logic", .unbuilt),
        (.isaAllElim(o, fn(o, o)), "logic", .unbuilt),
        (.isaAllElim(o, fn(i, fn(i, i))), "logic", .unbuilt),
        (.isaAllElim(o, fn(i, o)), "logic", .unbuilt),
        (.ifolAll(o, body: o), nil, nil),
        (.isaAllIntro(o, body: o), nil, nil),
        (.isaBound(o), nil, nil),
        (.isaPropAll, "logic", .rule),
        (.isaPropIntro, "logic", .rule),
        (.isaPropBound, "logic", .rule),
        (.isaBound(oo), "fol", .unbuilt),
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
        (.isaClassical(o, o), "logic", .rule),
        (.isaIffReflection(o, o, o), "logic", .rule),
        (.folAndIntro(o, o), nil, nil),
        (.folOrElim(o, o, o), nil, nil),
        (.folBottomElim(o, o), nil, nil),
        (.isaOfClass(a), nil, nil),
        (.folImpliesIntro(o, body: o), nil, nil),
        (.folImpliesElim(o, o), nil, nil),
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

private struct Q {
    var t = Table()
    let P = IRType.fn(.i, .o)
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func set(_ k: Int) throws -> NodeID { try n(.isaBound(k, .i)) }
    mutating func applied(_ p: Int, _ x: Int) throws -> NodeID {
        try n(.isaVarApp(head: try n(.isaBound(p, P)), args: [try set(x)]))
    }
    mutating func eq(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.ifol(.eq)), .fn(.i, .fn(.i, .o)), args: [a, b]))
    }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
    mutating func all(_ T: IRType, _ body: NodeID) throws -> NodeID { try n(.ifolAll(T, body: body)) }
    mutating func cited(_ name: String, _ a: Axiom, _ root: NodeID) throws -> Statement {
        Statement(name: name, root: root, proof: try n(.use(.axiom(a), [.i], root)), theory: "IFOL")
    }
}

/// IFOL's quantifier rules, `eq_reflection`, `refl` and `subst` at `[i]`, each its statement proved by citing the axiom, as
/// Isabelle registers the fact: `subst` is base's `class_subst`, the kernel proving `IFOL.subst`, the unit's own claim
/// beside base's; the other six are Logic's, unbuilt, and refused there.
@Test func ifolsSubstAtIIsBasesClassSubstAndItsOtherRulesAreUnbuilt() throws {
    var q = Q()
    let P = q.P
    let allI = try q.all(P, try q.imp(try q.all(.i, try q.applied(1, 0)), try q.all(.i, try q.applied(1, 0))))
    let spec = try q.all(P, try q.all(.i, try q.imp(try q.all(.i, try q.applied(2, 0)), try q.applied(1, 0))))
    let exI = try q.all(P, try q.all(.i, try q.imp(try q.applied(1, 0), try q.n(.ifolEx(.i, body: try q.applied(2, 0))))))
    let R = try q.n(.isaBound(1, .o))
    let exE = try q.all(P, try q.all(.o, try q.imp(try q.n(.ifolEx(.i, body: try q.applied(2, 0))),
        try q.imp(try q.all(.i, try q.imp(try q.applied(2, 0), R)), try q.n(.isaBound(0, .o))))))
    let xy = try q.eq(try q.set(1), try q.set(0))
    let eqReflection = try q.all(.i, try q.all(.i, try q.imp(xy, xy)))
    let refl = try q.all(.i, try q.eq(try q.set(0), try q.set(0)))
    let subst = try q.all(.i, try q.all(.i, try q.all(P, try q.imp(try q.eq(try q.set(2), try q.set(1)),
        try q.imp(try q.applied(0, 2), try q.applied(0, 1))))))
    let statements = [try q.cited("IFOL.allI", .ifol(.allI), allI), try q.cited("IFOL.spec", .ifol(.spec), spec),
                      try q.cited("IFOL.exI", .ifol(.exI), exI), try q.cited("IFOL.exE", .ifol(.exE), exE),
                      try q.cited("IFOL.eq_reflection", .ifol(.eqReflection), eqReflection),
                      try q.cited("IFOL.refl", .ifol(.refl), refl), try q.cited("IFOL.subst", .ifol(.subst), subst)]
    let unit = try lowered(q.t, statements)
    let unbuilt: [Axiom] = [.ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE), .ifol(.eqReflection), .ifol(.refl)]
    #expect(unit.refused.map(\.name) == statements.dropLast().map(\.name))
    #expect(unit.refused.map(\.refusal) == unbuilt.map { .unbuilt(pass: "logic", [.use(.axiom($0), [.i], .o)]) })
    #expect(unit.statements.map(\.name) == ["IFOL.subst"])
    try kernelChecks(unit)
}

/// Pure's `reflexive`, `symmetric` and `transitive` at `i`: base's `eq_refl`, `eq_symm` and `eq_trans` at variables, and at
/// `Pow(0)` through the instance Reify proves at a compound term; the kernel proves every statement.
@Test func puresEqualityAtIIsBasesEqualityAtVariablesAndAtACompoundTerm() throws {
    var q = Q()
    let xy = try q.eq(try q.set(1), try q.set(0)), yx = try q.eq(try q.set(0), try q.set(1))
    let symRoot = try q.all(.i, try q.all(.i, try q.imp(xy, yx)))
    let symProof = try q.n(.isaAllIntro(.i, body: try q.n(.isaAllIntro(.i, body: try q.n(.folImpliesIntro(xy, body: try q.n(
        .isaSymmetric(.i, try q.n(.hyp(0, xy))))))))))
    let (a, b, c) = (try q.set(2), try q.set(1), try q.set(0))
    let ab = try q.eq(a, b), bc = try q.eq(b, c), ac = try q.eq(a, c)
    let transRoot = try q.all(.i, try q.all(.i, try q.all(.i, try q.imp(ab, try q.imp(bc, ac)))))
    let transBody = try q.n(.folImpliesIntro(ab, body: try q.n(.folImpliesIntro(bc, body: try q.n(
        .isaTransitive(.i, try q.n(.hyp(1, ab)), try q.n(.hyp(0, bc))))))))
    var transProof = transBody
    for _ in 0..<3 { transProof = try q.n(.isaAllIntro(.i, body: transProof)) }
    let pow = try q.n(.isaConst(.primitive(.zf(.pow)), .fn(.i, .i), args: [try q.n(.isaConst(.primitive(.zf(.zero)), .i, args: []))]))
    let reflPow = try q.eq(pow, pow)
    let x = try q.set(0), xPow = try q.eq(x, pow), powX = try q.eq(pow, x)
    let symPowRoot = try q.all(.i, try q.imp(xPow, powX))
    let symPowProof = try q.n(.isaAllIntro(.i, body: try q.n(.folImpliesIntro(xPow, body: try q.n(
        .isaSymmetric(.i, try q.n(.hyp(0, xPow))))))))
    let statements = [Statement(name: "T.sym", root: symRoot, proof: symProof, theory: "Test"),
                      Statement(name: "T.trans", root: transRoot, proof: transProof, theory: "Test"),
                      Statement(name: "T.reflPow", root: reflPow, proof: try q.n(.isaReflexive(pow)), theory: "Test"),
                      Statement(name: "T.symPow", root: symPowRoot, proof: symPowProof, theory: "Test")]
    let unit = try lowered(q.t, statements)
    #expect(unit.refused.isEmpty)
    #expect(Set(unit.statements.map(\.name)).isSuperset(of: statements.map(\.name)))
    try kernelChecks(unit)
}

/// `reflexive` at a term holding a λ over a formula, `PrimReplace(0, λx y. y ∈ Pow(x))`: the walk names the atoms inside the
/// λ, so the side is read off the step as the walk was given it — the λ's class is built from the λ as read.
@Test func puresReflexiveAtITakesItsSideAsRead() throws {
    var q = Q()
    let zero = try q.n(.isaConst(.primitive(.zf(.zero)), .i, args: []))
    let pow = try q.n(.isaConst(.primitive(.zf(.pow)), .fn(.i, .i), args: [try q.set(1)]))
    let member = try q.n(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [try q.set(0), pow]))
    let relation = IRType.fn(.i, .fn(.i, .o))
    let lambda = try q.n(.isaAbs(.i, body: try q.n(.isaAbs(.i, body: member))))
    let image = try q.n(.isaConst(.primitive(.zf(.primReplace)), .fn(.i, .fn(relation, .i)), args: [zero, lambda]))
    let statement = Statement(name: "T.reflImage", root: try q.eq(image, image), proof: try q.n(.isaReflexive(image)), theory: "Test")
    let unit = try lowered(q.t, [statement])
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.contains { $0.name == "T.reflImage" })
    try kernelChecks(unit)
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

/// The logic's rules as the reader reads them: `conjI` as `and_intro`, `disjE` as `or_elim`, `classical` as its isa step
/// over IFOL's `¬`. Expand unfolds `¬`, Logic makes `classical` the kernel's reductio, and the kernel proves the three
/// schemas.
@Test func theLogicsRulesReadAsStepsAreLoweredAndProved() throws {
    var l = LogicTable()
    let not = try l.not()
    let (A2, B2) = (try l.bound(1, o), try l.bound(0, o))
    func h(_ k: Int, _ a: NodeID) throws -> NodeID { try l.t.intern(.hyp(k, a)) }
    func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID { try l.t.intern(.folImpliesIntro(a, body: body)) }
    func fix(_ n: Int, _ body: NodeID) throws -> NodeID {
        var p = body
        for _ in 0..<n { p = try l.t.intern(.isaAllIntro(o, body: p)) }
        return p
    }
    let conj = Statement(name: "T.conj", root: try l.all(o, try l.all(o, try l.imp(A2, try l.imp(B2, try l.and(A2, B2))))),
                         proof: try fix(2, try assume(A2, try assume(B2, try l.t.intern(.folAndIntro(try h(1, A2), try h(0, B2)))))),
                         theory: "Test")
    let (A3, B3, C3) = (try l.bound(2, o), try l.bound(1, o), try l.bound(0, o))
    let or3 = try l.t.intern(.folOr(A3, B3)), ac = try l.imp(A3, C3), bc = try l.imp(B3, C3)
    let cases = try l.t.intern(.folOrElim(try h(2, or3), try h(1, ac), try h(0, bc)))
    let disj = Statement(name: "T.cases", root: try l.all(o, try l.all(o, try l.all(o, try l.imp(or3, try l.imp(ac, try l.imp(bc, C3)))))),
                         proof: try fix(3, try assume(or3, try assume(ac, try assume(bc, cases)))), theory: "Test")
    let A1 = try l.bound(0, o)
    let premise = try l.imp(try l.const(.defined(not.constant), .fn(o, o), A1), A1)
    let classical = Statement(name: "T.classical", root: try l.all(o, try l.imp(premise, A1)),
                              proof: try fix(1, try assume(premise, try l.t.intern(.isaClassical(A1, try h(0, premise))))),
                              theory: "Test")
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [conj, disj, classical], definitions: [not])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["T.conj", "T.cases", "T.classical"])
    try kernelChecks(unit)
}

/// `IFOL.conjunct1` as Isabelle proves it: its box at `P` and `Q`, the box `and_elim_l` at its letters. The box is a
/// schema of the unit, the theorem its `schema_inst`, and the kernel proves both.
@Test func aTheoremProvedThroughABoxIsASchemaInstanceOfItsSchema() throws {
    var l = LogicTable()
    let (A, B) = (try l.bound(1, o), try l.bound(0, o))
    let both = try l.and(A, B)
    let root = try l.all(o, try l.all(o, try l.imp(both, A)))
    func fix(_ body: NodeID) throws -> NodeID {
        try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(o, body: body))))
    }
    let elim = try l.t.intern(.folAndElimL(try l.t.intern(.hyp(0, both))))
    let box = Statement(name: "T.BOX_conjunct1", root: root, proof: try fix(try l.t.intern(.folImpliesIntro(both, body: elim))),
                        theory: "Test")
    let cited = try l.t.intern(.use(.theorem("T.BOX_conjunct1"), [], root))
    let instance = try l.t.intern(.isaAllElim(try l.t.intern(.isaAllElim(cited, A)), B))
    let conjunct1 = Statement(name: "T.conjunct1", root: root, proof: try fix(instance), theory: "Test")
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [box, conjunct1])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.name) == ["T.BOX_conjunct1", "T.conjunct1"])
    try kernelChecks(unit)
}

/// `equal_elim (symmetric (combination (reflexive Trueprop) q)) fact`, the simplifier's rewrite of `fact ⊢ B` by
/// `q ⊢ A ↔ B`: `Trueprop` is `λP. P`, its `reflexive` pointwise over truth sets, the `combination` its truth instance at
/// `A`. The kernel proves the schema.
@Test func aRewriteUnderTruepropIsLoweredAndProved() throws {
    var l = LogicTable()
    let (A, B) = (try l.bound(1, o), try l.bound(0, o))
    let ab = try l.t.intern(.folIff(A, B))
    let identity = try l.t.intern(.isaAbs(o, body: try l.bound(0, o)))
    let lifted = try l.t.intern(.isaCombination(.fn(o, o), try l.t.intern(.isaReflexive(identity)), try l.t.intern(.hyp(1, ab))))
    let rewrite = try l.t.intern(.folIffElimL(try l.t.intern(.isaSymmetric(o, lifted)), try l.t.intern(.hyp(0, B))))
    let body = try l.t.intern(.folImpliesIntro(ab, body: try l.t.intern(.folImpliesIntro(B, body: rewrite))))
    let rw = Statement(name: "T.rewrite", root: try l.all(o, try l.all(o, try l.imp(ab, try l.imp(B, A)))),
                       proof: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(o, body: body)))), theory: "Test")
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [rw])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}

/// Pure's `⋀` over a proposition, introduced in a proof and instantiated at the statement's letter: the intro a truth set,
/// its elimination the truth instance. In a premise it is a truth set too, instantiated from its hypothesis. And `TERM`
/// unfolded, `⋀C. C ⟹ C`, is one truth set whether it stands at a statement's top (`T.term`) or in a premise
/// (`T.useTerm`): a proof passing the one to the other meets one formula, where a letter on the top did not. The kernel
/// proves all four.
@Test func pureAllOverAPropositionIsLoweredAndProved() throws {
    var l = LogicTable()
    let A = try l.bound(0, o), P = try l.t.intern(.isaPropBound(0))
    let reflexive = try l.t.intern(.isaPropIntro(body: try l.t.intern(.isaReflexive(P))))
    let unfolded = try l.t.intern(.folIffElimL(try l.t.intern(.isaAllElim(reflexive, A)), try l.t.intern(.hyp(0, A))))
    let protect = Statement(name: "T.protect", root: try l.all(o, try l.imp(A, A)),
                            proof: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.folImpliesIntro(A, body: unfolded)))),
                            theory: "Test")
    let premise = try l.t.intern(.isaPropAll(body: try l.imp(P, P)))
    let applied = try l.t.intern(.isaAllElim(try l.t.intern(.hyp(0, premise)), A))
    let use = Statement(name: "T.usePremise", root: try l.all(o, try l.imp(premise, try l.imp(A, A))),
                        proof: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.folImpliesIntro(premise, body: applied)))),
                        theory: "Test")
    let termRoot = try l.all(o, premise)
    let identity = try l.t.intern(.isaPropIntro(body: try l.t.intern(.folImpliesIntro(P, body: try l.t.intern(.hyp(0, P))))))
    let term = Statement(name: "T.term", root: termRoot, proof: try l.t.intern(.isaAllIntro(o, body: identity)), theory: "Test")
    let (X, Q) = (try l.bound(1, o), try l.bound(0, o))
    let cited = try l.t.intern(.isaAllElim(try l.t.intern(.use(.theorem("T.term"), [], termRoot)), X))
    let consumer = try l.t.intern(.folImpliesIntro(premise, body: try l.t.intern(.folImpliesIntro(Q, body: try l.t.intern(.hyp(0, Q))))))
    let useTerm = Statement(name: "T.useTerm", root: try l.all(o, try l.all(o, try l.imp(premise, try l.imp(Q, Q)))),
                            proof: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(o, body: try l.t.intern(
                                .folImpliesIntro(premise, body: try l.t.intern(.folImpliesElim(consumer, cited)))))))),
                            theory: "Test")
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: [protect, use, term, useTerm])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty)
    try kernelChecks(unit)
}
