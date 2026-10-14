import Testing
import IR
import Lowering

private let i = IRType.i
private let o = IRType.o
private let a = IRType.variable("'a")
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }

private func owners(_ p: Pattern) -> [String] { plan.filter { $0.owns(p) != nil }.map(\.name) }

private func lowered(_ t: Table, _ statements: [Statement]) throws -> Unit {
    var unit = Unit(table: t, statements: statements)
    try pipeline.run(&unit)
    return unit
}

/// Typing is no pass: its registry proves between reify and fol.
@Test func thePlanIsTheDesignsOrder() {
    #expect(plan.map(\.name) == ["expand", "logic", "reify", "fol"])
    #expect(pipeline.passes.map(\.name) == plan.map(\.name))
    #expect(pipeline.provingAfter == "reify")
}

/// DESIGN §4a, "Lowering's components": each of the reader's patterns has the owner the division gives it, and
/// one at most. A pattern at a type variable, the hidden variable and a citation fol-zfc lacks have none yet.
@Test func eachPatternHasTheOwnerTheDivisionGivesIt() {
    let expected: [(Pattern, String?, Owned?)] = [
        (.isaConst(.defined(.ifol, .object), fn(o, fn(o, o)), args: [o, o]), "expand", .rule),
        (.isaConst(.defined(.pure, .meta), fn(o, o), args: [o]), "expand", .rule),
        (.use(.isaDefinition(.fol, .object), [], o), "expand", .rule),
        (.isaConst(.defined(.zf, .meta), fn(fn(i, fn(i, o)), fn(i, o)), args: [fn(i, fn(i, o)), i]), "expand", .rule),
        (.use(.isaDefinition(.zf, .meta), [o], o), "expand", .rule),
        (.use(.axiom(.pure(.combination)), [i, o], o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.spec)), [i], o), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [fn(i, i), fn(i, i)]), "logic", .unbuilt),
        (.ifolAll(o, body: o), "logic", .unbuilt),
        (.isaAllElim(o, fn(o, o)), "logic", .unbuilt),
        (.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [i, i]), "reify", .unbuilt),
        (.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [i, i]), "reify", .unbuilt),
        (.isaConst(.defined(.zf, .object), fn(i, i), args: [i]), "reify", .unbuilt),
        (.isaConst(.declared, i, args: []), "reify", .unbuilt),
        (.isaVarApp(head: fn(i, o), args: [i]), "reify", .unbuilt),
        (.isaAbs(i, body: o), "reify", .unbuilt),
        (.ifolAll(i, body: o), "fol", .rule),
        (.ifolEx(i, body: o), "fol", .rule),
        (.isaAllIntro(i, body: o), "fol", .rule),
        (.isaAllElim(o, i), "fol", .rule),
        (.ifolAll(fn(i, o), body: o), "fol", .unbuilt),
        (.isaAllElim(o, fn(i, fn(i, i))), "fol", .unbuilt),
        (.isaBound(i), "fol", .rule),
        (.isaBound(fn(i, o)), "fol", .unbuilt),
        (.isaGuard(i, o), "fol", .rule),
        (.isaGuard(fn(i, o), o), "fol", .unbuilt),
        (.use(.lemma, [], o), nil, nil),
        (.folImplies(o, o), nil, nil),
        (.hyp(o), nil, nil),
        (.use(.theorem, [], o), nil, nil),
        (.ifolAll(a, body: o), nil, nil),
        (.isaBound(a), nil, nil),
        (.isaConst(.defined(.zf, .object), fn(a, a), args: [a]), nil, nil),
        (.isaConst(.defined(.zf, .meta), fn(a, a), args: [a]), nil, nil),
        (.use(.axiom(.pure(.reflexive)), [a], o), nil, nil),
        (.isaOfClass(i), nil, nil),
        (.isaFree(i), nil, nil),
        (.use(.theorem, [i], o), nil, nil),
        (.use(.axiom(.zf(.replacement)), [], o), nil, nil),
        (.use(.theoryAxiom, [], o), nil, nil),
        (.use(.isaDefinition(.zf, .object), [], o), nil, nil),
    ]
    for (p, owner, owned) in expected {
        #expect(owners(p) == (owner.map { [$0] } ?? []), "\(p)")
        #expect(plan.compactMap { $0.owns(p) }.first == owned, "\(p)")
    }
}

/// `⋀x. ⊥ ⟶ ⊥`: expand, logic and reify own nothing in it, and Fol writes its binder as fol-zfc's, guarded.
@Test func aStatementOfABinderAtIAloneReachesFolZfc() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let root = try t.intern(.ifolAll(i, body: try t.intern(.folImplies(bottom, bottom))))
    let proof = try t.intern(.isaAllIntro(i, body: try t.intern(.folImpliesIntro(bottom, body: try t.intern(.hyp(0, bottom))))))
    var unit = try lowered(t, [Statement(name: "thm", root: root, proof: proof)])
    let set = try unit.table.intern(.folPred("set", args: [try unit.table.intern(.folBound(0))]))
    let guarded = try unit.table.intern(.folForall(body: try unit.table.intern(.folImplies(set, try unit.table.intern(.folImplies(bottom, bottom))))))
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.root) == [guarded])
}

/// An elimination at `Pow(a)`: the compound term is Reify's, so the statement stops at Reify and Fol never
/// meets the instance.
@Test func anEliminationAtACompoundTermStopsAtReify() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let root = try t.intern(.folImplies(bottom, bottom))
    let pow = try t.intern(.isaConst(.primitive(.zf(.pow)), fn(i, i), args: [try t.intern(.isaConst(.declared("a"), i, args: []))]))
    let proof = try t.intern(.isaAllElim(try t.intern(.use(.theorem("lem"), [], try t.intern(.ifolAll(i, body: root)))), pow))
    let unit = try lowered(t, [Statement(name: "thm", root: root, proof: proof)])
    #expect(unit.refused.map(\.refusal) == [.unbuilt(pass: "reify", [
        .isaConst(.declared, i, args: []), .isaConst(.primitive(.zf(.pow)), fn(i, i), args: [i]),
    ])])
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
    var unit = Unit(table: l.t, statements: [statement], definitions: [not])
    try pipeline.run(&unit)
    let unfolded = try unit.table.intern(.folImplies(bottom, bottom))
    #expect(unit.refused.isEmpty)
    #expect(unit.statements.map(\.root) == [try unit.table.intern(.folImplies(unfolded, unfolded))])
}

/// `T.d ≡ λx. ¬(x ∈ x)` is Reify's: it passes Expand, which unfolds its `¬`, and reaches Reify so.
@Test func aDefinitionOwnedByALaterPassReachesItUnfolded() throws {
    var l = LogicTable()
    let not = try l.not()
    let x = try l.bound(0, i)
    let member = try l.mem(x, x)
    let d = try l.definition(Defined(.zf, "T.d", .object), fn(i, o), try l.lam(i, try l.const(.defined(not.constant), fn(o, o), member)))
    var unit = Unit(table: l.t, statements: [], definitions: [not, d])
    try pipeline.run(&unit)
    var reached = d
    reached.definiens = try unit.table.intern(.isaAbs(i, body: try unit.table.intern(.folImplies(member, try unit.table.intern(.folBottom)))))
    #expect(unit.definitions == [not, reached])
}
