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
        (.isaConst(.defined(.ifol), fn(o, fn(o, o)), args: [o, o]), "expand", .unbuilt),
        (.isaConst(.defined(.pure), fn(o, o), args: [o]), "expand", .unbuilt),
        (.use(.isaDefinition(.fol), [], o), "expand", .unbuilt),
        (.use(.axiom(.pure(.combination)), [i, o], o), "logic", .unbuilt),
        (.use(.axiom(.ifol(.spec)), [i], o), "logic", .unbuilt),
        (.isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [fn(i, i), fn(i, i)]), "logic", .unbuilt),
        (.ifolAll(o, body: o), "logic", .unbuilt),
        (.isaAllElim(o, fn(o, o)), "logic", .unbuilt),
        (.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [i, i]), "reify", .unbuilt),
        (.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [i, i]), "reify", .unbuilt),
        (.isaConst(.defined(.zf), fn(i, i), args: [i]), "reify", .unbuilt),
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
        (.isaConst(.defined(.zf), fn(a, a), args: [a]), nil, nil),
        (.use(.axiom(.pure(.reflexive)), [a], o), nil, nil),
        (.isaOfClass(i), nil, nil),
        (.isaFree(i), nil, nil),
        (.use(.theorem, [i], o), nil, nil),
        (.use(.axiom(.zf(.replacement)), [], o), nil, nil),
        (.use(.theoryAxiom, [], o), nil, nil),
        (.use(.isaDefinition(.zf), [], o), nil, nil),
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
