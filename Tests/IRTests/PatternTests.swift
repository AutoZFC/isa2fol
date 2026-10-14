import Testing
import IR

private let memT = IRType.fn(.i, .fn(.i, .o))

/// DESIGN §4.3b 4: congruence at a function, at a predicate and at a proposition are three cases, never one.
@Test func onePrimitiveAtSeveralTypesIsSeveralPatterns() throws {
    var t = Table()
    let root = try t.intern(.folBottom)
    let instances: [[IRType]] = [[.i, .i], [.i, .o], [.o, .o]]
    let uses = try instances.map { try t.intern(.use(.axiom(.pure(.combination)), $0, root)) }
    let found = Set(uses.map { Pattern(t[$0], in: t) })
    #expect(found == Set(instances.map { Pattern.use(.axiom(.pure(.combination)), $0, .o) }))
}

@Test func aPatternReplacesChildrenByTheirTypesAndDropsNamesAndIndices() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, .i)), y = try t.intern(.isaBound(3, .i))
    let atom = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, y]))
    #expect(Pattern(t[atom], in: t) == .isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]))
    #expect(Pattern(t[x], in: t) == Pattern(t[y], in: t), "an index is no part of a pattern")
    let a = try t.intern(.isaConst(.defined(Defined(.zf, "T.a")), .i, args: []))
    let b = try t.intern(.isaConst(.defined(Defined(.zf, "T.b")), .i, args: []))
    #expect(Pattern(t[a], in: t) == Pattern(t[b], in: t), "nor a name")
    let hidden = try t.intern(.isaFree(.hidden, .i)), named = try t.intern(.isaFree(.named("v"), .i))
    #expect(Pattern(t[hidden], in: t) == Pattern(t[named], in: t))
}

@Test func aProofStepStandsForAFormula() throws {
    var t = Table()
    let A = try t.intern(.folPred("A", args: []))
    let intro = try t.intern(.folImpliesIntro(A, body: try t.intern(.hyp(0, A))))
    #expect(Pattern(t[intro], in: t) == .folImpliesIntro(.o, body: .o))
}

/// A class variable at `i ⇒ o` is a predicate's argument: a pattern built from the kind alone would lose it.
@Test func aFolPatternKeepsItsArgumentsTypes() throws {
    var t = Table()
    let x = try t.intern(.folBound(0)), K = try t.intern(.isaBound(1, .fn(.i, .o)))
    let sets = try t.intern(.folPred("elem", args: [x, x])), withClass = try t.intern(.folPred("elem", args: [x, K]))
    #expect(Pattern(t[sets], in: t) == .folPred(args: [.i, .i]))
    #expect(Pattern(t[withClass], in: t) == .folPred(args: [.i, .fn(.i, .o)]))
}

@Test func aPatternPrintsDeterministically() {
    #expect("\(Pattern.use(.axiom(.pure(.combination)), [.i, .o], .o))" == "use(axiom Pure.combination, [i, o], o)")
    #expect("\(Pattern.isaConst(.defined(.zf), .fn(.i, .i), args: [.i]))" == "isaConst(defined zf, (i => i), args: [i])")
    #expect("\(Pattern.isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]))"
            == "isaConst(primitive ZF_Base.mem, (i => (i => o)), args: [i, i])")
    #expect("\(Pattern.use(.isaDefinition(.ifol), [], .o))" == "use(definition ifol, [], o)")
}

@Test func thePatternsUnderRootsAreTheOnesTheyReach() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, .i))
    let atom = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, x]))
    let root = try t.intern(.ifolAll(.i, body: atom))
    #expect(patterns(under: [root], in: t) == [
        .ifolAll(.i, body: .o), .isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]), .isaBound(.i),
    ])
}
