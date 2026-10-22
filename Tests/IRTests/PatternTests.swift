import IR
import Testing

private let memT = IRType.fn(.i, .fn(.i, .o))

/// DESIGN §4.3b 4: one primitive at several types is several pieces, never one.
@Test
func onePrimitiveAtSeveralTypesIsSeveralPatterns() throws {
    var t = Table()
    let root = try t.intern(.folBottom)
    let instances: [[IRType]] = [[.i], [.fn(.i, .i)], [.o]]
    let uses = try instances.map { try t.intern(.use(.axiom(.ifol(.refl)), $0, root)) }
    let found = Set(uses.map { Pattern(t[$0], in: t) })
    #expect(found == Set(instances.map { Pattern.use(.axiom(.ifol(.refl)), $0, .o) }))
}

@Test
func aPatternReplacesChildrenByTheirTypesAndDropsNamesAndIndices() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, .i))
    let y = try t.intern(.isaBound(3, .i))
    let atom = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, y]))
    #expect(Pattern(t[atom], in: t) == .isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]))
    #expect(Pattern(t[x], in: t) == Pattern(t[y], in: t), "an index is no part of a pattern")
    let a = try t.intern(.isaConst(.defined(Defined(.zf, "T.a", .object)), .i, args: []))
    let b = try t.intern(.isaConst(.defined(Defined(.zf, "T.b", .object)), .i, args: []))
    #expect(Pattern(t[a], in: t) == Pattern(t[b], in: t), "nor a name")
    let u = try t.intern(.isaFree("u", .i))
    let v = try t.intern(.isaFree("v", .i))
    #expect(Pattern(t[u], in: t) == Pattern(t[v], in: t))
}

@Test
func aProofStepStandsForAFormula() throws {
    var t = Table()
    let A = try t.intern(.folPred(.base("A"), args: []))
    let intro = try t.intern(.folImpliesIntro(A, body: try t.intern(.hyp(0, A))))
    #expect(Pattern(t[intro], in: t) == .folImpliesIntro(.o, body: .o))
}

/// A class variable at `i ⇒ o` is a predicate's argument: a pattern built from the kind alone would lose it.
@Test
func aFolPatternKeepsItsArgumentsTypes() throws {
    var t = Table()
    let x = try t.intern(.folBound(0))
    let K = try t.intern(.isaBound(1, .fn(.i, .o)))
    let sets = try t.intern(.folPred(.base("elem"), args: [x, x]))
    let withClass = try t.intern(.folPred(.base("elem"), args: [x, K]))
    #expect(Pattern(t[sets], in: t) == .folPred(args: [.i, .i]))
    #expect(Pattern(t[withClass], in: t) == .folPred(args: [.i, .fn(.i, .o)]))
}

/// A covered construct is ONE node of both dialects: the reader reads `⟹` as the fol-zfc implication, Pure's
/// `equal_intr` and `equal_elim` as `iff_intro` and `iff_elim_l`, and the logic's rules fol-zfc has as its steps;
/// `classical` and `iff_reflection`, stated over IFOL's defined `¬` and `⟷`, as isa steps. A free variable is the isa
/// dialect's (the index engine's); `¬` is fol-zfc's only, IFOL's being defined. A citation is fol-zfc's only of a
/// theorem at no type
/// arguments, or of base. A binder, its intro and its variable at `o` are fol-zfc's schema letter, and Pure's `⋀` over
/// a
/// proposition the isa dialect's; `schema_inst` is fol-zfc's only. Pure's other equality rules are steps of the isa
/// dialect.
@Test
func eachPatternBelongsToTheIsaDialectTheFolDialectOrBoth() {
    #expect(Pattern.folImplies(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folPred(args: [.i]).dialects == [.fol])
    #expect(Pattern.folNot(.o).dialects == [.fol])
    #expect(Pattern.isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]).dialects == [.isa])
    #expect(Pattern.isaFree(.i).dialects == [.isa])
    #expect(Pattern.isaOfClass(.variable("'a")).dialects == [.isa])
    #expect(Pattern.use(.theorem, [], .o).dialects == [.isa, .fol])
    #expect(Pattern.use(.theorem, [.i], .o).dialects == [.isa])
    #expect(Pattern.use(.axiom(.ifol(.subst)), [.i], .o).dialects == [.isa])
    #expect(Pattern.use(.base, [], .o).dialects == [.fol])
    #expect(Pattern.isaPropAll.dialects == [.isa])
    #expect(Pattern.isaPropIntro.dialects == [.isa])
    #expect(Pattern.isaPropBound.dialects == [.isa])
    #expect(Pattern.isaReflexive(.o).dialects == [.isa])
    #expect(Pattern.isaSymmetric(.o, .o).dialects == [.isa])
    #expect(Pattern.isaTransitive(.o, .o, .o).dialects == [.isa])
    #expect(Pattern.isaCombination(.fn(.o, .o), .o, .o).dialects == [.isa])
    #expect(Pattern.isaAbstract(.fn(.i, .o), .o).dialects == [.isa])
    #expect(Pattern.folIffIntro(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folIffElimL(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folAndIntro(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folAndElimL(.o).dialects == [.isa, .fol])
    #expect(Pattern.folAndElimR(.o).dialects == [.isa, .fol])
    #expect(Pattern.folOrIntroL(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folOrIntroR(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folOrElim(.o, .o, .o).dialects == [.isa, .fol])
    #expect(Pattern.folBottomElim(.o, .o).dialects == [.isa, .fol])
    #expect(Pattern.isaClassical(.o, .o).dialects == [.isa])
    #expect(Pattern.isaIffReflection(.o, .o, .o).dialects == [.isa])
    #expect(Pattern.isaDefinition(.zf, .object, [], args: [.i]).dialects == [.isa])
    #expect(Pattern.use(.axiom(.zf(.extension)), [], .o).dialects == [.isa])
    #expect(Pattern.use(.lemma, [], .o).dialects == [.isa, .fol])
    #expect(Pattern.isaGuard(.i, .o).dialects == [.isa])
    #expect(Pattern.ifolAll(.o, body: .o).dialects == [.isa, .fol])
    #expect(Pattern.isaAllIntro(.o, body: .o).dialects == [.isa, .fol])
    #expect(Pattern.isaBound(.o).dialects == [.isa, .fol])
    #expect(Pattern.ifolAll(.i, body: .o).dialects == [.isa])
    #expect(Pattern.ifolEx(.o, body: .o).dialects == [.isa])
    #expect(Pattern.isaAllElim(.o, .o).dialects == [.isa])
    #expect(Pattern.folSchemaInst(.o, .o).dialects == [.fol])
}

@Test
func aPatternPrintsDeterministically() {
    #expect("\(Pattern.use(.axiom(.ifol(.subst)), [.i], .o))" == "use(axiom IFOL.subst, [i], o)")
    #expect("\(Pattern.isaConst(.defined(.zf, .object), .fn(.i, .i), args: [.i]))" ==
        "isaConst(defined zf object, (i => i), args: [i])")
    #expect("\(Pattern.isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]))"
        == "isaConst(primitive ZF_Base.mem, (i => (i => o)), args: [i, i])")
    #expect("\(Pattern.isaDefinition(.pure, .meta, [], args: [.o]))" == "isaDefinition(pure, meta, [], args: [o])")
}

/// A class's definition is cited as a constant's is: by the family that declares the class, at the meta level, a
/// membership being a proposition.
@Test
func aClassDefinitionsCitationIsItsFamilysAtTheMetaLevel() throws {
    var t = Table()
    let term = TypeClass(.ifol, "IFOL.term")
    let member = try t.intern(.isaOfClass(.i, term))
    let stated = try t.equation(.o, member, member)
    let cited = try t.intern(.isaDefinition("IFOL.term_class_def", of: .ofClass(term), [.i], stated, args: []))
    #expect(Pattern(t[cited], in: t) == .isaDefinition(.ifol, .meta, [.i], args: []))
    #expect(Pattern(t[member], in: t) == .isaOfClass(.i))
}

@Test
func thePatternsUnderRootsAreTheOnesTheyReach() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, .i))
    let atom = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, x]))
    let root = try t.intern(.ifolAll(.i, body: atom))
    #expect(patterns(under: [root], in: t) == [
        .ifolAll(.i, body: .o),
        .isaConst(.primitive(.zf(.mem)), memT, args: [.i, .i]),
        .isaBound(.i),
    ])
}
