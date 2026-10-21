import IR
import Testing

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private let qpair = Constant.defined(Defined(.zf, "QPair.QPair", .object))
private let mem = Constant.primitive(.zf(.mem))
private let collect = Constant.defined(Defined(.zf, "ZF_Base.Collect", .object))

@Test
func equalContentIsTheSameNode() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    #expect(try t.intern(.isaFree("a", i)) == a)
    #expect(a != b)
    let q = try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    #expect(try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b])) == q)
    #expect(try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [b, a])) != q)
}

@Test
func aNodeReadsBackAsItsContent() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    #expect(t[a] == .isaFree("a", i))
}

/// `∀x. mem(x, A)` and `∀y. mem(y, A)` are one formula: no node carries the bound name.
@Test
func alphaEquivalentFormulasAreOneNode() throws {
    func forallMemA(_ t: inout Table) throws -> NodeID {
        let bound = try t.intern(.isaBound(0, i))
        let A = try t.intern(.isaFree("A", i))
        let body = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [bound, A]))
        return try t.intern(.ifolAll(i, body: body))
    }
    var t = Table()
    let x = try forallMemA(&t)
    let y = try forallMemA(&t)
    #expect(x == y)
}

@Test
func looseBoundCountsBindersAboveTheNode() throws {
    var t = Table()
    let b0 = try t.intern(.folBound(0))
    let b1 = try t.intern(.folBound(1))
    let elem = try t.intern(.folPred(.base("elem"), args: [b1, b0]))
    let inner = try t.intern(.folForall(body: elem))
    let outer = try t.intern(.folForall(body: inner))
    #expect(t.looseBound(of: elem) == 2)
    #expect(t.looseBound(of: inner) == 1)
    #expect(t.looseBound(of: outer) == 0)

    let x = try t.intern(.isaBound(0, i))
    let identity = try t.intern(.isaAbs(i, body: x))
    #expect(t.looseBound(of: x) == 1)
    #expect(t.looseBound(of: identity) == 0)
    let free = try t.intern(.isaFree("a", i))
    #expect(t.looseBound(of: free) == 0)
}

@Test
func everyNodeHasItsTypeFromItsContent() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    let pair = try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    let atom = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, pair]))
    let x = try t.intern(.isaBound(0, i))
    let body = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [x, a]))
    let conj = try t.intern(.folAnd(atom, atom))
    let lambda = try t.intern(.isaAbs(i, body: body))
    let all = try t.intern(.ifolAll(i, body: body))
    let bound = try t.intern(.folBound(0))
    #expect(t.type(of: pair) == i)
    #expect(t.type(of: atom) == o)
    #expect(t.type(of: conj) == o)
    #expect(t.type(of: lambda) == fn(i, o))
    #expect(t.type(of: all) == o)
    #expect(t.type(of: bound) == i)
}

/// One table per run, so an ID the table never issued is out of range.
@Test
func anIDTheTableNeverIssuedIsRefused() throws {
    var issuer = Table()
    _ = try issuer.intern(.isaFree("a", i))
    let unissued = try issuer.intern(.isaFree("b", i))
    var t = Table()
    #expect(throws: TableError.unknownNode(unissued)) {
        try t.intern(.folNot(unissued))
    }
}

@Test
func aChildOfTheWrongTypeIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    #expect(throws: TableError.childType(expected: o, found: i)) {
        try t.intern(.folAnd(a, a))
    }
    let atom = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, a]))
    #expect(throws: TableError.childType(expected: i, found: o)) {
        try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, atom]))
    }
}

/// S1: a fol predicate takes variables, never a term.
@Test
func aPredicateArgumentThatIsNotAVariableIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    #expect(throws: TableError.predicateArgumentNotVariable(a)) {
        try t.intern(.folPred(.base("elem"), args: [a, a]))
    }
}

/// A variable keeps its IR type until fol, so a predicate takes isa's variables too — a set, a
/// predicate class, a function class — and `legalize`, not the predicate, refuses them at the end.
@Test
func aPredicateTakesAVariableOfEveryTermType() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let P = try t.intern(.isaBound(1, fn(i, o)))
    let F = try t.intern(.isaBound(2, fn(i, i)))
    let set = try t.intern(.folPred(.base("set"), args: [x]))
    _ = try t.intern(.folPred(.base("elem"), args: [x, P]))
    _ = try t.intern(.folPred(.base("pmem"), args: [x, x, F]))
    _ = try t.intern(.folPred(.base("set"), args: [try t.intern(.folBound(0))]))
    #expect(throws: IRRefusal.sourceKindSurvived(x)) { try legalize(set, in: t) }
}

/// The guard writes fol-zfc's binder while variables are still isa's, so `forall_elim` takes them as a predicate does.
@Test
func aForallEliminationTakesAVariableOfEveryTermType() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let P = try t.intern(.isaBound(1, fn(i, o)))
    let body = try t.intern(.folPred(
        .base("elem"),
        args: [try t.intern(.isaBound(0, i)), try t.intern(.isaBound(2, fn(i, o)))],
    ))
    let all = try t.intern(.folForall(body: body))
    let atX = try t.intern(.folForallElim(try t.intern(.hyp(0, all)), x))
    #expect(t.conclusion(of: atX) == (try t.intern(.folPred(.base("elem"), args: [x, P]))))
    let p = try t.intern(.isaBound(0, o))
    #expect(throws: TableError.propositionAsTerm(p)) { try t.intern(.folForallElim(try t.intern(.hyp(0, all)), p)) }
}

/// S4: a proposition is never reified, so a variable at `o` is no predicate's argument.
@Test
func aVariableAtOIsNotAPredicateArgument() throws {
    var t = Table()
    let p = try t.intern(.isaBound(0, o))
    #expect(throws: TableError.propositionAsTerm(p)) {
        try t.intern(.folPred(.base("set"), args: [p]))
    }
}

/// The ZF surface: `Collect(A, P)` with `P` η-short is not surface-shaped.
@Test
func aFunctionArgumentThatIsNotAnAbstractionIsRefused() throws {
    var t = Table()
    let A = try t.intern(.isaFree("A", i))
    let P = try t.intern(.isaFree("P", fn(i, o)))
    #expect(throws: TableError.functionArgumentNotAbstraction(P)) {
        try t.intern(.isaConst(collect, fn(i, fn(fn(i, o), i)), args: [A, P]))
    }
}

@Test
func aPartialApplicationIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    #expect(throws: TableError.arityMismatch(expected: 2, found: 1)) {
        try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a]))
    }
}

@Test
func aNegativeBoundIndexIsRefused() throws {
    var t = Table()
    #expect(throws: TableError.negativeIndex(-1)) { try t.intern(.isaBound(-1, i)) }
    #expect(throws: TableError.negativeIndex(-2)) { try t.intern(.folBound(-2)) }
}

/// A class variable applied, `P(x)`: the head is a variable, never a constant.
@Test
func anAppliedHeadThatIsNotAVariableIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let P = try t.intern(.isaFree("P", fn(i, o)))
    let applied = try t.intern(.isaVarApp(head: P, args: [a]))
    #expect(t.type(of: applied) == o)
    let x = try t.intern(.isaBound(0, i))
    let lambda = try t.intern(.isaAbs(i, body: try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [x, a]))))
    #expect(throws: TableError.varAppHeadNotVariable(lambda)) {
        try t.intern(.isaVarApp(head: lambda, args: [a]))
    }
}

/// The guard of a variable concludes the formula it carries, as a hypothesis does; IR knows no guard.
@Test
func theGuardOfAVariableConcludesItsFormula() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let set = try t.intern(.folPred(.base("set"), args: [x]))
    let g = try t.intern(.isaGuard(x, set))
    #expect(t.conclusion(of: g) == set)
    let a = try t.intern(.isaConst(.declared("a"), i, args: []))
    #expect(throws: TableError.notATermVariable(a)) { try t.intern(.isaGuard(a, set)) }
    #expect(throws: TableError.childType(expected: o, found: i)) { try t.intern(.isaGuard(x, x)) }
}

/// `schema_inst`: the step instantiates the letter at the top of its premise's conclusion. A premise whose conclusion
/// binds no letter at its top is refused.
@Test
func aSchemaInstantiationConcludesItsPremisesLetterAtTheInstance() throws {
    var t = Table()
    let p = try t.intern(.isaBound(0, o))
    let schema = try t.intern(.ifolAll(o, body: try t.intern(.folImplies(p, p))))
    let c = try t.intern(.folPred(.base("C"), args: []))
    let instance = try t.intern(.folSchemaInst(try t.intern(.use(.theorem("id"), [], schema)), c))
    #expect(t.conclusion(of: instance) == (try t.intern(.folImplies(c, c))))
    let atI = try t.intern(.use(.theorem("lem"), [], try t.intern(.ifolAll(i, body: try t.intern(.folBottom)))))
    #expect(throws: TableError.principalConnective(atI)) { try t.intern(.folSchemaInst(atI, c)) }
}

/// Pure's `≡` is read by its type: `↔` at `o`, `IFOL.eq` at `i`, `Pure.eq` at a function type; `sides(ofEquation:)`
/// reads it back with its type.
@Test
func anEquationIsReadByItsType() throws {
    var t = Table()
    let A = try t.intern(.folPred(.base("A"), args: []))
    let a = try t.intern(.isaConst(.declared("a"), i, args: []))
    let f = try t.intern(.isaAbs(i, body: try t.intern(.isaBound(0, i))))
    #expect(try t.equation(o, A, A) == t.intern(.folIff(A, A)))
    #expect(try t.equation(i, a, a) == t.intern(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [a, a])))
    let atF = try t.equation(fn(i, i), f, f)
    #expect(atF == (try t.intern(.isaConst(.primitive(.pure(.eq)), fn(fn(i, i), fn(fn(i, i), o)), args: [f, f]))))
    #expect(t.sides(ofEquation: atF).map { [$0.type] } == [fn(i, i)])
    let conjunction = try t.intern(.folAnd(A, A))
    #expect(t.sides(ofEquation: conjunction) == nil)
}

/// Pure's equality rules are steps: each concludes by the reading of `≡` at its type.
@Test
func pureEqualityStepsConcludeByTheReadingOfEquality() throws {
    var t = Table()
    let A = try t.intern(.folPred(.base("A"), args: []))
    let B = try t.intern(.folPred(.base("B"), args: []))
    let C = try t.intern(.folPred(.base("C"), args: []))
    let a = try t.intern(.isaConst(.declared("a"), i, args: []))
    let b = try t.intern(.isaConst(.declared("b"), i, args: []))
    let reflO = try t.intern(.isaReflexive(A))
    let reflI = try t.intern(.isaReflexive(a))
    #expect(t.conclusion(of: reflO) == (try t.equation(o, A, A)))
    #expect(t.conclusion(of: reflI) == (try t.equation(i, a, a)))
    let ab = try t.intern(.hyp(0, try t.equation(o, A, B)))
    let bc = try t.intern(.hyp(1, try t.equation(o, B, C)))
    let sym = try t.intern(.isaSymmetric(o, ab))
    let trans = try t.intern(.isaTransitive(o, ab, bc))
    #expect(t.conclusion(of: sym) == (try t.equation(o, B, A)))
    #expect(t.conclusion(of: trans) == (try t.equation(o, A, C)))
    #expect(throws: TableError.premiseMismatch(expected: B, found: A)) { try t.intern(.isaTransitive(o, ab, ab)) }
    let atI = try t.intern(.hyp(0, try t.equation(i, a, b)))
    let symI = try t.intern(.isaSymmetric(i, atI))
    #expect(t.conclusion(of: symI) == (try t.equation(i, b, a)))
    #expect(throws: TableError.childType(expected: o, found: i)) { try t.intern(.isaSymmetric(o, atI)) }
    let notEquation = try t.intern(.hyp(0, A))
    #expect(throws: TableError.principalConnective(notEquation)) { try t.intern(.isaSymmetric(o, notEquation)) }
}

/// `combination` concludes `f x ≡ g y` β-reduced: at `λP. P ∧ C`, from `A ↔ B`, `A ∧ C ↔ B ∧ C`.
@Test
func aCombinationConcludesTheApplicationsBetaReduced() throws {
    var t = Table()
    let A = try t.intern(.folPred(.base("A"), args: []))
    let B = try t.intern(.folPred(.base("B"), args: []))
    let C = try t.intern(.folPred(.base("C"), args: []))
    let context = try t.intern(.isaAbs(o, body: try t.intern(.folAnd(try t.intern(.isaBound(0, o)), C))))
    let q = try t.intern(.hyp(0, try t.equation(o, A, B)))
    let step = try t.intern(.isaCombination(fn(o, o), try t.intern(.isaReflexive(context)), q))
    #expect(t.conclusion(of: step) == (try t.equation(o, try t.intern(.folAnd(A, C)), try t.intern(.folAnd(B, C)))))
    #expect(throws: TableError.notAFunctionType(o)) { try t.intern(.isaCombination(o, q, q)) }
}

/// `abstract_rule` concludes the equation of the two λs from `⋀x. f x ≡ g x`.
@Test
func anAbstractionConcludesTheEquationOfItsLambdas() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let fx = try t.intern(.isaConst(.declared("F"), fn(i, o), args: [x]))
    let gx = try t.intern(.isaConst(.declared("G"), fn(i, o), args: [x]))
    let pointwise = try t.intern(.hyp(0, try t.intern(.ifolAll(i, body: try t.equation(o, fx, gx)))))
    let step = try t.intern(.isaAbstract(fn(i, o), pointwise))
    let f = try t.intern(.isaAbs(i, body: fx))
    let g = try t.intern(.isaAbs(i, body: gx))
    #expect(t.conclusion(of: step) == (try t.equation(fn(i, o), f, g)))
}

/// `classical`'s isa step concludes `P` from `h : X → P`, and refuses an `h` concluding something else;
/// `iff_reflection`'s
/// concludes `P ↔ Q`.
@Test
func theLogicsIsaStepsConcludeTheirRulesConclusions() throws {
    var t = Table()
    let A = try t.intern(.isaBound(1, .o))
    let B = try t.intern(.isaBound(0, .o))
    let premise = try t.intern(.folImplies(B, A))
    let h = try t.intern(.hyp(0, premise))
    let classical = try t.intern(.isaClassical(A, h))
    #expect(t.conclusion(of: classical) == A)
    #expect(throws: TableError.self) { try t.intern(.isaClassical(B, h)) }
    let reflection = try t.intern(.isaIffReflection(A, B, h))
    #expect(t.conclusion(of: reflection) == (try t.intern(.folIff(A, B))))
}

/// Pure's `⋀` over a proposition: its intro concludes it, its variable is a formula and never a predicate's argument,
/// and
/// it is eliminated at a formula as a letter is.
@Test
func pureAllOverAPropositionIsIntroducedAndEliminatedAtAFormula() throws {
    var t = Table()
    let P = try t.intern(.isaPropBound(0))
    let implication = try t.intern(.folImplies(P, P))
    let intro = try t.intern(.isaPropIntro(body: try t.intern(.folImpliesIntro(P, body: try t.intern(.hyp(0, P))))))
    #expect(t.conclusion(of: intro) == (try t.intern(.isaPropAll(body: implication))))
    #expect(t.type(of: P) == .o)
    #expect(throws: TableError.self) { try t.intern(.folPred(.base("set"), args: [P])) }
    let C = try t.intern(.folPred(.base("C"), args: []))
    let instance = try t.intern(.isaAllElim(intro, C))
    #expect(t.conclusion(of: instance) == (try t.intern(.folImplies(C, C))))
}

/// A definition at its terms concludes its statement instantiated at them, `prop_def` at `C` concluding `PROP C ≡ C`;
/// at
/// no terms, its statement; a term of another type than its parameter's is refused.
@Test
func aDefinitionConcludesItsStatementAtItsTerms() throws {
    var t = Table()
    let prop = Defined(.pure, "Pure.prop", .meta)
    let A = try t.intern(.isaBound(0, o))
    let stated = try t.intern(.ifolAll(
        o,
        body: try t.intern(.folIff(try t.intern(.isaConst(.defined(prop), fn(o, o), args: [A])), A)),
    ))
    let C = try t.intern(.folPred(.base("C"), args: []))
    let at = try t.intern(.isaDefinition("Pure.prop_def", of: .constant(prop), [], stated, args: [C]))
    #expect(t.conclusion(of: at) == (try t.intern(.folIff(
        try t.intern(.isaConst(.defined(prop), fn(o, o), args: [C])),
        C,
    ))))
    let bare = try t.intern(.isaDefinition("Pure.prop_def", of: .constant(prop), [], stated, args: []))
    #expect(t.conclusion(of: bare) == stated)
    let x = try t.intern(.isaFree("x", i))
    #expect(throws: TableError.childType(expected: o, found: i)) {
        try t.intern(.isaDefinition("Pure.prop_def", of: .constant(prop), [], stated, args: [x]))
    }
}

/// fol-zfc's `forall_elim` takes Isabelle's class binder as Fol writes it: at `i ⇒ o` its body at the class, at `i ⇒ i`
/// the
/// binder's guard first, `function(K) → …` — the body Fol and the table write by one function.
@Test
func folsForallEliminationTakesAnIsaClassBinderAsFolWritesIt() throws {
    var t = Table()
    let P = IRType.fn(.i, .o)
    let F = IRType.fn(.i, .i)
    let K = try t.intern(.folBound(3))
    let predicate = try t.intern(.ifolAll(
        P,
        body: try t.intern(.folPred(.base("elem"), args: [try t.intern(.folBound(1)), try t.intern(.isaBound(0, P))])),
    ))
    let atP = try t.intern(.folForallElim(try t.intern(.hyp(0, predicate)), K))
    #expect(t.conclusion(of: atP) == (try t.intern(.folPred(.base("elem"), args: [try t.intern(.folBound(0)), K]))))
    let function = try t.intern(.ifolAll(
        F,
        body: try t.intern(.folPred(.base("elem"), args: [try t.intern(.folBound(1)), try t.intern(.isaBound(0, F))])),
    ))
    let atF = try t.intern(.folForallElim(try t.intern(.hyp(0, function)), K))
    let guarded = try t.intern(.folImplies(
        try t.intern(.folPred(.base("function"), args: [K])),
        try t.intern(.folPred(
            .base("elem"),
            args: [try t.intern(.folBound(0)), K],
        )),
    ))
    #expect(t.conclusion(of: atF) == guarded)
}

/// A layer reads the table below it: a node already there is found at its ID, its own are numbered past it, and the
/// table below is unchanged (DESIGN "Memory — a unit of work's nodes leave with it").
@Test
func aLayerFindsTheTableBelowAndNumbersItsOwnPastIt() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    var layer = Table(over: t)
    #expect(try layer.intern(.isaFree("a", i)) == a)
    let q = try layer.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    #expect(layer.count == t.count + 1)
    #expect(layer[q] == .isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    #expect(layer[b] == .isaFree("b", i))
    #expect(layer.type(of: q) == i)
    #expect(t.count == 2)
}

/// The index holds IDs, never nodes: every node is found again at its ID across the index's growth, in the table and
/// from a layer over it (DESIGN "A step written once a proof", decision 2).
@Test
func everyNodeIsFoundAgainAcrossTheIndexsGrowth() throws {
    var t = Table()
    let ids = try (0..<5000).map { try t.intern(.isaFree("x\($0)", i)) }
    #expect(try (0..<5000).allSatisfy { try t.intern(.isaFree("x\($0)", i)) == ids[$0] })
    #expect(t.count == 5000)
    var layer = Table(over: t)
    #expect(try (0..<5000).allSatisfy { try layer.intern(.isaFree("x\($0)", i)) == ids[$0] })
    let fresh = try (0..<3000).map { try layer.intern(.isaFree("y\($0)", i)) }
    #expect(try (0..<3000).allSatisfy { try layer.intern(.isaFree("y\($0)", i)) == fresh[$0] })
    #expect(layer.count == 8000)
    #expect(t.count == 5000)
}

/// An import adds to the table exactly the nodes a layer's results reach that it lacks, children first, and finds the
/// rest; the layer's other nodes leave with it.
@Test
func anImportAddsExactlyTheNewNodesItsResultsReach() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    var layer = Table(over: t)
    _ = try layer.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [b, a]))
    let ab = try layer.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    let m = try layer.intern(.isaConst(mem, fn(i, fn(i, o)), args: [ab, a]))
    let before = t.count
    let out = try t.imported([m, a], from: &layer)
    #expect(t.count == before + 2)
    #expect(out[1] == a)
    let q = try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    #expect(t.count == before + 2)
    #expect(t[out[0]] == .isaConst(mem, fn(i, fn(i, o)), args: [q, a]))
}

/// An imported step concludes what its layer derived, the conclusion imported with it: `∧`-intro of two hypotheses
/// concludes their conjunction, which the table lacked.
@Test
func anImportedStepConcludesWhatItsLayerDerivedItsConclusionImportedWithIt() throws {
    var t = Table()
    let p = try t.intern(.isaConst(.declared("P"), o, args: []))
    let q = try t.intern(.isaConst(.declared("Q"), o, args: []))
    var layer = Table(over: t)
    let both = try layer.intern(.folAndIntro(try layer.intern(.hyp(0, p)), try layer.intern(.hyp(1, q))))
    let before = t.count
    let out = try t.imported([both], from: &layer)
    #expect(t.count == before + 4)
    #expect(t.conclusion(of: out[0]) == (try t.intern(.folAnd(p, q))))
    #expect(t.count == before + 4)
}

private struct Holding: Request {
    let name: String
    let formula: NodeID

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Holding {
        Holding(name: name, formula: try f(formula))
    }
}

/// A lemma's citation imported carries its request remapped by the request itself: the ID it holds is the table's, and
/// what it reaches is imported with it, though the citation's children do not reach it.
@Test
func anImportedLemmaCitationHasItsRequestsIDsInTheTable() throws {
    var t = Table()
    let a = try t.intern(.isaFree("a", i))
    let b = try t.intern(.isaFree("b", i))
    var layer = Table(over: t)
    let held = try layer.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, a]))
    let root = try layer.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, b]))
    let cited = try layer.intern(.use(.lemma(Lemma(Holding(name: "L", formula: held))), [], root))
    let out = try t.imported([cited], from: &layer)
    let count = t.count
    let aa = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, a]))
    let ab = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, b]))
    #expect(t.count == count)
    #expect(t[out[0]] == .use(.lemma(Lemma(Holding(name: "L", formula: aa))), [], ab))
}

/// ⚠ A WIDE KIND HELD INLINE WIDENS EVERY NODE: the table holds each node at the enum's width, 80 bytes while a
/// definition's name, types and arguments were inline, for a connective's two children.
@Test
func aNodeIsSixteenBytesAndATypeOneWord() {
    #expect(MemoryLayout<Node>.stride == 16)
    #expect(MemoryLayout<IRType>.stride == 8)
}
