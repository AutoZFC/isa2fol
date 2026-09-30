import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }
private let memT = fn(i, fn(i, o))

private struct P {
    var t = Table()
    mutating func b(_ k: Int) throws -> NodeID { try t.intern(.folBound(k)) }
    mutating func pred(_ n: String, _ xs: NodeID...) throws -> NodeID { try t.intern(.folPred(n, args: xs)) }
    mutating func mem(_ a: NodeID, _ b: NodeID) throws -> NodeID { try t.intern(.isaConst("ZF_Base.mem", memT, args: [a, b])) }
    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try t.intern(.hyp(k, a)) }
    mutating func concl(_ s: NodeID) -> NodeID { t.conclusion(of: s)! }
}

/// A step constrains only its principal connective: `and_intro` over two isa statements is valid.
@Test func anIntroductionTakesPremisesOfAnyDialect() throws {
    var p = P()
    let a = try p.t.intern(.isaFree("a", i))
    let isaAtom = try p.mem(a, a)
    let isaAll = try p.t.intern(.ifolAll(i, body: try p.mem(try p.t.intern(.isaBound(0, i)), a)))
    let both = try p.t.intern(.folAndIntro(try p.hyp(1, isaAtom), try p.hyp(0, isaAll)))
    #expect(p.concl(both) == (try p.t.intern(.folAnd(isaAtom, isaAll))))
    #expect(p.t.type(of: both) == nil, "a step is not a value")
}

/// An elimination consumes: its major premise must have the rule's connective at the top.
@Test func anEliminationRefusesTheWrongPrincipalConnective() throws {
    var p = P()
    let set0 = try p.pred("set", try p.b(0))
    let premise = try p.hyp(0, set0)
    #expect(throws: TableError.principalConnective(premise)) { try p.t.intern(.folAndElimL(premise)) }
    #expect(throws: TableError.principalConnective(premise)) {
        try p.t.intern(.isaAllElim(premise, try p.b(0)))
    }
}

@Test func impliesElimMatchesTheAntecedentByID() throws {
    var p = P()
    let a = try p.pred("A"), b = try p.pred("B"), c = try p.pred("C")
    let ab = try p.hyp(1, try p.t.intern(.folImplies(a, b)))
    #expect(p.concl(try p.t.intern(.folImpliesElim(ab, try p.hyp(0, a)))) == b)
    #expect(throws: TableError.premiseMismatch(expected: a, found: c)) {
        try p.t.intern(.folImpliesElim(ab, try p.hyp(0, c)))
    }
}

@Test func eachRuleConcludesWhatTheCheckerDerives() throws {
    var p = P()
    let a = try p.pred("A"), b = try p.pred("B"), bottom = try p.t.intern(.folBottom)
    let notA = try p.t.intern(.folNot(a))
    let ha = try p.hyp(0, a)
    #expect(p.concl(try p.t.intern(.folImpliesIntro(a, body: ha))) == (try p.t.intern(.folImplies(a, a))))
    let andAB = try p.t.intern(.folAnd(a, b))
    #expect(p.concl(try p.t.intern(.folAndElimR(try p.hyp(0, andAB)))) == b)
    #expect(p.concl(try p.t.intern(.folOrIntroL(ha, b))) == (try p.t.intern(.folOr(a, b))))
    #expect(p.concl(try p.t.intern(.folOrIntroR(b, ha))) == (try p.t.intern(.folOr(b, a))))
    let contra = try p.t.intern(.folNotElim(try p.hyp(1, notA), ha))
    #expect(p.concl(contra) == bottom)
    #expect(p.concl(try p.t.intern(.folNotIntro(a, body: contra))) == (try p.t.intern(.folNot(a))))
    #expect(p.concl(try p.t.intern(.folClassicalAbsurd(a, body: try p.t.intern(.folNotElim(try p.hyp(0, notA), try p.hyp(1, a)))))) == a)
    #expect(p.concl(try p.t.intern(.folBottomElim(try p.hyp(0, bottom), b))) == b)
    let aa = try p.t.intern(.folImpliesIntro(a, body: ha))
    let iff = try p.t.intern(.folIffIntro(aa, aa))
    #expect(p.concl(iff) == (try p.t.intern(.folIff(a, a))))
    #expect(p.concl(try p.t.intern(.folIffElimL(iff, ha))) == a)
    let orAB = try p.t.intern(.folOr(a, b))
    let bToA = try p.hyp(0, try p.t.intern(.folImplies(b, a)))
    #expect(p.concl(try p.t.intern(.folOrElim(try p.hyp(1, orAB), aa, bToA))) == a)
    let root = try p.t.intern(.folAnd(a, b))
    #expect(p.concl(try p.t.intern(.use("thm", [], root))) == root)
}

/// A citation's types are part of what it is: one statement cited at two instances is two steps.
@Test func aCitationCarriesItsTypes() throws {
    var p = P()
    let root = try p.pred("A")
    let atI = try p.t.intern(.use("thm", [i], root)), atO = try p.t.intern(.use("thm", [o], root))
    #expect(atI != atO)
    #expect(p.concl(atI) == root)
}

@Test func aTypeVariableTypesNodesLikeAnyType() throws {
    var p = P()
    let a = IRType.variable("'a"), eqT = fn(a, fn(a, o))
    let x = try p.t.intern(.isaBound(0, a)), y = try p.t.intern(.isaFree("y", a))
    let xx = try p.t.intern(.isaConst("IFOL.eq", eqT, args: [x, x]))
    let yy = try p.t.intern(.isaConst("IFOL.eq", eqT, args: [y, y]))
    let all = try p.hyp(0, try p.t.intern(.ifolAll(a, body: xx)))
    #expect(p.concl(try p.t.intern(.isaAllElim(all, y))) == yy)
    let z = try p.t.intern(.isaFree("z", i))
    #expect(throws: TableError.childType(expected: a, found: i)) { try p.t.intern(.isaAllElim(all, z)) }
}

/// A term binder's body proves φ with the bound variable loose at 0: no fixed variable exists.
@Test func quantifierStepsWorkOnLooseIndices() throws {
    var p = P()
    let set0 = try p.pred("set", try p.b(0))
    let all = try p.t.intern(.folForall(body: set0))
    let intro = try p.t.intern(.folForallIntro(body: try p.hyp(0, set0)))
    #expect(p.concl(intro) == all)
    #expect(p.t.looseBound(of: intro) == 0, "the term binder binds the body's loose term 0")
    #expect(p.t.looseHyps(of: intro) == 1, "a term binder binds no hypothesis")
    let elim = try p.t.intern(.folForallElim(try p.hyp(0, all), try p.b(3)))
    #expect(p.concl(elim) == (try p.pred("set", try p.b(3))))
    #expect(throws: TableError.notATermVariable(try p.t.intern(.isaFree("a", i)))) {
        try p.t.intern(.folForallElim(try p.hyp(0, all), try p.t.intern(.isaFree("a", i))))
    }
}

/// `∃ intro` abstracts every occurrence of the witness; `∃ elim`'s conclusion may not mention it.
@Test func existentialStepsAbstractAndGuardTheWitness() throws {
    var p = P()
    let elem01 = try p.pred("elem", try p.b(0), try p.b(1))
    let intro = try p.t.intern(.folExistsIntro(try p.hyp(0, elem01), try p.b(0)))
    let exists = try p.t.intern(.folExists(body: try p.pred("elem", try p.b(0), try p.b(2))))
    #expect(p.concl(intro) == exists)
    let hypothesis = try p.t.intern(.folExists(body: elem01))
    let elim = try p.t.intern(.folExistsElim(try p.hyp(0, hypothesis), body: intro))
    #expect(p.concl(elim) == hypothesis)
    #expect(throws: TableError.witnessEscapes(try p.hyp(0, elem01))) {
        try p.t.intern(.folExistsElim(try p.hyp(0, hypothesis), body: try p.hyp(0, elem01)))
    }
}

/// Before fol, `∃` is typed: a witness `isaBound(k, T)` concludes `ifolEx(T, …)`, which `∃ elim` opens.
@Test func existentialStepsTakeTheTypedExistsBeforeFol() throws {
    var p = P()
    let x0 = try p.t.intern(.isaBound(0, i)), x1 = try p.t.intern(.isaBound(1, i)), x2 = try p.t.intern(.isaBound(2, i))
    let elem01 = try p.pred("elem", x0, x1)
    let intro = try p.t.intern(.folExistsIntro(try p.hyp(0, elem01), x0))
    #expect(p.concl(intro) == (try p.t.intern(.ifolEx(i, body: try p.pred("elem", x0, x2)))))
    let hypothesis = try p.t.intern(.ifolEx(i, body: elem01))
    let elim = try p.t.intern(.folExistsElim(try p.hyp(0, hypothesis), body: intro))
    #expect(p.concl(elim) == hypothesis)
    let a = try p.t.intern(.isaFree("a", i))
    #expect(throws: TableError.notATermVariable(a)) {
        try p.t.intern(.folExistsIntro(try p.hyp(0, elem01), a))
    }
}

@Test func theIsaQuantifierStepsTypeTheirTerm() throws {
    var p = P()
    let a = try p.t.intern(.isaFree("a", i))
    let body = try p.mem(try p.t.intern(.isaBound(0, i)), a)
    let all = try p.t.intern(.ifolAll(i, body: body))
    #expect(p.concl(try p.t.intern(.isaAllIntro(i, body: try p.hyp(0, body)))) == all)
    #expect(p.concl(try p.t.intern(.isaAllElim(try p.hyp(0, all), a))) == (try p.mem(a, a)))
    let formula = try p.mem(a, a)
    #expect(throws: TableError.childType(expected: i, found: o)) {
        try p.t.intern(.isaAllElim(try p.hyp(0, all), formula))
    }
    let vacuous = try p.t.intern(.ifolAll(i, body: formula))
    #expect(throws: TableError.childType(expected: i, found: o), "even when the body never uses it") {
        try p.t.intern(.isaAllElim(try p.hyp(0, vacuous), formula))
    }
}

/// η-long is the one canonical form: a function-typed term is a λ, here as in every argument position.
@Test func isaAllElimAtAFunctionTypeTakesAnAbstraction() throws {
    var p = P()
    let a = try p.t.intern(.isaFree("a", i))
    let applied = try p.t.intern(.isaVarApp(head: try p.t.intern(.isaBound(0, fn(i, o))), args: [a]))
    let all = try p.t.intern(.ifolAll(fn(i, o), body: applied))
    let bare = try p.t.intern(.isaFree("Q", fn(i, o)))
    #expect(throws: TableError.functionArgumentNotAbstraction(bare)) {
        try p.t.intern(.isaAllElim(try p.hyp(0, all), bare))
    }
    let lambda = try p.t.intern(.isaAbs(i, body: try p.mem(try p.t.intern(.isaBound(0, i)), a)))
    #expect(p.concl(try p.t.intern(.isaAllElim(try p.hyp(0, all), lambda))) == (try p.mem(a, a)))
}

@Test func aStepIsNotAFormulaAndAFormulaIsNotAStep() throws {
    var p = P()
    let a = try p.pred("A")
    let step = try p.hyp(0, a)
    #expect(throws: TableError.expectedValue(step)) { try p.t.intern(.folNot(step)) }
    #expect(throws: TableError.expectedStep(a)) { try p.t.intern(.folAndElimL(a)) }
}

// MARK: lowering a proof bottom-up with Rule.after

/// The DESIGN.md §4.7 example: once the citation's signature is lowered, `isaAllElim` on it is
/// invalid, so `after` must rewrite it before `intern` sees it. Its conclusion is unchanged.
private struct LowerCitationThenElimination: Rule {
    let isaRoot: NodeID, folRoot: NodeID
    func after(_ n: Node, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if case let .use(name, types, root) = n, root == isaRoot { return try t.intern(.use(name, types, folRoot)) }
        guard case let .isaAllElim(p, x) = n, case let .folForall(body)? = t.conclusion(of: p).map({ t[$0] }),
              case let .folImplies(guardFormula, _) = t[body] else { return nil }
        let guardHere = try instantiate(guardFormula, with: x, in: &t)
        let elim = try t.intern(.folForallElim(p, x))
        return try t.intern(.folImpliesElim(elim, try t.intern(.hyp(0, guardHere))))
    }
}

@Test func afterRewritesAStepOnceItsPremisesAreRewritten() throws {
    var p = P()
    let A = try p.t.intern(.isaFree("A", i))
    let memBody = try p.mem(try p.t.intern(.isaBound(0, i)), A)
    let isaRoot = try p.t.intern(.ifolAll(i, body: memBody))
    let folRoot = try p.t.intern(.folForall(body: try p.t.intern(.folImplies(try p.pred("set", try p.b(0)), try p.mem(try p.b(0), A)))))
    let x = try p.b(0)
    let before = try p.t.intern(.isaAllElim(try p.t.intern(.use("thm", [], isaRoot)), x))
    let concluded = p.concl(before)
    let after = try transform(before, LowerCitationThenElimination(isaRoot: isaRoot, folRoot: folRoot), in: &p.t)
    #expect(after != before)
    #expect(p.t.conclusion(of: after) == concluded, "the rewritten step concludes the same statement")
    guard case .folImpliesElim = p.t[after] else { Issue.record("not rewritten: \(p.t[after])"); return }
}

@Test func legalizeRefusesAnIsaStep() throws {
    var p = P()
    let set0 = try p.pred("set", try p.b(0))
    let step = try p.t.intern(.isaAllIntro(i, body: try p.hyp(0, set0)))
    let root = try p.t.intern(.folImpliesIntro(try p.pred("A"), body: step))
    #expect(throws: IRRefusal.sourceKindSurvived(step)) { try legalize(root, in: p.t) }
}
