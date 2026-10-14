import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }

private let qpair = Constant.defined(Defined(.zf, "QPair.QPair"))
private let mem = Constant.primitive(.zf(.mem))
private let collect = Constant.defined(Defined(.zf, "ZF_Base.Collect"))

@Test func equalContentIsTheSameNode() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let b = try t.intern(.isaFree(.named("b"), i))
    #expect(try t.intern(.isaFree(.named("a"), i)) == a)
    #expect(a != b)
    let q = try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b]))
    #expect(try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a, b])) == q)
    #expect(try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [b, a])) != q)
}

@Test func aNodeReadsBackAsItsContent() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    #expect(t[a] == .isaFree(.named("a"), i))
}

/// `∀x. mem(x, A)` and `∀y. mem(y, A)` are one formula: no node carries the bound name.
@Test func alphaEquivalentFormulasAreOneNode() throws {
    func forallMemA(_ t: inout Table) throws -> NodeID {
        let bound = try t.intern(.isaBound(0, i))
        let A = try t.intern(.isaFree(.named("A"), i))
        let body = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [bound, A]))
        return try t.intern(.ifolAll(i, body: body))
    }
    var t = Table()
    let x = try forallMemA(&t)
    let y = try forallMemA(&t)
    #expect(x == y)
}

@Test func looseBoundCountsBindersAboveTheNode() throws {
    var t = Table()
    let b0 = try t.intern(.folBound(0))
    let b1 = try t.intern(.folBound(1))
    let elem = try t.intern(.folPred("elem", args: [b1, b0]))
    let inner = try t.intern(.folForall(body: elem))
    let outer = try t.intern(.folForall(body: inner))
    #expect(t.looseBound(of: elem) == 2)
    #expect(t.looseBound(of: inner) == 1)
    #expect(t.looseBound(of: outer) == 0)

    let x = try t.intern(.isaBound(0, i))
    let identity = try t.intern(.isaAbs(i, body: x))
    #expect(t.looseBound(of: x) == 1)
    #expect(t.looseBound(of: identity) == 0)
    let free = try t.intern(.isaFree(.named("a"), i))
    #expect(t.looseBound(of: free) == 0)
}

@Test func everyNodeHasItsTypeFromItsContent() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let b = try t.intern(.isaFree(.named("b"), i))
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
@Test func anIDTheTableNeverIssuedIsRefused() throws {
    var issuer = Table()
    _ = try issuer.intern(.isaFree(.named("a"), i))
    let unissued = try issuer.intern(.isaFree(.named("b"), i))
    var t = Table()
    #expect(throws: TableError.unknownNode(unissued)) {
        try t.intern(.folNot(unissued))
    }
}

@Test func aChildOfTheWrongTypeIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    #expect(throws: TableError.childType(expected: o, found: i)) {
        try t.intern(.folAnd(a, a))
    }
    let atom = try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, a]))
    #expect(throws: TableError.childType(expected: i, found: o)) {
        try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [a, atom]))
    }
}

/// S1: a fol predicate takes variables, never a term.
@Test func aPredicateArgumentThatIsNotAVariableIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    #expect(throws: TableError.predicateArgumentNotVariable(a)) {
        try t.intern(.folPred("elem", args: [a, a]))
    }
}

/// A variable keeps its IR type until fol, so a predicate takes isa's variables too — a set, a
/// predicate class, a function class — and `legalize`, not the predicate, refuses them at the end.
@Test func aPredicateTakesAVariableOfEveryTermType() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let P = try t.intern(.isaBound(1, fn(i, o)))
    let F = try t.intern(.isaBound(2, fn(i, i)))
    let set = try t.intern(.folPred("set", args: [x]))
    _ = try t.intern(.folPred("elem", args: [x, P]))
    _ = try t.intern(.folPred("pmem", args: [x, x, F]))
    _ = try t.intern(.folPred("set", args: [try t.intern(.folBound(0))]))
    #expect(throws: IRRefusal.sourceKindSurvived(x)) { try legalize(set, in: t) }
}

/// The guard writes fol-zfc's binder while variables are still isa's, so `forall_elim` takes them as a predicate does.
@Test func aForallEliminationTakesAVariableOfEveryTermType() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i)), P = try t.intern(.isaBound(1, fn(i, o)))
    let body = try t.intern(.folPred("elem", args: [try t.intern(.isaBound(0, i)), try t.intern(.isaBound(2, fn(i, o)))]))
    let all = try t.intern(.folForall(body: body))
    let atX = try t.intern(.folForallElim(try t.intern(.hyp(0, all)), x))
    #expect(t.conclusion(of: atX) == (try t.intern(.folPred("elem", args: [x, P]))))
    let p = try t.intern(.isaBound(0, o))
    #expect(throws: TableError.propositionAsTerm(p)) { try t.intern(.folForallElim(try t.intern(.hyp(0, all)), p)) }
}

/// S4: a proposition is never reified, so a variable at `o` is no predicate's argument.
@Test func aVariableAtOIsNotAPredicateArgument() throws {
    var t = Table()
    let p = try t.intern(.isaBound(0, o))
    #expect(throws: TableError.propositionAsTerm(p)) {
        try t.intern(.folPred("set", args: [p]))
    }
}

/// The ZF surface: `Collect(A, P)` with `P` η-short is not surface-shaped.
@Test func aFunctionArgumentThatIsNotAnAbstractionIsRefused() throws {
    var t = Table()
    let A = try t.intern(.isaFree(.named("A"), i))
    let P = try t.intern(.isaFree(.named("P"), fn(i, o)))
    #expect(throws: TableError.functionArgumentNotAbstraction(P)) {
        try t.intern(.isaConst(collect, fn(i, fn(fn(i, o), i)), args: [A, P]))
    }
}

@Test func aPartialApplicationIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    #expect(throws: TableError.arityMismatch(expected: 2, found: 1)) {
        try t.intern(.isaConst(qpair, fn(i, fn(i, i)), args: [a]))
    }
}

@Test func aNegativeBoundIndexIsRefused() throws {
    var t = Table()
    #expect(throws: TableError.negativeIndex(-1)) { try t.intern(.isaBound(-1, i)) }
    #expect(throws: TableError.negativeIndex(-2)) { try t.intern(.folBound(-2)) }
}

/// A class variable applied, `P(x)`: the head is a variable, never a constant.
@Test func anAppliedHeadThatIsNotAVariableIsRefused() throws {
    var t = Table()
    let a = try t.intern(.isaFree(.named("a"), i))
    let P = try t.intern(.isaFree(.named("P"), fn(i, o)))
    let applied = try t.intern(.isaVarApp(head: P, args: [a]))
    #expect(t.type(of: applied) == o)
    let x = try t.intern(.isaBound(0, i))
    let lambda = try t.intern(.isaAbs(i, body: try t.intern(.isaConst(mem, fn(i, fn(i, o)), args: [x, a]))))
    #expect(throws: TableError.varAppHeadNotVariable(lambda)) {
        try t.intern(.isaVarApp(head: lambda, args: [a]))
    }
}

/// The guard of a variable concludes the formula it carries, as a hypothesis does; IR knows no guard.
@Test func theGuardOfAVariableConcludesItsFormula() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let set = try t.intern(.folPred("set", args: [x]))
    let g = try t.intern(.isaGuard(x, set))
    #expect(t.conclusion(of: g) == set)
    let a = try t.intern(.isaConst(.declared("a"), i, args: []))
    #expect(throws: TableError.notATermVariable(a)) { try t.intern(.isaGuard(a, set)) }
    #expect(throws: TableError.childType(expected: o, found: i)) { try t.intern(.isaGuard(x, x)) }
}
