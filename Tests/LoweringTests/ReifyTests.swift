import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private let successor = Defined(.zf, "ZF_Base.succ", .object)
private let small = Defined(.zf, "T.small", .object)
private let collect = Defined(.zf, "T.collect", .object)

/// Isabelle's formulas and the fol-zfc they are named to, spelled as DESIGN §4a "Reify — S1 at the site" spells them.
private struct R {
    init() throws {
        var t = Table()
        base = try LoweringTests.base(in: &t)
        self.t = t
    }

    var t = Table()
    let base: Base

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func x(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, i))
    }

    mutating func mem(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(
            .primitive(.zf(.mem)),
            fn(i, fn(i, o)),
            args: [a, b],
        ))
    }

    mutating func zero() throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.zero)), i, args: []))
    }

    mutating func succ(_ a: NodeID) throws -> NodeID {
        try n(.isaConst(.defined(successor), fn(i, i), args: [a]))
    }

    mutating func lam(_ body: NodeID) throws -> NodeID {
        try n(.isaAbs(i, body: body))
    }

    mutating func c(_ k: Int) throws -> NodeID {
        try n(.folBound(k))
    }

    mutating func p(_ name: String, _ xs: NodeID...) throws -> NodeID {
        try n(.folPred(.base(name), args: xs))
    }

    mutating func k(_ c: Constant, _ xs: NodeID...) throws -> NodeID {
        try n(.folPred(.constant(c), args: xs))
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

    mutating func someClass(_ body: NodeID) throws -> NodeID {
        try n(.folExists(body: body))
    }

    mutating func every(_ body: NodeID) throws -> NodeID {
        try n(.ifolAll(i, body: body))
    }

    /// `⟨a⟩ = τ`, `a` and `τ` the set variables at those indices: `∃e. zero(e) ∧ snoc(e, e, a, τ)`.
    mutating func single(_ a: Int, _ tau: Int) throws -> NodeID {
        try some(try and(try p("zero", try x(0)), try p("snoc", try x(0), try x(0), try x(a + 1), try x(tau + 1))))
    }

    /// `S` the class of `succ` at index `S`: `∃τ. ⟨a⟩ = τ ∧ ∃r. pmem(τ, r, S) ∧ core`, `a` and `S` as they stand
    /// outside.
    mutating func succOf(_ a: Int, _ S: Int, _ core: NodeID) throws -> NodeID {
        try some(try and(
            try single(a + 1, 0),
            try some(try and(try p("pmem", try x(1), try x(0), try c(S + 2)), core)),
        ))
    }

    mutating func logic(_ roots: [NodeID]) throws -> [NodeID] {
        try Logic(base: base).run(roots, [], in: &t)
    }
}

/// Each piece of DESIGN's table, named where it stands, by ID.
@Test
func eachPieceIsNamedWhereItStands() throws {
    var r = try R()
    let x = try r.x(1)
    let y = try r.x(0)
    let eq = try r.n(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [x, y]))
    let atZero = try r.mem(try r.x(0), try r.zero())
    let atSucc = try r.mem(x, try r.succ(y))
    let f = try r.n(.isaBound(2, fn(i, i)))
    let atApplied = try r.mem(x, try r.n(.isaVarApp(head: f, args: [y])))
    let predicate = try r.n(.isaConst(.defined(small), fn(i, o), args: [y]))
    let P = try r.n(.isaBound(1, fn(i, o)))
    let variable = try r.n(.isaVarApp(head: P, args: [y]))
    let out = try r.logic([try r.mem(x, y), eq, atZero, atSucc, atApplied, predicate, variable])
    let namedZero = try r.some(try r.and(
        try r.k(.primitive(.zf(.zero)), try r.x(0)),
        try r.p("elem", try r.x(1), try r.x(0)),
    ))
    let namedSucc = try r.someClass(try r.and(
        try r.k(.defined(successor), try r.c(0)),
        try r.succOf(1, 0, try r.p("elem", try r.x(4), try r.x(0))),
    ))
    let namedApplied = try r.some(try r.and(try r.single(1, 0), try r.some(try r.and(
        try r.p("apply", try r.x(1), try r.x(0), try r.n(.isaBound(4, fn(i, i)))),
        try r.p(
            "elem",
            try r.x(3),
            try r.x(0),
        ),
    ))))
    let namedPredicate = try r.someClass(try r.and(
        try r.k(.defined(small), try r.c(0)),
        try r.some(try r.and(
            try r.single(2, 0),
            try r.p("elem", try r.x(0), try r.c(1)),
        )),
    ))
    let namedVariable = try r.some(try r.and(
        try r.single(1, 0),
        try r.p("elem", try r.x(0), try r.n(.isaBound(2, fn(i, o)))),
    ))
    #expect(out == [
        try r.p("elem", x, y),
        try r.p("eq", x, y),
        namedZero,
        namedSucc,
        namedApplied,
        namedPredicate,
        namedVariable,
    ])
}

/// A λ in a class slot is named where it stands by its definition, its class bound by fol-zfc's own `∃`, before the
/// constant's class.
@Test
func aLambdaInAClassSlotIsNamedByItsDefinition() throws {
    var r = try R()
    let x = try r.x(2)
    let A = try r.x(1)
    let lambda = try r.lam(try r.mem(try r.x(0), try r.x(1)))
    let atom = try r.mem(x, try r.n(.isaConst(.defined(collect), fn(i, fn(fn(i, o), i)), args: [A, lambda])))
    let definition = try r.every(try r.iff(
        try r.p("elem", try r.x(0), try r.c(1)),
        try r.some(try r.and(
            try r.single(0, 1),
            try r.p("elem", try r.x(0), try r.x(3)),
        )),
    ))
    let pmem = try r.p("pmem", try r.x(1), try r.x(0), try r.c(2))
    let value = try r.some(try r.and(
        try r.single(4, 0),
        try r.some(try r.and(pmem, try r.p("elem", try r.x(6), try r.x(0)))),
    ))
    let named = try r.someClass(try r.and(
        definition,
        try r.someClass(try r.and(try r.k(.defined(collect), try r.c(0), try r.c(1)), value)),
    ))
    #expect(try r.logic([atom]) == [named])
}

/// ⚠ One variable per occurrence: `succ(a) ∈ succ(a)` names `succ(a)` twice.
@Test
func oneTermTwiceIsTwoVariables() throws {
    var r = try R()
    let a = try r.x(0)
    let atom = try r.mem(try r.succ(a), try r.succ(a))
    let second = try r.someClass(try r.and(
        try r.k(.defined(successor), try r.c(0)),
        try r.succOf(4, 0, try r.p("elem", try r.x(3), try r.x(0))),
    ))
    let first = try r.someClass(try r.and(try r.k(.defined(successor), try r.c(0)), try r.succOf(1, 0, second)))
    #expect(try r.logic([atom]) == [first])
}

/// Naming is a function of the site: named, then instantiated at a variable, is instantiated, then named.
@Test
func namingCommutesWithAnInstanceAtAVariable() throws {
    var r = try R()
    let body = try r.mem(try r.x(0), try r.succ(try r.x(0)))
    let named = try r.logic([body])[0]
    let y = try r.x(3)
    #expect(try instantiate(named, with: y, in: &r.t) == (try r.logic([try instantiate(body, with: y, in: &r.t)])[0]))
}

/// A predicate's `@def`, a set constant's, and one with a class argument as a parameter outside the tuple.
@Test
func aConstantsDefinitionIsItsClassFromItsDefinition() throws {
    var r = try R()
    let selfMember = Defined(.zf, "T.d", .object)
    let empty = Defined(.zf, "T.e", .object)
    let at = Defined(.zf, "T.f", .object)
    let d = Definition(
        defines: .constant(selfMember),
        type: fn(i, o),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(try r.mem(try r.x(0), try r.x(0))),
    )
    let e = Definition(defines: .constant(empty), type: i, axiomTypes: [], parameters: 0, definiens: try r.zero())
    let P = fn(i, o)
    let applied = try r.n(.isaVarApp(head: try r.n(.isaBound(0, P)), args: [try r.x(1)]))
    let f = Definition(
        defines: .constant(at),
        type: fn(i, fn(P, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(try r.n(.isaAbs(P, body: applied))),
    )
    let prover = ReifyProver(base: r.base)
    let defs = [d, e, f]
    let stated = try [selfMember, empty, at].map { try prover.define($0, defs, in: &r.t) }
    let dDef = try r.n(.folForall(body: try r.iff(try r.k(.defined(selfMember), try r.c(0)), try r.every(try r.iff(
        try r.p("elem", try r.x(0), try r.c(1)),
        try r.some(try r.and(
            try r.single(0, 1),
            try r.p("elem", try r.x(0), try r.x(0)),
        )),
    )))))
    let eDef = try r.n(.folForall(body: try r.iff(
        try r.k(.defined(empty), try r.c(0)),
        try r.some(try r.and(
            try r.k(.primitive(.zf(.zero)), try r.x(0)),
            try r.p("eq", try r.c(1), try r.x(0)),
        )),
    )))
    let named = try r.some(try r.and(try r.single(1, 0), try r.p("elem", try r.x(0), try r.n(.isaBound(3, P)))))
    let fBody = try r.every(try r.iff(
        try r.p("elem", try r.x(0), try r.c(2)),
        try r.some(try r.and(try r.single(0, 1), named)),
    ))
    let fDef = try r.n(.folForall(body: try r.n(.folForall(body: try r.iff(
        try r.k(.defined(at), try r.c(1), try r.n(.isaBound(0, P))),
        fBody,
    )))))
    #expect(stated == [dDef, eDef, fDef])
}

/// The statement of a theorem citing `lem : ⋀x. φ(x)` at a compound term, through Logic and then Fol: each proof
/// concludes
/// its statement by ID at both. Returns Logic's proof.
private func instance(
    _ r: inout R,
    _ phi: NodeID,
    at a: NodeID,
    under binders: [IRType] = [],
) throws -> (NodeID, [NodeID]) {
    let lemRoot = try r.n(.ifolAll(i, body: phi))
    var root = try instantiate(phi, with: a, in: &r.t)
    var proof = try r.n(.isaAllElim(try r.n(.use(.theorem("lem"), [], lemRoot)), a))
    for T in binders.reversed() {
        root = try r.n(.ifolAll(T, body: root))
        proof = try r.n(.isaAllIntro(T, body: proof))
    }
    let lowered = try r.logic([root, proof])
    #expect(r.t.conclusion(of: lowered[1]) == lowered[0])
    #expect(patterns(under: lowered, in: r.t).allSatisfy { Logic(base: r.base).owns($0) == nil })
    let fol = try Fol().run(lowered, [], in: &r.t)
    #expect(r.t.conclusion(of: fol[1]) == fol[0])
    var cited = [NodeID]()
    var seen = Set<NodeID>()
    var work = [lowered[1]]
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case .use(.lemma, _, let root) = r.t[id] { cited.append(root) }
        r.t[id].forEachChild { c, _ in work.append(c) }
    }
    return (lowered[1], cited)
}

/// `lem : ⋀x. x ∈ x` at `succ(0)`: Isabelle's `succ(0) ∈ succ(0)` named, each occurrence converted in turn, citing EX
/// and
/// UNIQ of `succ(0)`.
@Test
func anInstanceAtACompoundTermConcludesIsabellesFormulaNamed() throws {
    var r = try R()
    let phi = try r.mem(try r.x(0), try r.x(0))
    let (_, cited) = try instance(&r, phi, at: try r.succ(try r.zero()))
    let core = try r.p("eq", try r.x(4), try r.x(0))
    let ex = try r.some(try r.some(try r.and(
        try r.k(.primitive(.zf(.zero)), try r.x(0)),
        try r.someClass(try r.and(
            try r.k(.defined(successor), try r.c(0)),
            try r.succOf(1, 0, core),
        )),
    )))
    #expect(cited.count == 2 && cited.contains(ex))
}

/// At an applied function variable, EX and UNIQ are closed over it: their guard `function(f)` is discharged by `f`'s.
@Test
func anInstanceAtAnAppliedFunctionVariableDischargesItsGuard() throws {
    var r = try R()
    let phi = try r.mem(try r.x(0), try r.x(0))
    let applied = try r.n(.isaVarApp(head: try r.n(.isaBound(0, fn(i, i))), args: [try r.zero()]))
    let (_, cited) = try instance(&r, phi, at: applied, under: [fn(i, i)])
    #expect(cited.count == 2)
    #expect(cited.allSatisfy { if case .folForall = r.t[$0] { true } else { false } })
}

/// `lem : ⋀x. 0 ∈ collect(0, λz. z ∈ x)` at `succ(0)`: `x` stands in a λ, whose class is kept, its definition
/// converted.
@Test
func anInstanceInsideALambdaKeepsItsClass() throws {
    var r = try R()
    let lambda = try r.lam(try r.mem(try r.x(0), try r.x(1)))
    let phi = try r.mem(
        try r.zero(),
        try r.n(.isaConst(.defined(collect), fn(i, fn(fn(i, o), i)), args: [try r.zero(), lambda])),
    )
    let (_, cited) = try instance(&r, phi, at: try r.succ(try r.zero()))
    #expect(cited.count == 2)
}
