import IR

@frozen
public enum ReifyError: Error, Equatable, Sendable {
    case notAnAtom(NodeID)
    case notATerm(NodeID)
    case notAClassArgument(NodeID)
    case noDefinition(String)
    case noProof(String)
    case misproved(String)
}

public struct Reify {
    public init() { }

    public func owns(_ p: Pattern) -> Owned? {
        switch p {
        case .isaConst(let kind, let T, _):
            if mentionsTypeVariable(T) { return nil }
            switch kind {
            case .primitive(.zf): return .rule
            case .primitive(.ifol(.eq)): return T == .fn(.i, .fn(.i, .o)) ? .rule : .unbuilt
            case .primitive(.pure): return nil
            case .defined(let f, let level): return unfolds(f, level) ? nil : namesConstant(T) ? .rule : .unbuilt
            }

        case .isaVarApp(head: let T, _):
            return mentionsTypeVariable(T) ? nil : isObject(T) ? .rule : .unbuilt

        case .isaAbs(let T, body: let U):
            return isObject(.fn(T, U)) ? .rule : nil

        case .isaDefinition(let f, let level, let types, _):
            return unfolds(f, level) || types.contains(where: mentionsTypeVariable) ? nil : .rule

        case .isaAllElim, .ifolAll, .ifolEx, .isaFree, .isaBound, .isaOfClass, .isaAllIntro, .isaReflexive,
             .isaSymmetric,
             .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
             .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd,
             .folSchemaInst,
             .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
            return nil
        }
    }

    func names(_ p: Pattern) -> Bool {
        owns(p) == .rule && value(p) == .o
    }

}

private func namesConstant(_ T: IRType) -> Bool {
    let domains = T.domains
    return domains.allSatisfy { isObject($0) || $0 == .o } && (result(T) == .i || result(T) == .o)
}

private func value(_ p: Pattern) -> IRType? {
    switch p {
    case .isaConst(_, let T, _), .isaVarApp(head: let T, _): result(T)
    case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
         .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition,
         .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
         .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
         .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
         .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd, .folSchemaInst,
         .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
        nil
    }
}

private let equality = IRType.fn(.i, .fn(.i, .o))

/// Where a formula stands: a statement names every term (S1 at the site); a proof's formula, below `depth` binders of
/// its own, holds the value of each term holding no variable it binds.
/// `naming`: the proof's variables, counted from the formula's root, whose terms are named as the formula's own.
enum Mode: Hashable {
    case statement
    case proof(Int, naming: Set<Int>)

    static func proof(_ d: Int) -> Mode {
        .proof(d, naming: [])
    }

    func deeper(_ k: Int) -> Mode {
        switch self {
        case .statement: .statement
        case .proof(let d, let naming): .proof(d + k, naming: naming)
        }
    }

    func valued(_ x: NodeID, in t: Table) -> Bool {
        guard case .proof(let d, let naming) = self else { return false }
        return looseIndices(x, in: t).allSatisfy { $0 >= d && !naming.contains($0 - d) }
    }
}

func looseIndices(_ x: NodeID, in t: Table) -> Set<Int> {
    var found = Set<Int>()
    var seen = Set<At>()
    var work = [(x, 0)]
    while let (n, d) = work.popLast() {
        guard t.looseBound(of: n) > d, seen.insert(At(node: n, depth: d)).inserted else { continue }
        if let v = t[n].boundVariable, v.namespace == .term {
            if v.index >= d { found.insert(v.index - d) }
            continue
        }
        t[n].forEachChild { c, binds in work.append((c, d + binds.terms)) }
    }
    return found
}

func lowestLoose(_ x: NodeID, in t: Table) -> Int {
    var lowest = Int.max
    var seen = Set<At>()
    var work = [(x, 0)]
    while let (n, d) = work.popLast() {
        guard t.looseBound(of: n) > d, seen.insert(At(node: n, depth: d)).inserted else { continue }
        if let v = t[n].boundVariable, v.namespace == .term {
            if v.index >= d { lowest = min(lowest, v.index - d) }
            continue
        }
        t[n].forEachChild { c, binds in work.append((c, d + binds.terms)) }
    }
    return lowest
}

func named(atom n: Node, mode: Mode = .statement, in t: inout Table) throws -> NodeID {
    var naming = Naming(mode: mode)
    let core = try naming.atom(n, in: &t)
    return try naming.chain.formula(core, in: &t)
}

/// `⟦v = t⟧`: S1's naming of the equation at `t`'s own application, its arguments their values.
func valueFact(_ v: NodeID, in t: inout Table) throws -> NodeID {
    guard case .isaValue(let term) = t[v] else { throw ReifyError.notATerm(v) }
    var naming = Naming(mode: .proof(0))
    let r = try naming.applied(term, &t)
    let core = try naming.chain.predicate(.base("eq"), [.outer(v), r], in: &t)
    return try naming.chain.formula(core, in: &t)
}

func equation(_ a: NodeID, _ b: NodeID, in t: inout Table) throws -> NodeID {
    try t.intern(.isaConst(.primitive(.ifol(.eq)), equality, args: [a, b]))
}

enum NamedPiece: Hashable {
    case setConstant(Constant)
    case constantClass(Constant, IRType, classes: [Ref])
    case lambdaClass(NodeID)
    case tuple([Ref])
    case value(tuple: Ref, cls: Ref)
    case applied(tuple: Ref, function: NodeID)
    case truthSet(NodeID)
}

/// ⚠ ONE VARIABLE PER OCCURRENCE, NEVER PER DISTINCT TERM: shared per term, the instance of a translation differs from
/// the translation of the instance. A proof's value is one per term; the meeting lemmas reconcile the two.
struct Naming {
    init(_ chain: Chain = Chain(), mode: Mode = .statement) {
        self.chain = chain
        self.mode = mode
    }

    var chain: Chain
    let mode: Mode
    private(set) var pieces = [NamedPiece]()
    private(set) var ranges = [(binders: Range<Int>, term: NodeID)]()

    mutating func atom(_ n: Node, in t: inout Table) throws -> NodeID {
        switch n {
        case .isaConst(.primitive(.zf(.mem)), _, let args):
            let a = try name(args[0], &t)
            let b = try name(args[1], &t)
            return try chain.predicate(.base("elem"), [a, b], in: &t)

        case .isaConst(.primitive(.ifol(.eq)), _, let args):
            let a = try name(args[0], &t)
            let b = try name(args[1], &t)
            return try chain.predicate(.base("eq"), [a, b], in: &t)

        case .isaConst(let c, let T, let args):
            let (sets, classes) = try arguments(T, args, &t)
            let C = bind(.cls, .constantClass(c, T, classes: classes))
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, C], in: &t)

        case .isaVarApp(let P, let args):
            let sets = try entries(args, &t)
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, .outer(P)], in: &t)

        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL,
             .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR,
             .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim,
             .folClassicalAbsurd,
             .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
            throw ReifyError.notAnAtom(try t.intern(n))
        }
    }

    mutating func name(_ x: NodeID, _ t: inout Table) throws -> Ref {
        switch t[x] {
        case .isaBound, .folBound, .isaValue:
            return .outer(x)

        case .isaConst, .isaVarApp:
            if mode.valued(x, in: t) { return .outer(try valueNode(x, in: &t)) }
            return try applied(x, &t)

        case .ifolAll, .ifolEx, .isaFree, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd,
             .folSchemaInst,
             .folLetterAll, .folLetter, .folLetterAbs, .isaValueFact:
            throw ReifyError.notATerm(x)
        }
    }

    mutating func applied(_ x: NodeID, _ t: inout Table) throws -> Ref {
        let start = chain.binders.count
        let r = try application(x, &t)
        ranges.append((start..<chain.binders.count, x))
        return r
    }

    private mutating func application(_ x: NodeID, _ t: inout Table) throws -> Ref {
        switch t[x] {
        case .isaConst(let c, .i, let args) where args.isEmpty:
            let v = bind(.set, .setConstant(c))
            chain.constrain(v, try chain.predicate(.constant(c), [v], in: &t))
            return v

        case .isaConst(let c, let T, let args):
            let (sets, classes) = try arguments(T, args, &t)
            let C = bind(.cls, .constantClass(c, T, classes: classes))
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            let r = bind(.set, .value(tuple: tau, cls: C))
            chain.constrain(r, try chain.predicate(.base("pmem"), [tau, r, C], in: &t))
            return r

        case .isaVarApp(let f, let args):
            let sets = try entries(args, &t)
            let tau = try tupled(sets, &t)
            let r = bind(.set, .applied(tuple: tau, function: f))
            chain.constrain(r, try chain.predicate(.base("apply"), [tau, r, .outer(f)], in: &t))
            return r

        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL,
             .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR,
             .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim,
             .folClassicalAbsurd,
             .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
            throw ReifyError.notATerm(x)
        }
    }

    private mutating func nameClass(_ lambda: NodeID, _ t: inout Table) throws -> Ref {
        let K = bind(.cls, .lambdaClass(lambda))
        chain.constrain(
            K,
            try classDefinition(
                try chain.here(.outer(lambda), in: &t),
                K: try chain.here(K, in: &t),
                mode: mode.deeper(chain.binders.count),
                in: &t,
            ),
        )
        return K
    }

    private mutating func arguments(_ T: IRType, _ args: [NodeID], _ t: inout Table) throws -> ([Ref], [Ref]) {
        let domains = T.domains
        let sets = try args.indices.filter { isEntry(domains[$0]) }.map { k in try entry(args[k], domains[k], &t) }
        let classes = try args.indices.filter { !isEntry(domains[$0]) }.map { try nameClass(args[$0], &t) }
        return (sets, classes)
    }

    private mutating func entries(_ args: [NodeID], _ t: inout Table) throws -> [Ref] {
        try args.map { x in
            guard let T = t.type(of: x) else { throw ReifyError.notATerm(x) }
            return try entry(x, T, &t)
        }
    }

    private mutating func entry(_ x: NodeID, _ T: IRType, _ t: inout Table) throws -> Ref {
        guard T == .o else { return try name(x, &t) }
        let read = try formula(x, mode, in: &t)
        let E = bind(.set, .truthSet(x))
        let e = try chain.here(E, in: &t)
        let holding = try t.intern(.folIff(try holds(e, in: &t), try chain.here(.outer(read), in: &t)))
        chain.constrain(E, try t.intern(.folAnd(try truth(e, in: &t), holding)))
        return E
    }

    private mutating func bind(_ b: Binder, _ piece: NamedPiece) -> Ref {
        pieces.append(piece)
        return chain.bind(b)
    }

    private mutating func tupled(_ sets: [Ref], _ t: inout Table) throws -> Ref {
        let tau = bind(.set, .tuple(sets))
        chain.constrain(
            tau,
            try tuple(try sets.map { try chain.here($0, in: &t) }, try chain.here(tau, in: &t), in: &t),
        )
        return tau
    }
}

func classDefinition(
    _ lambda: NodeID,
    K: NodeID,
    raw: Bool = false,
    mode: Mode = .statement,
    in t: inout Table,
) throws -> NodeID {
    let b = try classBody(lambda, raw: raw, mode: mode, in: &t)
    let outside = b.outside
    let inside = b.formula
    let k = try shift(K, by: outside, in: &t)
    let application = outside == 1
        ? try t.intern(.folPred(.base("elem"), args: [try t.intern(.isaBound(0, .i)), k]))
        : try t.intern(.folPred(
            .base("pmem"),
            args: [try t.intern(.isaBound(1, .i)), try t.intern(.isaBound(0, .i)), k],
        ))
    var definition = try t.intern(.folIff(application, inside))
    for _ in 0..<outside { definition = try t.intern(.ifolAll(.i, body: definition)) }
    return definition
}

struct ClassBody {
    let outside: Int
    let arity: Int
    let member: NodeID
    let formula: NodeID
}

func classBody(
    _ lambda: NodeID,
    raw: Bool,
    mode: Mode = .statement,
    in t: inout Table,
) throws -> ClassBody {
    var n = 0
    var inner = lambda
    while case .isaAbs(let T, let body) = t[inner] {
        guard T == .i else { throw ReifyError.notAClassArgument(lambda) }
        (n, inner) = (n + 1, body)
    }
    guard let U = t.type(of: inner), U == .i || U == .o else { throw ReifyError.notAClassArgument(lambda) }
    let outside = U == .o ? 1 : 2
    var body = try shift(lambda, by: outside, in: &t)
    for _ in 0..<n {
        guard case .isaAbs(_, let b) = t[body] else { throw ReifyError.notAClassArgument(lambda) }
        body = b
    }
    let below = mode.deeper(outside + n)
    let member: NodeID
    if U == .o {
        member = raw ? body : try formula(body, below, in: &t)
    } else {
        let valued = try equation(try t.intern(.isaBound(n, .i)), body, in: &t)
        member = raw ? valued : try named(atom: t[valued], mode: below, in: &t)
    }
    let xs = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
    var inside = try t.intern(.folAnd(try tuple(xs, try t.intern(.isaBound(n + outside - 1, .i)), in: &t), member))
    for _ in 0..<n { inside = try t.intern(.ifolEx(.i, body: inside)) }
    return ClassBody(outside: outside, arity: n, member: member, formula: inside)
}

public struct ReifyProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "reify"

    public func owns(_ l: Lemma) -> Owned? {
        switch l.request {
        case is Existence, is Uniqueness: .rule

        case is Unfolding: .rule

        case let f as ConstantFact:
            switch f.fact {
            case .classExists, .lift: nil
            case .existence, .uniqueness, .agreement, .totality, .function: .rule
            }

        case let f as LambdaFact:
            switch f.fact {
            case .classExists, .arguments: nil
            case .function: .rule
            }

        default: nil
        }
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        _: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved {
        let proof: NodeID
        switch l.request {
        case let r as Existence: proof = try TermProofs(base: base).existence(r, in: &t)
        case let r as Uniqueness: proof = try TermProofs(base: base).uniqueness(r, in: &t)
        case let r as Unfolding: proof = try UnfoldingProofs(base: base, definitions: definitions).prove(r, in: &t)
        case let f as ConstantFact: proof = try GraphProofs(base: base, definitions: definitions).prove(f, in: &t)
        case let f as LambdaFact: proof = try GraphProofs(base: base, definitions: definitions).prove(f, in: &t)
        default: throw ReifyError.noProof(l.name)
        }
        guard t.conclusion(of: proof) == statement else { throw ReifyError.misproved(l.name) }
        return .proof(proof)
    }

    public func defines(_ c: Defined) -> Owned? {
        unfolds(c.family, c.level) ? nil : .rule
    }

    public func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        try atDefinition(c, definitions, in: &t)
    }

    let base: Base

}

func atDefinition(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
    guard let d = definitions.first(where: { $0.defines == .constant(c) })
    else { throw ReifyError.noDefinition(c.name) }
    let predicate = Predicate.constant(.defined(c))
    let domains = d.type.domains
    guard d.type != .i else {
        let v = try t.intern(.folBound(0))
        let equated = try equation(v, d.definiens, in: &t)
        let valued = try named(atom: t[equated], in: &t)
        return try t.intern(.folForall(body: try t.intern(.folIff(
            try t.intern(.folPred(predicate, args: [v])),
            valued,
        ))))
    }
    let classes = domains.filter { !isEntry($0) }
    let k = classes.count
    let lambda = try definedLambda(
        d,
        classes: try classes.indices.map { try t.intern(.isaBound(k - 1 - $0, classes[$0])) },
        in: &t,
    )
    let parameters = try [t.intern(.folBound(k))] + classes.indices.map { try t.intern(.isaBound(
        k - 1 - $0,
        classes[$0],
    )) }
    let defines = try t.intern(.folPred(predicate, args: parameters))
    var root = try t.intern(.folIff(defines, try classDefinition(lambda, K: parameters[0], in: &t)))
    for _ in 0...k { root = try t.intern(.folForall(body: root)) }
    return root
}

func definedLambda(_ d: Definition, classes: [NodeID], in t: inout Table) throws -> NodeID {
    let domains = d.type.domains
    let m = domains.count(where: isEntry)
    var sets = 0
    var slots = 0
    let arguments = try domains.map { T -> NodeID in
        if isEntry(T) {
            defer { sets += 1 }
            return try atEntry(T, try t.intern(.isaBound(m - 1 - sets, .i)), in: &t)
        }
        defer { slots += 1 }
        return try shift(classes[slots], by: m, in: &t)
    }
    var lambda = try beta(d.definiens, arguments, in: &t)
    for _ in 0..<m { lambda = try t.intern(.isaAbs(.i, body: lambda)) }
    return lambda
}
