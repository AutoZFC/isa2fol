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
            case .declared: return .unbuilt
            case .defined(let f, let level): return unfolds(f, level) ? nil : namesConstant(T) ? .rule : .unbuilt
            }

        case .isaVarApp(head: let T, _):
            return mentionsTypeVariable(T) ? nil : isObject(T) ? .rule : .unbuilt

        case .isaAbs(let T, body: let U):
            return isObject(.fn(T, U)) ? .rule : nil

        case .isaAllElim, .ifolAll, .ifolEx, .isaFree, .isaBound, .isaOfClass, .isaAllIntro, .isaReflexive,
             .isaSymmetric,
             .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition,
             .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
             .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst,
             .folLetterAll, .folLetter, .folLetterAbs:
            return nil
        }
    }

    func after(_ n: Node, was id: NodeID, base: Base, in t: inout Table) throws -> NodeID? {
        if names(Pattern(t[id], in: t)) { return try named(atom: n, in: &t) }
        if case .isaAllElim = t[id] { return try instance(children(n)[0], was: id, base: base, in: &t) }
        if case .isaExIntro(_, let a, _) = t[id], owns(Pattern(t[a], in: t)) == .rule {
            return try TermInstance(base: base).witnessed(children(n)[0], body: children(n)[2], was: id, in: &t)
        }
        return nil
    }

    func instance(_ p: NodeID, was id: NodeID, base: Base, in t: inout Table) throws -> NodeID {
        guard case .isaAllElim(_, let a) = t[id] else { throw InstanceError.notAnInstance(id) }
        guard owns(Pattern(t[a], in: t)) == .rule else { return try t.intern(.isaAllElim(p, a)) }
        return try TermInstance(base: base).proof(p, was: id, in: &t)
    }

    func names(_ p: Pattern) -> Bool {
        owns(p) == .rule && value(p) == .o
    }

}

func named(formula: NodeID, in t: inout Table) throws -> NodeID {
    try transform(formula, Atoms(), in: &t)
}

/// ⚠ A TRUTH-SET VARIABLE READS `holds(E)` HERE, AS LOGIC'S WALK READS IT: left as it stands, a λ's class named from a
/// template differs from the walked one, silently, until a step's premise mismatches.
private struct Atoms: Rule {
    func after(_ n: Node, was id: NodeID, context _: Depth, in t: inout Table) throws -> NodeID? {
        if case .isaPropBound(let k) = n { return try holds(try t.intern(.folBound(k)), in: &t) }
        return Reify().names(Pattern(t[id], in: t)) ? try named(atom: n, in: &t) : nil
    }
}

private func namesConstant(_ T: IRType) -> Bool {
    let domains = T.domains
    return domains.allSatisfy(isObject) && (result(T) == .i || result(T) == .o && !domains.isEmpty)
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
         .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst,
         .folLetterAll, .folLetter, .folLetterAbs:
        nil
    }
}

private let equality = IRType.fn(.i, .fn(.i, .o))

func named(atom n: Node, in t: inout Table) throws -> NodeID {
    var naming = Naming()
    let core = try naming.atom(n, in: &t)
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
}

/// ⚠ ONE VARIABLE PER OCCURRENCE, NEVER PER DISTINCT TERM: shared per term, the instance of a translation differs from
/// the translation of the instance.
struct Naming {
    init(_ chain: Chain = Chain(), designated: [Int]? = nil) {
        self.chain = chain
        self.designated = designated
    }

    var chain: Chain
    let designated: [Int]?
    private(set) var site: (binders: Range<Int>, value: Ref)?
    private(set) var pieces = [NamedPiece]()

    mutating func atom(_ n: Node, in t: inout Table) throws -> NodeID {
        switch n {
        case .isaConst(.primitive(.zf(.mem)), _, let args):
            let a = try name(args[0], [0], &t)
            let b = try name(args[1], [1], &t)
            return try chain.predicate(.base("elem"), [a, b], in: &t)

        case .isaConst(.primitive(.ifol(.eq)), _, let args):
            let a = try name(args[0], [0], &t)
            let b = try name(args[1], [1], &t)
            return try chain.predicate(.base("eq"), [a, b], in: &t)

        case .isaConst(let c, let T, let args):
            let (sets, classes) = try arguments(T, args, [], &t)
            let C = bind(.cls, .constantClass(c, T, classes: classes))
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, C], in: &t)

        case .isaVarApp(let P, let args):
            let sets = try args.indices.map { try name(args[$0], [$0], &t) }
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, .outer(P)], in: &t)

        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL,
             .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR,
             .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd,
             .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            throw ReifyError.notAnAtom(try t.intern(n))
        }
    }

    mutating func name(_ x: NodeID, _ path: [Int], _ t: inout Table) throws -> Ref {
        let start = chain.binders.count
        let r = try value(x, path, &t)
        if path == designated { site = (start..<chain.binders.count, r) }
        return r
    }

    private mutating func value(_ x: NodeID, _ path: [Int], _ t: inout Table) throws -> Ref {
        switch t[x] {
        case .isaBound, .folBound:
            return .outer(x)

        case .isaConst(let c, .i, let args) where args.isEmpty:
            let v = bind(.set, .setConstant(c))
            chain.constrain(v, try chain.predicate(.constant(c), [v], in: &t))
            return v

        case .isaConst(let c, let T, let args):
            let (sets, classes) = try arguments(T, args, path, &t)
            let C = bind(.cls, .constantClass(c, T, classes: classes))
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            let r = bind(.set, .value(tuple: tau, cls: C))
            chain.constrain(r, try chain.predicate(.base("pmem"), [tau, r, C], in: &t))
            return r

        case .isaVarApp(let f, let args):
            let sets = try args.indices.map { try name(args[$0], path + [$0], &t) }
            let tau = try tupled(sets, &t)
            let r = bind(.set, .applied(tuple: tau, function: f))
            chain.constrain(r, try chain.predicate(.base("apply"), [tau, r, .outer(f)], in: &t))
            return r

        case .ifolAll, .ifolEx, .isaFree, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst,
             .folLetterAll, .folLetter, .folLetterAbs:
            throw ReifyError.notATerm(x)
        }
    }

    private mutating func nameClass(_ lambda: NodeID, _ path: [Int], _ t: inout Table) throws -> Ref {
        let K = bind(.cls, .lambdaClass(lambda))
        if path == designated { site = (chain.binders.count - 1..<chain.binders.count, K) }
        chain.constrain(
            K,
            try classDefinition(try chain.here(.outer(lambda), in: &t), K: try chain.here(K, in: &t), in: &t),
        )
        return K
    }

    private mutating func arguments(
        _ T: IRType,
        _ args: [NodeID],
        _ path: [Int],
        _ t: inout Table,
    ) throws -> ([Ref], [Ref]) {
        let domains = T.domains
        let sets = try args.indices.filter { domains[$0] == .i }.map { try name(args[$0], path + [$0], &t) }
        let classes = try args.indices.filter { domains[$0] != .i }.map { try nameClass(args[$0], path + [$0], &t) }
        return (sets, classes)
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

func classDefinition(_ lambda: NodeID, K: NodeID, raw: Bool = false, in t: inout Table) throws -> NodeID {
    let (outside, inside) = try classBody(lambda, raw: raw, in: &t)
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

func classBody(_ lambda: NodeID, raw: Bool, in t: inout Table) throws -> (outside: Int, body: NodeID) {
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
    let member: NodeID
    if U == .o {
        member = raw ? body : try named(formula: body, in: &t)
    } else {
        let valued = try equation(try t.intern(.isaBound(n, .i)), body, in: &t)
        member = raw ? valued : try named(atom: t[valued], in: &t)
    }
    let xs = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
    var inside = try t.intern(.folAnd(try tuple(xs, try t.intern(.isaBound(n + outside - 1, .i)), in: &t), member))
    for _ in 0..<n { inside = try t.intern(.ifolEx(.i, body: inside)) }
    return (outside, inside)
}

public struct ReifyProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "reify"

    public func owns(_ l: Lemma) -> Owned? {
        switch l.request {
        case is Existence, is Uniqueness: .rule

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
        in t: inout Table,
    ) throws -> NodeID {
        let proof: NodeID
        switch l.request {
        case let r as Existence: proof = try TermProofs(base: base).existence(r, in: &t)
        case let r as Uniqueness: proof = try TermProofs(base: base).uniqueness(r, in: &t)
        case let f as ConstantFact: proof = try GraphProofs(base: base, definitions: definitions).prove(f, in: &t)
        case let f as LambdaFact: proof = try GraphProofs(base: base, definitions: definitions).prove(f, in: &t)
        default: throw ReifyError.noProof(l.name)
        }
        guard t.conclusion(of: proof) == statement else { throw ReifyError.misproved(l.name) }
        return proof
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
    guard !domains.isEmpty else {
        let v = try t.intern(.folBound(0))
        let equated = try equation(v, d.definiens, in: &t)
        let valued = try named(atom: t[equated], in: &t)
        return try t.intern(.folForall(body: try t.intern(.folIff(
            try t.intern(.folPred(predicate, args: [v])),
            valued,
        ))))
    }
    let classes = domains.filter { $0 != .i }
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
    let m = domains.count(where: { $0 == .i })
    var sets = 0
    var slots = 0
    let arguments = try domains.map { T -> NodeID in
        if T == .i {
            defer { sets += 1 }
            return try t.intern(.isaBound(m - 1 - sets, .i))
        }
        defer { slots += 1 }
        return try shift(classes[slots], by: m, in: &t)
    }
    var lambda = try beta(d.definiens, arguments, in: &t)
    for _ in 0..<m { lambda = try t.intern(.isaAbs(.i, body: lambda)) }
    return lambda
}
