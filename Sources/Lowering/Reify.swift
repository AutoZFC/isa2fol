import IR

@frozen public enum ReifyError: Error, Equatable, Sendable {
    case notAnAtom(NodeID)
    case notATerm(NodeID)
    case notAClassArgument(NodeID)
    case noDefinition(String)
    case noProof(String)
}

public struct Reify {
    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch p {
        case let .isaConst(kind, T, _):
            if mentionsTypeVariable(T) { return nil }
            switch kind {
            case .primitive(.zf): return .rule
            case .primitive(.ifol(.eq)): return T == .fn(.i, .fn(.i, .o)) ? .rule : .unbuilt
            case .primitive(.pure): return nil
            case .declared: return .unbuilt
            case let .defined(f, level): return unfolds(f, level) ? nil : namesConstant(T) ? .rule : .unbuilt
            }
        case let .isaVarApp(head: T, _):
            return mentionsTypeVariable(T) ? nil : isObject(T) ? .rule : .unbuilt
        case let .isaAbs(T, body: U):
            return isObject(.fn(T, U)) ? .rule : nil
        case let .isaAllElim(_, T):
            return T != .i && isObject(T) ? .unbuilt : nil
        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaOfClass, .isaAllIntro, .isaReflexive, .isaSymmetric,
             .isaTransitive, .isaCombination, .isaAbstract, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
             .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst:
            return nil
        }
    }

    func after(_ n: Node, was id: NodeID, base: Base, in t: inout Table) throws -> NodeID? {
        if names(Pattern(t[id], in: t)) { return try named(atom: n, in: &t) }
        if case let .isaAllElim(_, a) = t[id], owns(Pattern(t[a], in: t)) == .rule {
            return try TermInstance(base: base).proof(children(n)[0], was: id, in: &t)
        }
        return nil
    }

    func names(_ p: Pattern) -> Bool { owns(p) == .rule && value(p) == .o }

    static func guardPredicate(_ T: IRType) -> Predicate? {
        switch T {
        case .i: return .base("set")
        case .fn: return isObject(T) && result(T) == .i ? .base("function") : nil
        case .o, .variable: return nil
        }
    }

    static func guarded(_ x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID? {
        guard let p = guardPredicate(T) else { return nil }
        return try t.intern(.folPred(p, args: [x]))
    }

}

func named(formula: NodeID, in t: inout Table) throws -> NodeID {
    try transform(formula, Atoms(), in: &t)
}

private struct Atoms: Rule {
    func after(_ n: Node, was id: NodeID, context: Depth, in t: inout Table) throws -> NodeID? {
        Reify().names(Pattern(t[id], in: t)) ? try named(atom: n, in: &t) : nil
    }
}

private func namesConstant(_ T: IRType) -> Bool {
    let domains = T.domains
    return domains.allSatisfy(isObject) && (result(T) == .i || result(T) == .o && !domains.isEmpty)
}

func result(_ T: IRType) -> IRType {
    guard case let .fn(_, U) = T else { return T }
    return result(U)
}

private func value(_ p: Pattern) -> IRType? {
    switch p {
    case let .isaConst(_, T, _), let .isaVarApp(head: T, _): return result(T)
    case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
         .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
         .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
         .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
         .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst:
        return nil
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

/// ⚠ ONE VARIABLE PER OCCURRENCE, NEVER PER DISTINCT TERM: shared per term, the instance of a translation differs from
/// the translation of the instance.
struct Naming {
    var chain: Chain
    let designated: [Int]?
    private(set) var site: (binders: Range<Int>, value: Ref)?

    init(_ chain: Chain = Chain(), designated: [Int]? = nil) {
        self.chain = chain
        self.designated = designated
    }

    mutating func atom(_ n: Node, in t: inout Table) throws -> NodeID {
        switch n {
        case let .isaConst(.primitive(.zf(.mem)), _, args):
            let (a, b) = (try name(args[0], [0], &t), try name(args[1], [1], &t))
            return try chain.predicate(.base("elem"), [a, b], in: &t)
        case let .isaConst(.primitive(.ifol(.eq)), _, args):
            let (a, b) = (try name(args[0], [0], &t), try name(args[1], [1], &t))
            return try chain.predicate(.base("eq"), [a, b], in: &t)
        case let .isaConst(c, T, args):
            let (sets, classes) = try arguments(T, args, [], &t)
            let C = chain.bind(.cls)
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, C], in: &t)
        case let .isaVarApp(P, args):
            let sets = try args.indices.map { try name(args[$0], [$0], &t) }
            let tau = try tupled(sets, &t)
            return try chain.predicate(.base("elem"), [tau, .outer(P)], in: &t)
        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folImplies, .folAnd, .folOr, .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL,
             .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR,
             .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd,
             .folSchemaInst:
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
        case let .isaConst(c, .i, args) where args.isEmpty:
            let v = chain.bind(.set)
            chain.constrain(v, try chain.predicate(.constant(c), [v], in: &t))
            return v
        case let .isaConst(c, T, args):
            let (sets, classes) = try arguments(T, args, path, &t)
            let C = chain.bind(.cls)
            chain.constrain(C, try chain.predicate(.constant(c), [C] + classes, in: &t))
            let tau = try tupled(sets, &t)
            let r = chain.bind(.set)
            chain.constrain(r, try chain.predicate(.base("pmem"), [tau, r, C], in: &t))
            return r
        case let .isaVarApp(f, args):
            let sets = try args.indices.map { try name(args[$0], path + [$0], &t) }
            let tau = try tupled(sets, &t)
            let r = chain.bind(.set)
            chain.constrain(r, try chain.predicate(.base("apply"), [tau, r, .outer(f)], in: &t))
            return r
        case .ifolAll, .ifolEx, .isaFree, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folImplies, .folAnd, .folOr, .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst:
            throw ReifyError.notATerm(x)
        }
    }

    private mutating func nameClass(_ lambda: NodeID, _ path: [Int], _ t: inout Table) throws -> Ref {
        let K = chain.bind(.cls)
        if path == designated { site = (chain.binders.count - 1..<chain.binders.count, K) }
        chain.constrain(K, try classDefinition(try chain.here(.outer(lambda), in: &t), K: try chain.here(K, in: &t), in: &t))
        return K
    }

    private mutating func arguments(_ T: IRType, _ args: [NodeID], _ path: [Int], _ t: inout Table) throws -> ([Ref], [Ref]) {
        let domains = T.domains
        let sets = try args.indices.filter { domains[$0] == .i }.map { try name(args[$0], path + [$0], &t) }
        let classes = try args.indices.filter { domains[$0] != .i }.map { try nameClass(args[$0], path + [$0], &t) }
        return (sets, classes)
    }

    private mutating func tupled(_ sets: [Ref], _ t: inout Table) throws -> Ref {
        let tau = chain.bind(.set)
        chain.constrain(tau, try tuple(try sets.map { try chain.here($0, in: &t) }, try chain.here(tau, in: &t), in: &t))
        return tau
    }
}

func classDefinition(_ lambda: NodeID, K: NodeID, raw: Bool = false, in t: inout Table) throws -> NodeID {
    var n = 0, inner = lambda
    while case let .isaAbs(T, body) = t[inner] {
        guard T == .i else { throw ReifyError.notAClassArgument(lambda) }
        (n, inner) = (n + 1, body)
    }
    guard let U = t.type(of: inner), U == .i || U == .o else { throw ReifyError.notAClassArgument(lambda) }
    let outside = U == .o ? 1 : 2
    var body = try shift(lambda, by: outside, in: &t)
    for _ in 0..<n {
        guard case let .isaAbs(_, b) = t[body] else { throw ReifyError.notAClassArgument(lambda) }
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
    let k = try shift(K, by: outside, in: &t)
    let application = U == .o
        ? try t.intern(.folPred(.base("elem"), args: [try t.intern(.isaBound(0, .i)), k]))
        : try t.intern(.folPred(.base("pmem"), args: [try t.intern(.isaBound(1, .i)), try t.intern(.isaBound(0, .i)), k]))
    var definition = try t.intern(.folIff(application, inside))
    for _ in 0..<outside { definition = try t.intern(.ifolAll(.i, body: definition)) }
    return definition
}

public struct ReifyProver: Prover {
    public let name = "reify"

    public init() {}

    public func owns(_ l: Lemma) -> Owned? { l.request is Existence || l.request is Uniqueness ? .unbuilt : nil }

    public func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        throw ReifyError.noProof(l.name)
    }

    public func defines(_ c: Defined) -> Owned? { unfolds(c.family, c.level) ? nil : .rule }

    public func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        guard let d = definitions.first(where: { $0.constant == c }) else { throw ReifyError.noDefinition(c.name) }
        let predicate = Predicate.constant(.defined(c)), domains = d.type.domains
        guard !domains.isEmpty else {
            let v = try t.intern(.folBound(0))
            let equated = try equation(v, d.definiens, in: &t)
            let valued = try named(atom: t[equated], in: &t)
            return try t.intern(.folForall(body: try t.intern(.folIff(try t.intern(.folPred(predicate, args: [v])), valued))))
        }
        let classes = domains.filter { $0 != .i }, m = domains.count - classes.count, k = classes.count
        var sets = 0, slots = 0
        let arguments = try domains.map { T -> NodeID in
            if T == .i {
                defer { sets += 1 }
                return try t.intern(.isaBound(m - 1 - sets, .i))
            }
            defer { slots += 1 }
            return try t.intern(.isaBound(m + k - 1 - slots, T))
        }
        var lambda = try beta(d.definiens, arguments, in: &t)
        for _ in 0..<m { lambda = try t.intern(.isaAbs(.i, body: lambda)) }
        let parameters = try [t.intern(.folBound(k))] + classes.indices.map { try t.intern(.isaBound(k - 1 - $0, classes[$0])) }
        let defines = try t.intern(.folPred(predicate, args: parameters))
        var root = try t.intern(.folIff(defines, try classDefinition(lambda, K: parameters[0], in: &t)))
        for _ in 0...k { root = try t.intern(.folForall(body: root)) }
        return root
    }
}
