@frozen public enum Dialect: Hashable, Sendable {
    case isa
    case fol
}

@frozen public enum Pattern: Hashable, Sendable {
    case ifolAll(IRType, body: IRType)
    case ifolEx(IRType, body: IRType)
    case isaConst(ConstantKind, IRType, args: [IRType])
    case isaFree(IRType)
    case isaBound(IRType)
    case isaVarApp(head: IRType, args: [IRType])
    case isaAbs(IRType, body: IRType)
    case isaOfClass(IRType)
    case isaAllIntro(IRType, body: IRType)
    case isaAllElim(IRType, IRType)
    case isaReflexive(IRType)
    case isaSymmetric(IRType, IRType)
    case isaTransitive(IRType, IRType, IRType)
    case isaCombination(IRType, IRType, IRType)
    case isaAbstract(IRType, IRType)
    case isaClassical(IRType, IRType)
    case isaIffReflection(IRType, IRType, IRType)
    case isaDefinition(Family, Level, [IRType], args: [IRType])
    case isaPropAll
    case isaPropIntro
    case isaPropBound

    case folImplies(IRType, IRType)
    case folAnd(IRType, IRType)
    case folOr(IRType, IRType)
    case folIff(IRType, IRType)
    case folBottom
    case folImpliesIntro(IRType, body: IRType)
    case folImpliesElim(IRType, IRType)
    case use(CitedKind, [IRType], IRType)
    case hyp(IRType)
    case folIffIntro(IRType, IRType)
    case folIffElimL(IRType, IRType)
    case folAndIntro(IRType, IRType)
    case folAndElimL(IRType)
    case folAndElimR(IRType)
    case folOrIntroL(IRType, IRType)
    case folOrIntroR(IRType, IRType)
    case folOrElim(IRType, IRType, IRType)
    case folBottomElim(IRType, IRType)

    case isaGuard(IRType, IRType)
    case isaExIntro(IRType, IRType)
    case isaExElim(IRType, IRType, body: IRType)

    case folNot(IRType)
    case folBound
    case folPred(args: [IRType])
    case folForall(body: IRType)
    case folExists(body: IRType)
    case folNotIntro(IRType, body: IRType)
    case folNotElim(IRType, IRType)
    case folIffElimR(IRType, IRType)
    case folForallIntro(body: IRType)
    case folForallElim(IRType, IRType)
    case folExistsIntro(IRType, IRType)
    case folExistsElim(IRType, body: IRType)
    case folClassicalAbsurd(IRType, body: IRType)
    case folSchemaInst(IRType, IRType)
    case folLetterAll(Int, body: IRType)
    case folLetter(args: [IRType])
    case folLetterAbs(body: IRType)

    @frozen public enum ConstantKind: Hashable, Sendable, CustomStringConvertible {
        case primitive(Primitive)
        case defined(Family, Level)
        case declared

        init(_ c: Constant) {
            switch c {
            case let .primitive(p): self = .primitive(p)
            case let .defined(d): self = .defined(d.family, d.level)
            case .declared: self = .declared
            }
        }

        public var description: String {
            switch self {
            case let .primitive(p): return "primitive \(p)"
            case let .defined(f, level): return "defined \(f) \(level)"
            case .declared: return "declared"
            }
        }
    }

    @frozen public enum CitedKind: Hashable, Sendable, CustomStringConvertible {
        case theorem
        case axiom(Axiom)
        case theoryAxiom
        case lemma
        case base
        case definition

        init(_ c: Cited) {
            switch c {
            case .theorem: self = .theorem
            case let .axiom(a): self = .axiom(a)
            case .theoryAxiom: self = .theoryAxiom
            case .lemma: self = .lemma
            case .base: self = .base
            case .definition: self = .definition
            }
        }

        public var description: String {
            switch self {
            case .theorem: return "theorem"
            case let .axiom(a): return "axiom \(a)"
            case .theoryAxiom: return "theory axiom"
            case .lemma: return "lemma"
            case .base: return "base"
            case .definition: return "@def"
            }
        }
    }

    public init(_ n: Node, in t: Table) {
        let T = { (c: NodeID) in t.patternType(of: c) }
        let Ts = { (cs: [NodeID]) in cs.map(T) }
        switch n {
        case let .ifolAll(U, b): self = .ifolAll(U, body: T(b))
        case let .ifolEx(U, b): self = .ifolEx(U, body: T(b))
        case let .isaConst(c, U, xs): self = .isaConst(ConstantKind(c), U, args: Ts(xs))
        case let .isaFree(_, U): self = .isaFree(U)
        case let .isaBound(_, U): self = .isaBound(U)
        case let .isaVarApp(h, xs): self = .isaVarApp(head: T(h), args: Ts(xs))
        case let .isaAbs(U, b): self = .isaAbs(U, body: T(b))
        case let .isaOfClass(U, _): self = .isaOfClass(U)
        case let .isaAllIntro(U, b): self = .isaAllIntro(U, body: T(b))
        case let .isaAllElim(p, x): self = .isaAllElim(T(p), T(x))
        case let .isaReflexive(x): self = .isaReflexive(T(x))
        case let .isaSymmetric(U, p): self = .isaSymmetric(U, T(p))
        case let .isaTransitive(U, p, q): self = .isaTransitive(U, T(p), T(q))
        case let .isaCombination(U, p, q): self = .isaCombination(U, T(p), T(q))
        case let .isaAbstract(U, p): self = .isaAbstract(U, T(p))
        case let .isaClassical(a, h): self = .isaClassical(T(a), T(h))
        case let .isaIffReflection(a, b, h): self = .isaIffReflection(T(a), T(b), T(h))
        case let .isaDefinition(_, d, types, _, xs): self = .isaDefinition(d.family, d.level, types, args: Ts(xs))
        case .isaPropAll: self = .isaPropAll
        case .isaPropIntro: self = .isaPropIntro
        case .isaPropBound: self = .isaPropBound

        case let .folImplies(a, b): self = .folImplies(T(a), T(b))
        case let .folAnd(a, b): self = .folAnd(T(a), T(b))
        case let .folOr(a, b): self = .folOr(T(a), T(b))
        case let .folIff(a, b): self = .folIff(T(a), T(b))
        case .folBottom: self = .folBottom
        case let .folImpliesIntro(a, b): self = .folImpliesIntro(T(a), body: T(b))
        case let .folImpliesElim(p, q): self = .folImpliesElim(T(p), T(q))
        case let .use(c, types, root): self = .use(CitedKind(c), types, T(root))
        case let .hyp(_, a): self = .hyp(T(a))
        case let .isaGuard(x, g): self = .isaGuard(T(x), T(g))
        case let .isaExIntro(p, v): self = .isaExIntro(T(p), T(v))
        case let .isaExElim(U, p, b): self = .isaExElim(U, T(p), body: T(b))

        case let .folNot(a): self = .folNot(T(a))
        case .folBound: self = .folBound
        case let .folPred(_, xs): self = .folPred(args: Ts(xs))
        case let .folForall(b): self = .folForall(body: T(b))
        case let .folExists(b): self = .folExists(body: T(b))
        case let .folAndIntro(p, q): self = .folAndIntro(T(p), T(q))
        case let .folAndElimL(p): self = .folAndElimL(T(p))
        case let .folAndElimR(p): self = .folAndElimR(T(p))
        case let .folOrIntroL(p, b): self = .folOrIntroL(T(p), T(b))
        case let .folOrIntroR(a, q): self = .folOrIntroR(T(a), T(q))
        case let .folOrElim(p, q, r): self = .folOrElim(T(p), T(q), T(r))
        case let .folNotIntro(a, b): self = .folNotIntro(T(a), body: T(b))
        case let .folNotElim(p, q): self = .folNotElim(T(p), T(q))
        case let .folIffIntro(p, q): self = .folIffIntro(T(p), T(q))
        case let .folIffElimL(p, q): self = .folIffElimL(T(p), T(q))
        case let .folIffElimR(p, q): self = .folIffElimR(T(p), T(q))
        case let .folForallIntro(b): self = .folForallIntro(body: T(b))
        case let .folForallElim(p, v): self = .folForallElim(T(p), T(v))
        case let .folExistsIntro(p, v): self = .folExistsIntro(T(p), T(v))
        case let .folExistsElim(p, b): self = .folExistsElim(T(p), body: T(b))
        case let .folBottomElim(p, c): self = .folBottomElim(T(p), T(c))
        case let .folClassicalAbsurd(a, b): self = .folClassicalAbsurd(T(a), body: T(b))
        case let .folSchemaInst(p, a): self = .folSchemaInst(T(p), T(a))
        case let .folLetterAll(k, b): self = .folLetterAll(k, body: T(b))
        case let .folLetter(_, xs): self = .folLetter(args: Ts(xs))
        case let .folLetterAbs(b): self = .folLetterAbs(body: T(b))
        }
    }
}

extension Pattern {
    public var dialects: Set<Dialect> {
        switch self {
        case let .ifolAll(T, _), let .isaAllIntro(T, _), let .isaBound(T):
            return T == .o ? [.isa, .fol] : [.isa]
        case .ifolEx, .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaAllElim, .isaGuard, .isaExIntro, .isaExElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition,
             .isaPropAll, .isaPropIntro, .isaPropBound:
            return [.isa]
        case let .use(kind, types, _):
            switch kind {
            case .theorem, .lemma, .definition: return types.isEmpty ? [.isa, .fol] : [.isa]
            case .axiom, .theoryAxiom: return [.isa]
            case .base: return [.fol]
            }
        case .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .hyp, .folIffIntro,
             .folIffElimL, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folBottomElim:
            return [.isa, .fol]
        case .folNot, .folBound, .folPred, .folForall, .folExists, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
             .folLetterAbs:
            return [.fol]
        }
    }
}

public func patterns(under roots: [NodeID], in t: Table) -> Set<Pattern> {
    var seen: Set<NodeID> = [], found: Set<Pattern> = [], work = roots
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        found.insert(Pattern(t[id], in: t))
        t[id].forEachChild { c, _ in work.append(c) }
    }
    return found
}
