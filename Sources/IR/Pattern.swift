@frozen
public enum Dialect: Hashable, Sendable {
    case isa
    case fol
}

@frozen
public enum Pattern: Hashable, Sendable {
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
    case isaHidden(IRType, body: IRType)

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
    case isaExIntro(IRType, IRType, body: IRType)
    case isaExElim(IRType, IRType, body: IRType)
    case value(IRType)
    case valueFact(IRType)
    case valueElim(IRType, IRType, body: IRType)

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
    case folCut(IRType, body: IRType)
    case folClassicalAbsurd(IRType, body: IRType)
    case folSchemaInst(IRType, IRType)
    case folLetterAll(Int, body: IRType)
    case folLetter(args: [IRType])
    case folLetterAbs(body: IRType)

    public init(_ n: Node, in t: Table) {
        let T = { (c: NodeID) in t.patternType(of: c) }
        let Ts = { (cs: [NodeID]) in cs.map(T) }
        switch n {
        case .ifolAll(let U, let b): self = .ifolAll(U, body: T(b))

        case .ifolEx(let U, let b): self = .ifolEx(U, body: T(b))

        case .isaConst(let c, let U, let xs): self = .isaConst(ConstantKind(c), U, args: Ts(xs))

        case .isaFree(_, let U): self = .isaFree(U)

        case .isaBound(_, let U): self = .isaBound(U)

        case .isaVarApp(let h, let xs): self = .isaVarApp(head: T(h), args: Ts(xs))

        case .isaAbs(let U, let b): self = .isaAbs(U, body: T(b))

        case .isaOfClass(let U, _): self = .isaOfClass(U)

        case .isaAllIntro(let U, let b): self = .isaAllIntro(U, body: T(b))

        case .isaAllElim(let p, let x): self = .isaAllElim(T(p), T(x))

        case .isaReflexive(let x): self = .isaReflexive(T(x))

        case .isaSymmetric(let U, let p): self = .isaSymmetric(U, T(p))

        case .isaTransitive(let U, let p, let q): self = .isaTransitive(U, T(p), T(q))

        case .isaCombination(let U, let p, let q): self = .isaCombination(U, T(p), T(q))

        case .isaAbstract(let U, let p): self = .isaAbstract(U, T(p))

        case .isaClassical(let a, let h): self = .isaClassical(T(a), T(h))

        case .isaIffReflection(let a, let b, let h): self = .isaIffReflection(T(a), T(b), T(h))

        case .isaDefinition(_, let d, let types, _, let xs): self = .isaDefinition(
                d.family,
                d.level,
                types,
                args: Ts(xs),
            )

        case .isaPropAll: self = .isaPropAll

        case .isaPropIntro: self = .isaPropIntro

        case .isaPropBound: self = .isaPropBound

        case .isaHidden(let U, let b): self = .isaHidden(U, body: T(b))

        case .folImplies(let a, let b): self = .folImplies(T(a), T(b))

        case .folAnd(let a, let b): self = .folAnd(T(a), T(b))

        case .folOr(let a, let b): self = .folOr(T(a), T(b))

        case .folIff(let a, let b): self = .folIff(T(a), T(b))

        case .folBottom: self = .folBottom

        case .folImpliesIntro(let a, let b): self = .folImpliesIntro(T(a), body: T(b))

        case .folImpliesElim(let p, let q): self = .folImpliesElim(T(p), T(q))

        case .use(let c, let types, let root): self = .use(CitedKind(c), types, T(root))

        case .hyp(_, let a): self = .hyp(T(a))

        case .isaGuard(let x, let g): self = .isaGuard(T(x), T(g))

        case .isaExIntro(let p, let v, let b): self = .isaExIntro(T(p), T(v), body: T(b))

        case .isaExElim(let U, let p, let b): self = .isaExElim(U, T(p), body: T(b))

        case .value(let x): self = .value(T(x))

        case .valueFact(_, let a): self = .valueFact(T(a))

        case .valueElim(let v, let p, let b): self = .valueElim(T(v), T(p), body: T(b))

        case .folNot(let a): self = .folNot(T(a))

        case .folBound: self = .folBound

        case .folPred(_, let xs): self = .folPred(args: Ts(xs))

        case .folForall(let b): self = .folForall(body: T(b))

        case .folExists(let b): self = .folExists(body: T(b))

        case .folAndIntro(let p, let q): self = .folAndIntro(T(p), T(q))

        case .folAndElimL(let p): self = .folAndElimL(T(p))

        case .folAndElimR(let p): self = .folAndElimR(T(p))

        case .folOrIntroL(let p, let b): self = .folOrIntroL(T(p), T(b))

        case .folOrIntroR(let a, let q): self = .folOrIntroR(T(a), T(q))

        case .folOrElim(let p, let q, let r): self = .folOrElim(T(p), T(q), T(r))

        case .folNotIntro(let a, let b): self = .folNotIntro(T(a), body: T(b))

        case .folNotElim(let p, let q): self = .folNotElim(T(p), T(q))

        case .folIffIntro(let p, let q): self = .folIffIntro(T(p), T(q))

        case .folIffElimL(let p, let q): self = .folIffElimL(T(p), T(q))

        case .folIffElimR(let p, let q): self = .folIffElimR(T(p), T(q))

        case .folForallIntro(let b): self = .folForallIntro(body: T(b))

        case .folForallElim(let p, let v): self = .folForallElim(T(p), T(v))

        case .folExistsIntro(let p, let v): self = .folExistsIntro(T(p), T(v))

        case .folExistsElim(let p, let b): self = .folExistsElim(T(p), body: T(b))

        case .folCut(let p, let b): self = .folCut(T(p), body: T(b))

        case .folBottomElim(let p, let c): self = .folBottomElim(T(p), T(c))

        case .folClassicalAbsurd(let a, let b): self = .folClassicalAbsurd(T(a), body: T(b))

        case .folSchemaInst(let p, let a): self = .folSchemaInst(T(p), T(a))

        case .folLetterAll(let k, let b): self = .folLetterAll(k, body: T(b))

        case .folLetter(_, let xs): self = .folLetter(args: Ts(xs))

        case .folLetterAbs(let b): self = .folLetterAbs(body: T(b))
        }
    }

    @frozen
    public enum ConstantKind: Hashable, Sendable, CustomStringConvertible {
        case primitive(Primitive)
        case defined(Family, Level)

        init(_ c: Constant) {
            switch c {
            case .primitive(let p): self = .primitive(p)
            case .defined(let d): self = .defined(d.family, d.level)
            }
        }

        public var description: String {
            switch self {
            case .primitive(let p): "primitive \(p)"
            case .defined(let f, let level): "defined \(f) \(level)"
            }
        }
    }

    @frozen
    public enum CitedKind: Hashable, Sendable, CustomStringConvertible {
        case theorem
        case axiom(Axiom)
        case lemma
        case base
        case definition

        init(_ c: Cited) {
            switch c {
            case .theorem: self = .theorem
            case .axiom(let a): self = .axiom(a)
            case .lemma: self = .lemma
            case .base: self = .base
            case .definition: self = .definition
            }
        }

        public var description: String {
            switch self {
            case .theorem: "theorem"
            case .axiom(let a): "axiom \(a)"
            case .lemma: "lemma"
            case .base: "base"
            case .definition: "@def"
            }
        }
    }

}

extension Pattern {
    public var dialects: Set<Dialect> {
        switch self {
        case .ifolAll(let T, _), .isaAllIntro(let T, _), .isaBound(let T):
            T == .o ? [.isa, .fol] : [.isa]

        case .ifolEx, .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaAllElim, .isaGuard, .isaExIntro,
             .isaExElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition,
             .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden:
            [.isa]

        case .use(let kind, let types, _):
            switch kind {
            case .theorem, .lemma, .definition: types.isEmpty ? [.isa, .fol] : [.isa]
            case .axiom: [.isa]
            case .base: [.fol]
            }

        case .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .hyp, .folIffIntro,
             .folIffElimL, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
             .folBottomElim, .value, .valueFact, .valueElim:
            [.isa, .fol]

        case .folNot, .folBound, .folPred, .folForall, .folExists, .folNotIntro, .folNotElim, .folIffElimR,
             .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folClassicalAbsurd, .folSchemaInst,
             .folLetterAll,
             .folLetter,
             .folLetterAbs:
            [.fol]
        }
    }
}

public func patterns(under roots: [NodeID], in t: Table) -> Set<Pattern> {
    var seen = Set<NodeID>()
    var found = Set<Pattern>()
    var work = roots
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        found.insert(Pattern(t[id], in: t))
        t[id].forEachHeldChild { work.append($0) }
    }
    return found
}
