public enum Dialect: Hashable, Sendable {
    case isa, fol, builtin
}

public enum Binder: Hashable, Sendable {
    case setVar, classVar
}

public enum Op: Hashable, Sendable {
    case blockArg(Int, IRType)

    case isaFree(String, IRType)
    case isaAtom(String, [OpID])
    case isaTrueprop(OpID)
    case isaImp(OpID, OpID)
    case isaAll(IRType, RegionID)
    case isaAxiom(String)

    case folVar(String)
    case folPred(String, [OpID])
    case folImplies(OpID, OpID)
    case folForall(Binder, RegionID)
    case folUse(String)

    case cast(OpID, IRType)

    public var dialect: Dialect {
        switch self {
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll, .isaAxiom:
            return .isa
        case .folVar, .folPred, .folImplies, .folForall, .folUse:
            return .fol
        case .blockArg, .cast:
            return .builtin
        }
    }

    public var type: IRType {
        switch self {
        case let .blockArg(_, t), let .isaFree(_, t), let .cast(_, t): return t
        case .isaAtom, .folPred, .folImplies, .folForall: return .o
        case .isaTrueprop, .isaImp, .isaAll, .isaAxiom: return .prop
        case .folVar: return .i
        case .folUse: return .o
        }
    }

    public var producesEvidence: Bool {
        switch self {
        case .isaAxiom, .folUse: return true
        case .blockArg, .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll,
             .folVar, .folPred, .folImplies, .folForall, .cast: return false
        }
    }

    public var operands: [OpID] {
        switch self {
        case .blockArg, .isaFree, .isaAxiom, .folVar, .folUse, .isaAll, .folForall:
            return []
        case let .isaTrueprop(a), let .cast(a, _):
            return [a]
        case let .isaImp(a, b), let .folImplies(a, b):
            return [a, b]
        case let .isaAtom(_, xs), let .folPred(_, xs):
            return xs
        }
    }

    public var region: RegionID? {
        switch self {
        case let .isaAll(_, r), let .folForall(_, r): return r
        case .blockArg, .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAxiom,
             .folVar, .folPred, .folImplies, .folUse, .cast: return nil
        }
    }

    /// ⚠ `operands` ALLOCATES — even `[a, b]` is a heap array. Use this in any
    /// loop over the whole graph; rebuilding every op was 1.5x the rewrite cost.
    public func references(_ v: OpID) -> Bool {
        switch self {
        case .blockArg, .isaFree, .isaAxiom, .folVar, .folUse, .isaAll, .folForall:
            return false
        case let .isaTrueprop(a), let .cast(a, _):
            return a == v
        case let .isaImp(a, b), let .folImplies(a, b):
            return a == v || b == v
        case let .isaAtom(_, xs), let .folPred(_, xs):
            return xs.contains(v)
        }
    }

    public func substituting(_ f: (OpID) -> OpID) -> Op {
        switch self {
        case .blockArg, .isaFree, .isaAxiom, .folVar, .folUse, .isaAll, .folForall:
            return self
        case let .isaTrueprop(a): return .isaTrueprop(f(a))
        case let .cast(a, t): return .cast(f(a), t)
        case let .isaImp(a, b): return .isaImp(f(a), f(b))
        case let .folImplies(a, b): return .folImplies(f(a), f(b))
        case let .isaAtom(n, xs): return .isaAtom(n, xs.map(f))
        case let .folPred(n, xs): return .folPred(n, xs.map(f))
        }
    }
}
