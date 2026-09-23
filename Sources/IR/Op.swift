public enum Dialect: Hashable, Sendable {
    case isa, fol, builtin
}

public enum Binder: Hashable, Sendable {
    case setVar, classVar
}

public enum Op: Hashable, Sendable {
    case isaFree(String)
    case isaAtom(String)
    case isaTrueprop
    case isaImp
    case isaAll(sort: IRType)
    case isaAxiom(String)

    case folVar(String)
    case folPred(String)
    case folImplies
    case folForall(Binder)
    case folUse(String)

    case cast(to: IRType)

    public var dialect: Dialect {
        switch self {
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll, .isaAxiom:
            return .isa
        case .folVar, .folPred, .folImplies, .folForall, .folUse:
            return .fol
        case .cast:
            return .builtin
        }
    }

    /// ⚠ EVIDENCE IS A PROPERTY OF THE OP, NOT A TYPE. Isabelle has no sort for
    /// proofs; a derivation's type is the proposition it proves. This is what
    /// Builder refuses to rewrite.
    public var producesEvidence: Bool {
        switch self {
        case .isaAxiom, .folUse:
            return true
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll,
             .folVar, .folPred, .folImplies, .folForall, .cast:
            return false
        }
    }

    public var arity: Int? {
        switch self {
        case .isaFree, .isaAxiom, .folVar, .folUse: return 0
        case .isaTrueprop, .cast: return 1
        case .isaImp, .folImplies: return 2
        case .isaAll, .folForall: return 0
        case .isaAtom, .folPred: return nil
        }
    }
}
