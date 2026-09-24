public enum Binder: Hashable, Sendable, CustomStringConvertible {
    case setVar, classVar
    public var description: String { self == .setVar ? "setVar" : "classVar" }
}

public enum Op: Hashable, Sendable {
    case blockArg(Int, IRType)

    case isaFree(String, IRType)
    case isaAtom(String, [OpID])
    case isaTrueprop(OpID)
    case isaImp(OpID, OpID)
    case isaAll(IRType, RegionID)

    case folVar(String)
    case folPred(String, [OpID])
    case folImplies(OpID, OpID)
    case folForall(Binder, RegionID)

    public var type: IRType {
        switch self {
        case let .blockArg(_, t), let .isaFree(_, t): return t
        case .isaAtom, .folPred, .folImplies, .folForall: return .o
        case .isaTrueprop, .isaImp, .isaAll: return .prop
        case .folVar: return .i
        }
    }

    public var region: RegionID? {
        switch self {
        case let .isaAll(_, r), let .folForall(_, r): return r
        case .blockArg, .isaFree, .isaAtom, .isaTrueprop, .isaImp,
             .folVar, .folPred, .folImplies: return nil
        }
    }

    public func forEachOperand(_ body: (OpID) -> Void) {
        switch self {
        case .blockArg, .isaFree, .folVar, .isaAll, .folForall:
            return
        case let .isaTrueprop(a):
            body(a)
        case let .isaImp(a, b), let .folImplies(a, b):
            body(a); body(b)
        case let .isaAtom(_, xs), let .folPred(_, xs):
            xs.forEach(body)
        }
    }

    public func mapOperands(_ f: (OpID) -> OpID) -> Op {
        switch self {
        case .blockArg, .isaFree, .folVar, .isaAll, .folForall:
            return self
        case let .isaTrueprop(a): return .isaTrueprop(f(a))
        case let .isaImp(a, b): return .isaImp(f(a), f(b))
        case let .folImplies(a, b): return .folImplies(f(a), f(b))
        case let .isaAtom(n, xs): return .isaAtom(n, xs.map(f))
        case let .folPred(n, xs): return .folPred(n, xs.map(f))
        }
    }

    public func references(_ v: OpID) -> Bool {
        var hit = false
        forEachOperand { if $0 == v { hit = true } }
        return hit
    }
}
