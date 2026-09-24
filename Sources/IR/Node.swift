public struct NodeID: Hashable, Sendable, CustomStringConvertible {
    let raw: UInt32
    public var description: String { "%\(raw)" }
}

@frozen public enum Node: Hashable, Sendable {
    case folBound(Int)
    case folPred(String, args: [NodeID])
    case folAnd(NodeID, NodeID)
    case folOr(NodeID, NodeID)
    case folImplies(NodeID, NodeID)
    case folIff(NodeID, NodeID)
    case folNot(NodeID)
    case folBottom
    case folForall(body: NodeID)
    case folExists(body: NodeID)

    case ifolAll(IRType, body: NodeID)
    case ifolEx(IRType, body: NodeID)

    case isaConst(String, IRType, args: [NodeID])
    case isaFree(String, IRType)
    case isaBound(Int, IRType)
    case isaVarApp(head: NodeID, args: [NodeID])
    case isaAbs(IRType, body: NodeID)

    /// ⚠ THE ONLY PLACE THAT SAYS WHICH KINDS BIND. The traversal, the index engine
    /// and `looseBound` all read it here; a second list would let them disagree.
    public func mapChildren(_ f: (NodeID, _ underBinder: Bool) throws -> NodeID) rethrows -> Node {
        switch self {
        case .folBound, .folBottom, .isaFree, .isaBound:
            return self
        case let .folPred(n, xs):
            return .folPred(n, args: try xs.map { try f($0, false) })
        case let .folAnd(a, b): return .folAnd(try f(a, false), try f(b, false))
        case let .folOr(a, b): return .folOr(try f(a, false), try f(b, false))
        case let .folImplies(a, b): return .folImplies(try f(a, false), try f(b, false))
        case let .folIff(a, b): return .folIff(try f(a, false), try f(b, false))
        case let .folNot(a): return .folNot(try f(a, false))
        case let .folForall(b): return .folForall(body: try f(b, true))
        case let .folExists(b): return .folExists(body: try f(b, true))
        case let .ifolAll(T, b): return .ifolAll(T, body: try f(b, true))
        case let .ifolEx(T, b): return .ifolEx(T, body: try f(b, true))
        case let .isaConst(n, T, xs):
            return .isaConst(n, T, args: try xs.map { try f($0, false) })
        case let .isaVarApp(h, xs):
            return .isaVarApp(head: try f(h, false), args: try xs.map { try f($0, false) })
        case let .isaAbs(T, b): return .isaAbs(T, body: try f(b, true))
        }
    }

    public func forEachChild(_ f: (NodeID, _ underBinder: Bool) throws -> Void) rethrows {
        _ = try mapChildren { c, under in try f(c, under); return c }
    }

    public var boundVariable: (index: Int, reindexed: (Int) -> Node)? {
        switch self {
        case let .folBound(k): return (k, { .folBound($0) })
        case let .isaBound(k, T): return (k, { .isaBound($0, T) })
        case .folPred, .folAnd, .folOr, .folImplies, .folIff, .folNot, .folBottom,
             .folForall, .folExists, .ifolAll, .ifolEx, .isaConst, .isaFree,
             .isaVarApp, .isaAbs:
            return nil
        }
    }
}
