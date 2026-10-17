@frozen public enum IRType: Hashable, Sendable, CustomStringConvertible {
    case i
    case o
    indirect case fn(IRType, IRType)
    case variable(String)

    public var description: String {
        switch self {
        case .i: return "i"
        case .o: return "o"
        case let .fn(a, b): return "(\(a) => \(b))"
        case let .variable(name): return name
        }
    }

    public var domains: [IRType] {
        guard case let .fn(T, rest) = self else { return [] }
        return [T] + rest.domains
    }
}

public func mentionsTypeVariable(_ T: IRType) -> Bool {
    switch T {
    case .i, .o: return false
    case .variable: return true
    case let .fn(a, b): return mentionsTypeVariable(a) || mentionsTypeVariable(b)
    }
}

public func isObject(_ T: IRType) -> Bool {
    switch T {
    case .i: return true
    case .o, .variable: return false
    case let .fn(a, b): return a == .i && (b == .o || isObject(b))
    }
}

public func result(_ T: IRType) -> IRType {
    guard case let .fn(_, U) = T else { return T }
    return result(U)
}

public func guardPredicate(_ T: IRType) -> Predicate? {
    switch T {
    case .i: return .base("set")
    case .fn: return isObject(T) && result(T) == .i ? .base("function") : nil
    case .o, .variable: return nil
    }
}

public func guarded(_ x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID? {
    guard let p = guardPredicate(T) else { return nil }
    return try t.intern(.folPred(p, args: [x]))
}

public func guardedBody(_ T: IRType, _ body: NodeID, in t: inout Table) throws -> NodeID {
    guard let g = try guarded(try t.intern(.folBound(0)), T, in: &t) else { return body }
    return try t.intern(.folImplies(g, body))
}
