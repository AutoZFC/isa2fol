@frozen
public enum IRType: Hashable, Sendable, CustomStringConvertible {
    case i
    case o
    indirect case fn(IRType, IRType)
    case variable(String)

    public var description: String {
        switch self {
        case .i: "i"
        case .o: "o"
        case .fn(let a, let b): "(\(a) => \(b))"
        case .variable(let name): name
        }
    }

    public var domains: [IRType] {
        guard case .fn(let T, let rest) = self else { return [] }
        return [T] + rest.domains
    }
}

public func mentionsTypeVariable(_ T: IRType) -> Bool {
    switch T {
    case .i, .o: false
    case .variable: true
    case .fn(let a, let b): mentionsTypeVariable(a) || mentionsTypeVariable(b)
    }
}

public func isObject(_ T: IRType) -> Bool {
    switch T {
    case .i: true
    case .o, .variable: false
    case .fn(let a, let b): a == .i && (b == .o || isObject(b))
    }
}

public func takesAFunctionOrProposition(_ T: IRType) -> Bool {
    T.domains.contains { if case .fn = $0 { true } else { $0 == .o } }
}

public func result(_ T: IRType) -> IRType {
    guard case .fn(_, let U) = T else { return T }
    return result(U)
}

public func objectType(_ T: IRType) -> IRType {
    guard case .fn(let A, let B) = T else { return T }
    return .fn(A == .o ? .i : A, objectType(B))
}

public func guardPredicate(_ T: IRType) -> Predicate? {
    switch T {
    case .i: .base("set")
    case .fn: isObject(objectType(T)) && result(T) == .i ? .base("function") : nil
    case .o, .variable: nil
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
