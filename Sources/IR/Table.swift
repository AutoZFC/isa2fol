@frozen public enum TableError: Error, Equatable, Sendable {
    case unknownNode(NodeID)
    case negativeIndex(Int)
    case childType(expected: IRType, found: IRType)
    case predicateArgumentNotVariable(NodeID)
    case functionArgumentNotAbstraction(NodeID)
    case arityMismatch(expected: Int, found: Int)
    case varAppHeadNotVariable(NodeID)
}

public struct Table: Sendable {
    private var nodes: [Node] = []
    private var types: [IRType] = []
    private var loose: [Int] = []
    private var index: [Node: NodeID] = [:]

    public init() {}

    public subscript(_ id: NodeID) -> Node { nodes[Int(id.raw)] }
    public func type(of id: NodeID) -> IRType { types[Int(id.raw)] }
    public func looseBound(of id: NodeID) -> Int { loose[Int(id.raw)] }

    public mutating func intern(_ n: Node) throws -> NodeID {
        if let id = index[n] { return id }
        try n.forEachChild { c, _ in
            guard Int(c.raw) < nodes.count else { throw TableError.unknownNode(c) }
        }
        let type = try typeOf(n)
        var bound = 0
        if let v = n.boundVariable {
            guard v.index >= 0 else { throw TableError.negativeIndex(v.index) }
            bound = v.index + 1
        }
        n.forEachChild { c, under in bound = max(bound, looseBound(of: c) - (under ? 1 : 0)) }
        let id = NodeID(raw: UInt32(nodes.count))
        nodes.append(n)
        types.append(type)
        loose.append(bound)
        index[n] = id
        return id
    }

    private func typeOf(_ n: Node) throws -> IRType {
        switch n {
        case .folBound:
            return .i
        case let .folPred(_, xs):
            for x in xs {
                guard case .folBound = self[x] else { throw TableError.predicateArgumentNotVariable(x) }
            }
            return .o
        case let .folAnd(a, b), let .folOr(a, b), let .folImplies(a, b), let .folIff(a, b):
            try expect(.o, a)
            try expect(.o, b)
            return .o
        case let .folNot(a), let .folForall(a), let .folExists(a),
             let .ifolAll(_, a), let .ifolEx(_, a):
            try expect(.o, a)
            return .o
        case .folBottom:
            return .o
        case let .isaConst(_, T, xs):
            return try apply(T, xs)
        case let .isaFree(_, T), let .isaBound(_, T):
            return T
        case let .isaVarApp(h, xs):
            if case .isaFree = self[h] { return try apply(type(of: h), xs) }
            if case .isaBound = self[h] { return try apply(type(of: h), xs) }
            throw TableError.varAppHeadNotVariable(h)
        case let .isaAbs(T, b):
            return .fn(T, type(of: b))
        }
    }

    private func expect(_ expected: IRType, _ c: NodeID) throws {
        guard type(of: c) == expected else { throw TableError.childType(expected: expected, found: type(of: c)) }
    }

    private func apply(_ f: IRType, _ xs: [NodeID]) throws -> IRType {
        var result = f
        for x in xs {
            guard case let .fn(domain, codomain) = result else {
                throw TableError.arityMismatch(expected: arity(f), found: xs.count)
            }
            try expect(domain, x)
            if case .fn = domain, !isAbstraction(x) { throw TableError.functionArgumentNotAbstraction(x) }
            result = codomain
        }
        if case .fn = result { throw TableError.arityMismatch(expected: arity(f), found: xs.count) }
        return result
    }

    private func isAbstraction(_ x: NodeID) -> Bool {
        if case .isaAbs = self[x] { return true }
        return false
    }

    private func arity(_ T: IRType) -> Int {
        if case let .fn(_, rest) = T { return 1 + arity(rest) }
        return 0
    }
}
