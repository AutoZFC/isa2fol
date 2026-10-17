import IR

enum Ref: Hashable {
    case outer(NodeID)
    case bound(Int)
}

enum Binder: Hashable {
    case set
    case cls
}

struct Chain {
    init() {
        opened = nil
    }

    init(opened variables: [NodeID], shift: Int) {
        opened = (variables, shift)
    }

    private(set) var binders = [Binder]()
    private(set) var constraints = [NodeID?]()

    mutating func bind(_ b: Binder) -> Ref {
        binders.append(b)
        constraints.append(nil)
        return .bound(binders.count - 1)
    }

    mutating func constrain(_ r: Ref, _ constraint: NodeID) {
        guard case .bound(let k) = r else { return }
        constraints[k] = constraint
    }

    func here(_ r: Ref, in t: inout Table) throws -> NodeID {
        switch (r, opened) {
        case (.outer(let x), let o?): return try shift(x, by: o.shift, in: &t)
        case (.bound(let k), let o?): return o.variables[k]
        case (.outer(let x), nil): return try shift(x, by: binders.count, in: &t)
        case (.bound(let k), nil):
            let d = binders.count - 1 - k
            return try t.intern(binders[k] == .set ? .isaBound(d, .i) : .folBound(d))
        }
    }

    func stated() throws -> [NodeID] {
        try constraints.indices.map { k in
            guard let c = constraints[k] else { throw ChainError.unconstrained(k) }
            return c
        }
    }

    func predicate(_ p: Predicate, _ refs: [Ref], in t: inout Table) throws -> NodeID {
        try t.intern(.folPred(p, args: try refs.map { try here($0, in: &t) }))
    }

    func formula(_ core: NodeID, in t: inout Table) throws -> NodeID {
        try folded(core, in: &t) { b, c, body, t in
            let both = try t.intern(.folAnd(c, body))
            return try t.intern(b == .set ? .ifolEx(.i, body: both) : .folExists(body: both))
        }
    }

    func premises(_ core: NodeID, in t: inout Table) throws -> NodeID {
        try folded(core, in: &t) { b, c, body, t in
            let premised = try t.intern(.folImplies(c, body))
            return try t.intern(b == .set ? .ifolAll(.i, body: premised) : .folForall(body: premised))
        }
    }

    private let opened: (variables: [NodeID], shift: Int)?

    private func folded(
        _ core: NodeID,
        in t: inout Table,
        _ wrap: (Binder, NodeID, NodeID, inout Table) throws -> NodeID,
    ) throws -> NodeID {
        var body = core
        for k in binders.indices.reversed() {
            guard let constraint = constraints[k] else { throw ChainError.unconstrained(k) }
            body = try wrap(binders[k], constraint, body, &t)
        }
        return body
    }
}

@frozen
public enum ChainError: Error, Equatable, Sendable {
    case unconstrained(Int)
}
