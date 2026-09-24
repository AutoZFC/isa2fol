@frozen public enum IRRefusal: Error, Equatable, Sendable {
    case sourceKindSurvived(NodeID)
    case instantiateType(expected: IRType, found: IRType)
    case notAFreeVariable(NodeID)
}

public func shift(_ id: NodeID, by delta: Int, in t: inout Table) throws -> NodeID {
    try transform(id, Shift(delta: delta), in: &t)
}

public func instantiate(_ body: NodeID, with replacement: NodeID, in t: inout Table) throws -> NodeID {
    try transform(body, Instantiate(replacement: replacement), in: &t)
}

public func abstract(_ id: NodeID, over frees: [NodeID], in t: inout Table) throws -> NodeID {
    var position: [NodeID: Int] = [:]
    for (p, x) in frees.enumerated() {
        guard case .isaFree = t[x] else { throw IRRefusal.notAFreeVariable(x) }
        position[x] = p
    }
    return try transform(id, Abstract(position: position, count: frees.count), in: &t)
}

private struct Shift: Rule {
    let delta: Int
    func apply(_ id: NodeID, depth: Int, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth { return id }
        guard let v = t[id].boundVariable else { return nil }
        return try t.intern(v.reindexed(v.index + delta))
    }
}

private struct Instantiate: Rule {
    let replacement: NodeID
    func apply(_ id: NodeID, depth: Int, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth { return id }
        guard let v = t[id].boundVariable else { return nil }
        if v.index > depth { return try t.intern(v.reindexed(v.index - 1)) }
        guard t.type(of: id) == t.type(of: replacement) else {
            throw IRRefusal.instantiateType(expected: t.type(of: id), found: t.type(of: replacement))
        }
        return try shift(replacement, by: depth, in: &t)
    }
}

private struct Abstract: Rule {
    let position: [NodeID: Int]
    let count: Int
    func apply(_ id: NodeID, depth: Int, in t: inout Table) throws -> NodeID? {
        if let p = position[id] { return try t.intern(.isaBound(depth + count - 1 - p, t.type(of: id))) }
        guard let v = t[id].boundVariable, v.index >= depth else { return nil }
        return try t.intern(v.reindexed(v.index + count))
    }
}
