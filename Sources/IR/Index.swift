@frozen
public enum IRRefusal: Error, Equatable, Sendable {
    case sourceKindSurvived(NodeID)
    case instantiateType(expected: IRType, found: IRType)
    case notAFreeVariable(NodeID)
    case indexOccurs(NodeID)
}

public func shift(_ id: NodeID, by delta: Int, in t: inout Table) throws -> NodeID {
    try transform(id, Shift(delta: delta), in: &t)
}

public func instantiate(_ body: NodeID, with replacement: NodeID, in t: inout Table) throws -> NodeID {
    guard let found = t.type(of: replacement) else { throw TableError.expectedValue(replacement) }
    return try transform(body, Instantiate(replacement: replacement, type: found), in: &t)
}

public func beta(_ f: NodeID, _ args: [NodeID], in t: inout Table) throws -> NodeID {
    var reduced = f
    for a in args {
        guard case .isaAbs(_, let body) = t[reduced] else { throw TableError.varAppHeadNotVariable(reduced) }
        reduced = try instantiate(body, with: a, in: &t)
    }
    return reduced
}

public func abstract(_ id: NodeID, over frees: [NodeID], in t: inout Table) throws -> NodeID {
    var position = [NodeID: Int]()
    for (p, x) in frees.enumerated() {
        guard case .isaFree = t[x] else { throw IRRefusal.notAFreeVariable(x) }
        position[x] = p
    }
    return try transform(id, Abstract(position: position, count: frees.count), in: &t)
}

public func abstractIndex(_ id: NodeID, _ k: Int, in t: inout Table) throws -> NodeID {
    try transform(id, AbstractIndex(k: k), in: &t)
}

public func unshift(_ id: NodeID, in t: inout Table) throws -> NodeID {
    try transform(id, Unshift(), in: &t)
}

/// ⚠ A FOL-ZFC VARIABLE IS UNTYPED: it takes any term variable, and any variable may be instantiated at it, the node
/// substituted as it is. Retyped instead, one variable would stand in two forms that differ by ID until Fol erases
/// both.
private func isFolVariable(_ id: NodeID, _ t: Table) -> Bool {
    if case .folBound = t[id] { return true }
    return false
}

private func termVariable(_ id: NodeID, _ t: Table) -> (index: Int, reindexed: (Int) -> Node)? {
    guard let v = t[id].boundVariable, v.namespace == .term else { return nil }
    return (v.index, v.reindexed)
}

private struct Shift: Rule {
    let delta: Int

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard let v = termVariable(id, t) else { return nil }
        return try t.intern(v.reindexed(v.index + delta))
    }
}

private struct Instantiate: Rule {
    let replacement: NodeID
    let type: IRType

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard let v = termVariable(id, t) else { return nil }
        if v.index > depth.terms { return try t.intern(v.reindexed(v.index - 1)) }
        guard let expected = t.type(of: id) else { throw TableError.expectedValue(id) }
        guard expected == type || isFolVariable(id, t) || isFolVariable(replacement, t) else {
            throw IRRefusal.instantiateType(expected: expected, found: type)
        }
        return try shift(replacement, by: depth.terms, in: &t)
    }

    func after(_ n: Node, was _: NodeID, context _: Depth, in t: inout Table) throws -> NodeID? {
        if case .folLetter(let head, let args) = n, case .folLetterAbs = t[head] { return try letterBeta(
            head,
            args,
            in: &t,
        ) }
        guard case .isaVarApp(let head, let args) = n, case .isaAbs = t[head] else { return nil }
        return try beta(head, args, in: &t)
    }
}

private func letterBeta(_ f: NodeID, _ args: [NodeID], in t: inout Table) throws -> NodeID {
    var reduced = f
    for a in args {
        guard case .folLetterAbs(let body) = t[reduced] else { throw TableError.letterArity(f) }
        reduced = try instantiate(body, with: a, in: &t)
    }
    return reduced
}

private struct Abstract: Rule {
    let position: [NodeID: Int]
    let count: Int

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if let p = position[id], let T = t.type(of: id) {
            return try t.intern(.isaBound(depth.terms + count - 1 - p, T))
        }
        guard let v = termVariable(id, t), v.index >= depth.terms else { return nil }
        return try t.intern(v.reindexed(v.index + count))
    }
}

private struct AbstractIndex: Rule {
    let k: Int

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard let v = termVariable(id, t) else { return nil }
        if v.index == k + depth.terms { return try t.intern(v.reindexed(depth.terms)) }
        return try t.intern(v.reindexed(v.index + 1))
    }
}

private struct Unshift: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard let v = termVariable(id, t) else { return nil }
        if v.index == depth.terms { throw IRRefusal.indexOccurs(id) }
        return try t.intern(v.reindexed(v.index - 1))
    }
}
