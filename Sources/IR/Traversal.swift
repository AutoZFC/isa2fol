public struct Depth: Hashable, Sendable {
    public init(terms: Int = 0, hyps: Int = 0) {
        self.terms = terms
        self.hyps = hyps
    }

    public var terms: Int
    public var hyps: Int

}

public protocol Rule {
    associatedtype Context: Hashable = Depth

    var start: Context { get }

    func enter(_ c: Context, _ binder: Node, _ binds: Binds, in t: Table) -> Context
    func narrow(_ c: Context, _ id: NodeID, in t: Table) -> Context
    func before(_ id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
    func after(_ n: Node, was id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
}

extension Rule {
    public func narrow(_ c: Context, _: NodeID, in _: Table) -> Context {
        c
    }

    public func before(_: NodeID, context _: Context, in _: inout Table) throws -> NodeID? {
        nil
    }

    public func after(_: Node, was _: NodeID, context _: Context, in _: inout Table) throws -> NodeID? {
        nil
    }
}

extension Rule where Context == Depth {
    public var start: Depth {
        Depth()
    }

    public func enter(_ c: Depth, _: Node, _ binds: Binds, in _: Table) -> Depth {
        Depth(terms: c.terms + binds.terms, hyps: c.hyps + binds.hyps)
    }
}

private struct Visit<Context: Hashable>: Hashable {
    let id: NodeID
    let context: Context
}

public func transform<R: Rule>(_ roots: [NodeID], _ rule: R, in t: inout Table) throws -> [NodeID] {
    var cache = [Visit<R.Context>: NodeID]()
    return try roots.map { try visit($0, rule.start, rule, &cache, &t) }
}

public func transform(_ root: NodeID, _ rule: some Rule, in t: inout Table) throws -> NodeID {
    try transform([root], rule, in: &t)[0]
}

private func visit<R: Rule>(
    _ id: NodeID,
    _ outer: R.Context,
    _ rule: R,
    _ cache: inout [Visit<R.Context>: NodeID],
    _ t: inout Table,
) throws -> NodeID {
    let key = Visit(id: id, context: rule.narrow(outer, id, in: t))
    if let done = cache[key] { return done }
    let result = try rewrite(id, key.context, rule, &cache, &t)
    cache[key] = result
    return result
}

private func rewrite<R: Rule>(
    _ id: NodeID,
    _ c: R.Context,
    _ rule: R,
    _ cache: inout [Visit<R.Context>: NodeID],
    _ t: inout Table,
) throws -> NodeID {
    if let replaced = try rule.before(id, context: c, in: &t) { return replaced }
    let n = t[id]
    let rebuilt = try n.mapChildren { child, binds in
        let inner = binds == .none ? c : rule.enter(c, n, binds, in: t)
        return try visit(child, inner, rule, &cache, &t)
    }
    if let rewritten = try rule.after(rebuilt, was: id, context: c, in: &t) { return rewritten }
    return try t.intern(rebuilt)
}
