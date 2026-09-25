public struct Depth: Hashable, Sendable {
    public var terms: Int
    public var hyps: Int

    public init(terms: Int = 0, hyps: Int = 0) {
        self.terms = terms
        self.hyps = hyps
    }
}

public protocol Rule {
    func before(_ id: NodeID, depth: Depth, in t: inout Table) throws -> NodeID?
    func after(_ n: Node, depth: Depth, in t: inout Table) throws -> NodeID?
}

extension Rule {
    public func before(_ id: NodeID, depth: Depth, in t: inout Table) throws -> NodeID? { nil }
    public func after(_ n: Node, depth: Depth, in t: inout Table) throws -> NodeID? { nil }
}

public func transform(_ root: NodeID, _ rule: Rule, in t: inout Table) throws -> NodeID {
    try visit(root, depth: Depth(), rule, &t)
}

private func visit(_ id: NodeID, depth: Depth, _ rule: Rule, _ t: inout Table) throws -> NodeID {
    if let replaced = try rule.before(id, depth: depth, in: &t) { return replaced }
    let rebuilt = try t[id].mapChildren { c, binds in
        try visit(c, depth: Depth(terms: depth.terms + binds.terms, hyps: depth.hyps + binds.hyps), rule, &t)
    }
    if let rewritten = try rule.after(rebuilt, depth: depth, in: &t) { return rewritten }
    return try t.intern(rebuilt)
}
