public protocol Rule {
    func apply(_ id: NodeID, depth: Int, in t: inout Table) throws -> NodeID?
}

public func transform(_ root: NodeID, _ rule: Rule, in t: inout Table) throws -> NodeID {
    try visit(root, depth: 0, rule, &t)
}

private func visit(_ id: NodeID, depth: Int, _ rule: Rule, _ t: inout Table) throws -> NodeID {
    if let replaced = try rule.apply(id, depth: depth, in: &t) { return replaced }
    let rebuilt = try t[id].mapChildren { c, under in
        try visit(c, depth: depth + (under ? 1 : 0), rule, &t)
    }
    return try t.intern(rebuilt)
}
