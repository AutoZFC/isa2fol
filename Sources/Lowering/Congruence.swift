import IR

func congruent(_ l: NodeID, _ r: NodeID, _ base: Base, _ equal: (NodeID, NodeID, inout Table) throws -> NodeID,
               _ t: inout Table) throws -> NodeID {
    guard case let .folPred(p, ls) = t[l], case let .folPred(p2, rs) = t[r], p == p2, ls.count == rs.count else {
        throw InstanceError.noCongruence(l)
    }
    var current = ls, joined: NodeID?
    for k in ls.indices where ls[k] != rs[k] {
        var next = current
        next[k] = rs[k]
        let (claim, variables): (BaseStatement, [NodeID])
        switch (p, k) {
        case (.base("elem"), 0): (claim, variables) = (.congElemL, [current[0], next[0], current[1]])
        case (.base("elem"), 1): (claim, variables) = (.congElemR, [current[0], current[1], next[1]])
        case (.base("eq"), 0): (claim, variables) = (.congEqL, [current[0], next[0], current[1]])
        case (.base("eq"), 1): (claim, variables) = (.congEqR, [current[0], current[1], next[1]])
        case (.base("snoc"), 2): (claim, variables) = (.congSnocV, [current[0], current[1], current[2], next[2], current[3]])
        default: throw InstanceError.noCongruence(l)
        }
        let step = try base.claimed(claim, variables, [try equal(ls[k], rs[k], &t)], in: &t)
        if let previous = joined {
            let (a, b, c) = (try t.intern(.folPred(p, args: ls)), try t.intern(.folPred(p, args: current)), try t.intern(.folPred(p, args: next)))
            joined = try base.applied(.iffTrans, [a, b, c], [previous, step], in: &t)
        } else {
            joined = step
        }
        current = next
    }
    guard let joined else { return try base.instance(.iffRefl, [l], in: &t) }
    return joined
}
