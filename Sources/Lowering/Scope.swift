import IR

struct Scope {
    private var variables: [IRType?] = []
    private var hypotheses: [(formula: NodeID, depth: Int)] = []

    var depth: Int { variables.count }

    mutating func fix(_ T: IRType?) -> Int {
        variables.append(T)
        return variables.count - 1
    }

    mutating func assume(_ formula: NodeID) -> Int {
        hypotheses.append((formula, depth))
        return hypotheses.count - 1
    }

    func variable(_ level: Int, in t: inout Table) throws -> NodeID {
        let k = depth - 1 - level
        guard let T = variables[level] else { return try t.intern(.folBound(k)) }
        return try t.intern(.isaBound(k, T))
    }

    func hypothesis(_ level: Int, in t: inout Table) throws -> NodeID {
        let h = hypotheses[level]
        return try t.intern(.hyp(hypotheses.count - 1 - level, try shift(h.formula, by: depth - h.depth, in: &t)))
    }

    func lift(_ x: NodeID, from d: Int = 0, in t: inout Table) throws -> NodeID { try shift(x, by: depth - d, in: &t) }

    func proof(_ f: Fact, in t: inout Table) throws -> NodeID {
        switch f {
        case let .hypothesis(level): return try hypothesis(level, in: &t)
        case let .left(g): return try t.intern(.folAndElimL(try proof(g, in: &t)))
        case let .right(g): return try t.intern(.folAndElimR(try proof(g, in: &t)))
        }
    }
}

indirect enum Fact: Hashable {
    case hypothesis(Int)
    case left(Fact)
    case right(Fact)
}

struct Opened {
    var witnesses: [Int] = []
    var constraints: [Fact] = []
    var core: Fact
}

@frozen public enum ScopeError: Error, Equatable, Sendable {
    case notAChain(NodeID)
}

func opening(_ fact: Fact, _ binders: [Binder], in s: Scope, _ t: inout Table,
             _ body: (Scope, Opened, inout Table) throws -> NodeID) throws -> NodeID {
    try opening(fact, binders[...], s, Opened(core: fact), &t, body)
}

private func opening(_ fact: Fact, _ binders: ArraySlice<Binder>, _ s: Scope, _ o: Opened, _ t: inout Table,
                     _ body: (Scope, Opened, inout Table) throws -> NodeID) throws -> NodeID {
    guard let b = binders.first else {
        var o = o
        o.core = fact
        return try body(s, o, &t)
    }
    let p = try s.proof(fact, in: &t)
    let both: NodeID
    switch t.conclusion(of: p).map({ t[$0] }) {
    case let .ifolEx(.i, x)? where b == .set: both = x
    case let .folExists(x)? where b == .cls: both = x
    default: throw ScopeError.notAChain(p)
    }
    var inner = s, o = o
    o.witnesses.append(inner.fix(b == .set ? .i : nil))
    let h = inner.assume(both)
    o.constraints.append(.left(.hypothesis(h)))
    let proved = try opening(.right(.hypothesis(h)), binders.dropFirst(), inner, o, &t, body)
    return try t.intern(b == .set ? .isaExElim(.i, p, body: proved) : .folExistsElim(p, body: proved))
}

func closing(_ binders: [Binder], _ witnesses: [NodeID], _ constraints: [NodeID], _ core: NodeID,
             in t: inout Table) throws -> NodeID {
    var proof = core
    for k in binders.indices.reversed() {
        let both = try t.intern(.folAndIntro(constraints[k], proof))
        proof = try t.intern(binders[k] == .set ? .isaExIntro(both, witnesses[k]) : .folExistsIntro(both, witnesses[k]))
    }
    return proof
}
