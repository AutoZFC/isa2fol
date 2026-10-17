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

/// ⚠ A PROOF BUILT OUTSIDE AN ASSUMPTION IS NEVER REUSED INSIDE IT: its hypothesis indices shift, and the table checks no
/// hypothesis against its binder. Rebuild it from its levels at the scope it is used in, or `have` it first.
struct Frame {
    private(set) var scope: Scope
    private var steps: [Step] = []

    private enum Step {
        case forall(IRType?)
        case implies(NodeID)
        case exists(Binder, NodeID)
        case cut(NodeID, NodeID)
    }

    init(_ scope: Scope = Scope()) { self.scope = scope }

    mutating func fix(_ T: IRType?) -> Int {
        steps.append(.forall(T))
        return scope.fix(T)
    }

    mutating func assume(_ formula: NodeID) -> Int {
        steps.append(.implies(formula))
        return scope.assume(formula)
    }

    mutating func have(_ p: NodeID, in t: inout Table) throws -> Int {
        guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        steps.append(.cut(c, p))
        return scope.assume(c)
    }

    mutating func open(_ p: NodeID, in t: inout Table) throws -> (witness: Int, hypothesis: Int) {
        guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        if case let .ifolEx(.i, body) = t[c] {
            steps.append(.exists(.set, p))
            let w = scope.fix(.i)
            return (w, scope.assume(body))
        }
        guard case let .folExists(body) = t[c] else { throw ScopeError.notAChain(p) }
        steps.append(.exists(.cls, p))
        let w = scope.fix(nil)
        return (w, scope.assume(body))
    }

    mutating func open(chain fact: Fact, _ binders: [Binder], in t: inout Table) throws -> Opened {
        var o = Opened(core: fact)
        var current = fact
        for _ in binders {
            let (w, h) = try open(try scope.proof(current, in: &t), in: &t)
            o.witnesses.append(w)
            o.constraints.append(.left(.hypothesis(h)))
            current = .right(.hypothesis(h))
        }
        o.core = current
        return o
    }

    mutating func open(_ p: NodeID, count n: Int, in t: inout Table) throws -> (witnesses: [Int], body: Fact) {
        var witnesses: [Int] = [], current = p, body = Fact.hypothesis(-1)
        for k in 0..<n {
            let (w, h) = try open(current, in: &t)
            witnesses.append(w)
            body = .hypothesis(h)
            if k < n - 1 { current = try scope.hypothesis(h, in: &t) }
        }
        return (witnesses, body)
    }

    func variable(_ level: Int, in t: inout Table) throws -> NodeID { try scope.variable(level, in: &t) }
    func proof(_ f: Fact, in t: inout Table) throws -> NodeID { try scope.proof(f, in: &t) }
    func hypothesis(_ level: Int, in t: inout Table) throws -> NodeID { try scope.hypothesis(level, in: &t) }

    func close(_ body: NodeID, in t: inout Table) throws -> NodeID {
        var proof = body
        for step in steps.reversed() {
            switch step {
            case let .forall(T):
                if let T, T == .i || T == .o { proof = try t.intern(.isaAllIntro(T, body: proof)) } else { proof = try t.intern(.folForallIntro(body: proof)) }
            case let .implies(a): proof = try t.intern(.folImpliesIntro(a, body: proof))
            case let .exists(b, p): proof = try t.intern(b == .set ? .isaExElim(.i, p, body: proof) : .folExistsElim(p, body: proof))
            case let .cut(c, p): proof = try t.intern(.folImpliesElim(try t.intern(.folImpliesIntro(c, body: proof)), p))
            }
        }
        return proof
    }
}

func eliminated(_ p: NodeID, at x: NodeID, in t: inout Table) throws -> NodeID {
    guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
    if case .ifolAll(.i, _) = t[c] { return try t.intern(.isaAllElim(p, x)) }
    guard case .folForall = t[c] else { throw TableError.principalConnective(p) }
    return try t.intern(.folForallElim(p, x))
}

func eliminated(_ p: NodeID, at xs: [NodeID], premises: [NodeID] = [], in t: inout Table) throws -> NodeID {
    var step = p
    for x in xs { step = try eliminated(step, at: x, in: &t) }
    for q in premises { step = try t.intern(.folImpliesElim(step, q)) }
    return step
}
