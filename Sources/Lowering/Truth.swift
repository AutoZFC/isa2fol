import IR

@frozen
public enum TruthError: Error, Equatable, Sendable {
    case notPointwise(NodeID)
    case bareTruthVariable(NodeID)
}

private let holdsPredicate = Predicate.base("holds")
private let truthPredicate = Predicate.base("truth")

func holds(_ x: NodeID, in t: inout Table) throws -> NodeID {
    try t.intern(.folPred(holdsPredicate, args: [x]))
}

func truth(_ x: NodeID, in t: inout Table) throws -> NodeID {
    try t.intern(.folPred(truthPredicate, args: [x]))
}

struct Truths {
    let base: Base

    func instance(_ p: NodeID, at a: NodeID, in t: inout Table) throws -> NodeID {
        guard
            let stated = t.conclusion(of: p), case .folForall(let guarded) = t[stated],
            case .folImplies(_, let phi) = t[guarded]
        else { throw TruthError.notPointwise(p) }
        let target = try fill(phi, a, in: &t)
        var frame = Frame()
        let hp = frame.assume(stated)
        let (w, h) = try frame.open(try base.instance(.truthEX, [a], in: &t), in: &t)
        let e = try frame.variable(w, in: &t)
        let at = try t.intern(.folImpliesElim(
            try t.intern(.folForallElim(try frame.hypothesis(hp, in: &t), e)),
            try t.intern(.folAndElimL(try frame.hypothesis(h, in: &t))),
        ))
        guard let opened = t.conclusion(of: at) else { throw TableError.expectedStep(at) }
        let filled = try frame.scope.lift(target, in: &t)
        let read = try frame.scope.lift(a, in: &t)
        let d = frame.scope.depth
        let beta = try Replacement(base: base) { _, l, r, inner, t in
            guard
                r == (try inner.lift(read, from: d, in: &t)),
                l == (try holds(try inner.variable(w, in: &t), in: &t))
            else {
                return nil
            }
            return try inner.proof(.right(.hypothesis(h)), in: &t)
        }.proof(opened, opened, filled, in: frame.scope, &t)
        let proved = try frame.close(try t.intern(.folIffElimL(beta, at)), in: &t)
        return try t.intern(.folImpliesElim(proved, p))
    }
}

func fill(_ phi: NodeID, _ a: NodeID, in t: inout Table) throws -> NodeID {
    try transform(phi, Fill(a: a), in: &t)
}

private struct Fill: Rule {
    let a: NodeID

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        if
            case .folPred(let p, let xs) = t[id], p == holdsPredicate, xs.count == 1, case .folBound(let k) = t[xs[0]],
            k == depth.terms
        {
            return try shift(a, by: depth.terms, in: &t)
        }
        guard let v = t[id].boundVariable, v.namespace == .term else { return nil }
        guard v.index != depth.terms else { throw TruthError.bareTruthVariable(id) }
        return try t.intern(v.reindexed(v.index - 1))
    }
}
