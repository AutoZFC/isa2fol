import IR

@frozen public enum TruthError: Error, Equatable, Sendable {
    case notPointwise(NodeID)
    case notAFunction(NodeID)
    case bareTruthVariable(NodeID)
}

func propositional(_ T: IRType) -> Bool {
    guard case let .fn(.o, U) = T else { return false }
    return U == .o || propositional(U)
}

private func arguments(_ T: IRType) -> Int {
    guard case let .fn(.o, U) = T else { return 0 }
    return 1 + arguments(U)
}

private let holdsPredicate = Predicate.base("holds")
private let truthPredicate = Predicate.base("truth")

func holds(_ x: NodeID, in t: inout Table) throws -> NodeID { try t.intern(.folPred(holdsPredicate, args: [x])) }
func truth(_ x: NodeID, in t: inout Table) throws -> NodeID { try t.intern(.folPred(truthPredicate, args: [x])) }

struct Truths {
    let base: Base

    func pointwise(_ F: IRType, _ f: NodeID, _ g: NodeID, in t: inout Table) throws -> NodeID {
        guard case let .fn(.o, U) = F else { return try t.equation(F, f, g) }
        let inner = try pointwise(U, try atFresh(f, in: &t), try atFresh(g, in: &t), in: &t)
        return try t.intern(.folForall(body: try t.intern(.folImplies(try truth(try t.intern(.folBound(0)), in: &t), inner))))
    }

    func reflexive(_ F: IRType, _ f: NodeID, in t: inout Table) throws -> NodeID {
        guard case let .fn(.o, U) = F else { return try base.instance(.iffRefl, [f], in: &t) }
        let inner = try reflexive(U, try atFresh(f, in: &t), in: &t)
        let premise = try truth(try t.intern(.folBound(0)), in: &t)
        return try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(premise, body: inner))))
    }

    func symmetric(_ F: IRType, _ p: NodeID, in t: inout Table) throws -> NodeID {
        try closed([p], arguments(F), in: &t) { _, hs, vs, ts, t in
            let ab = try eliminated(hs[0], vs, ts, in: &t)
            let (a, b) = try sides(ab, t)
            return try base.applied(.iffSymm, [a, b], [ab], in: &t)
        }
    }

    func transitive(_ F: IRType, _ p: NodeID, _ q: NodeID, in t: inout Table) throws -> NodeID {
        try closed([p, q], arguments(F), in: &t) { _, hs, vs, ts, t in
            let ab = try eliminated(hs[0], vs, ts, in: &t), bc = try eliminated(hs[1], vs, ts, in: &t)
            let (a, b) = try sides(ab, t)
            return try base.applied(.iffTrans, [a, b, try sides(bc, t).right], [ab, bc], in: &t)
        }
    }

    func combination(_ F: IRType, _ p: NodeID, _ q: NodeID, in t: inout Table) throws -> NodeID {
        guard case let .fn(.o, U) = F else { throw TruthError.notAFunction(p) }
        return try closed([p, q], arguments(U), in: &t) { s, hs, vs, ts, t in
            let (a, b) = try sides(hs[1], t), d = s.depth
            guard let stated = t.conclusion(of: hs[0]) else { throw TableError.expectedStep(hs[0]) }
            let fa = try eliminated(try instance(hs[0], at: a, in: &t), vs, ts, in: &t)
            let ga = try sides(fa, t).right, gb = try iff(try atArguments(stated, b, vs, in: &t), t).right
            let congruent = try Replacement(base: base) { _, l, r, inner, t in
                guard l == (try inner.lift(a, from: d, in: &t)), r == (try inner.lift(b, from: d, in: &t)) else { return nil }
                return try inner.hypothesis(1, in: &t)
            }.proof(ga, ga, gb, in: s, &t)
            return try base.applied(.iffTrans, [try sides(fa, t).left, ga, gb], [fa, congruent], in: &t)
        }
    }

    func instance(_ p: NodeID, at a: NodeID, in t: inout Table) throws -> NodeID {
        guard let stated = t.conclusion(of: p), case let .folForall(guarded) = t[stated],
              case let .folImplies(_, phi) = t[guarded] else { throw TruthError.notPointwise(p) }
        let target = try fill(phi, a, in: &t)
        var frame = Frame()
        let hp = frame.assume(stated)
        let (w, h) = try frame.open(try base.instance(.truthEX, [a], in: &t), in: &t)
        let e = try frame.variable(w, in: &t)
        let at = try t.intern(.folImpliesElim(try t.intern(.folForallElim(try frame.hypothesis(hp, in: &t), e)),
                                              try t.intern(.folAndElimL(try frame.hypothesis(h, in: &t)))))
        guard let opened = t.conclusion(of: at) else { throw TableError.expectedStep(at) }
        let (filled, read, d) = (try frame.scope.lift(target, in: &t), try frame.scope.lift(a, in: &t), frame.scope.depth)
        let beta = try Replacement(base: base) { _, l, r, inner, t in
            guard r == (try inner.lift(read, from: d, in: &t)), l == (try holds(try inner.variable(w, in: &t), in: &t)) else {
                return nil
            }
            return try inner.proof(.right(.hypothesis(h)), in: &t)
        }.proof(opened, opened, filled, in: frame.scope, &t)
        let proved = try frame.close(try t.intern(.folIffElimL(beta, at)), in: &t)
        return try t.intern(.folImpliesElim(proved, p))
    }

    private func atFresh(_ f: NodeID, in t: inout Table) throws -> NodeID {
        let lifted = try shift(f, by: 1, in: &t)
        guard case let .isaAbs(.o, body) = t[lifted] else { throw TruthError.notAFunction(f) }
        return try instantiate(body, with: try holds(try t.intern(.folBound(0)), in: &t), in: &t)
    }

    private func atArguments(_ stated: NodeID, _ b: NodeID, _ vs: [NodeID], in t: inout Table) throws -> NodeID {
        guard case let .folForall(guarded) = t[stated], case let .folImplies(_, phi) = t[guarded] else {
            throw TruthError.notPointwise(stated)
        }
        var current = try fill(phi, b, in: &t)
        for v in vs {
            guard case let .folForall(inner) = t[current], case let .folImplies(_, body) = t[inner] else {
                throw TruthError.notPointwise(current)
            }
            current = try instantiate(body, with: v, in: &t)
        }
        return current
    }

    private func eliminated(_ p: NodeID, _ vs: [NodeID], _ ts: [NodeID], in t: inout Table) throws -> NodeID {
        var step = p
        for (v, h) in zip(vs, ts) { step = try t.intern(.folImpliesElim(try t.intern(.folForallElim(step, v)), h)) }
        return step
    }

    private func closed(_ premises: [NodeID], _ n: Int, in t: inout Table,
                        _ body: (Scope, [NodeID], [NodeID], [NodeID], inout Table) throws -> NodeID) throws -> NodeID {
        var frame = Frame(), levels: [Int] = [], fixed: [Int] = [], assumed: [Int] = []
        for p in premises {
            guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
            levels.append(frame.assume(c))
        }
        for _ in 0..<n {
            let w = frame.fix(nil)
            fixed.append(w)
            assumed.append(frame.assume(try truth(try frame.variable(w, in: &t), in: &t)))
        }
        let hs = try levels.map { try frame.hypothesis($0, in: &t) }
        let vs = try fixed.map { try frame.variable($0, in: &t) }
        let ts = try assumed.map { try frame.hypothesis($0, in: &t) }
        var proof = try frame.close(try body(frame.scope, hs, vs, ts, &t), in: &t)
        for p in premises { proof = try t.intern(.folImpliesElim(proof, p)) }
        return proof
    }
}

func fill(_ phi: NodeID, _ a: NodeID, in t: inout Table) throws -> NodeID {
    try transform(phi, Fill(a: a), in: &t)
}

private struct Fill: Rule {
    let a: NodeID

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        if case let .folPred(p, xs) = t[id], p == holdsPredicate, xs.count == 1, case let .folBound(k) = t[xs[0]], k == depth.terms {
            return try shift(a, by: depth.terms, in: &t)
        }
        guard let v = t[id].boundVariable, v.namespace == .term else { return nil }
        guard v.index != depth.terms else { throw TruthError.bareTruthVariable(id) }
        return try t.intern(v.reindexed(v.index - 1))
    }
}
