import IR

@frozen public enum CongruenceError: Error, Equatable, Sendable {
    case noCongruence(NodeID)
}

func congruent(_ l: NodeID, _ r: NodeID, _ base: Base, _ equal: (NodeID, NodeID, inout Table) throws -> NodeID,
               _ t: inout Table) throws -> NodeID {
    guard case let .folPred(p, ls) = t[l], case let .folPred(p2, rs) = t[r], p == p2, ls.count == rs.count else {
        throw CongruenceError.noCongruence(l)
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
        default: throw CongruenceError.noCongruence(l)
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

struct Replacement {
    let base: Base
    let hole: (NodeID, NodeID, NodeID, Scope, inout Table) throws -> NodeID?

    func proof(_ phi: NodeID, _ l: NodeID, _ r: NodeID, in s: Scope, _ t: inout Table) throws -> NodeID {
        if l == r { return try base.instance(.iffRefl, [l], in: &t) }
        if let p = try hole(phi, l, r, s, &t) { return p }
        switch t[phi] {
        case let .folNot(a):
            guard case let .folNot(la) = t[l], case let .folNot(ra) = t[r] else { throw CongruenceError.noCongruence(phi) }
            return try base.applied(.congNot, [la, ra], [try proof(a, la, ra, in: s, &t)], in: &t)
        case .folAnd, .folOr, .folImplies, .folIff:
            guard let (c, a, b) = connective(t[phi]), let (c2, la, lb) = connective(t[l]), let (c3, ra, rb) = connective(t[r]),
                  c == c2, c == c3 else { throw CongruenceError.noCongruence(phi) }
            let left = try proof(a, la, ra, in: s, &t), right = try proof(b, lb, rb, in: s, &t)
            return try base.applied(c, [la, ra, lb, rb], [left, right], in: &t)
        case let .ifolAll(T, body):
            guard T == .o || T == .i, case .ifolAll(T, let lb) = t[l], case .ifolAll(T, let rb) = t[r] else {
                throw CongruenceError.noCongruence(phi)
            }
            if T == .i { return try quantified(.congForall, .i, body, lb, rb, s, &t) }
            var inner = s
            _ = inner.assume(l)
            _ = inner.fix(T)
            let p = try proof(body, lb, rb, in: inner, &t)
            let x = try t.intern(.isaBound(0, T))
            let at = { (side: NodeID, t: inout Table) throws -> NodeID in
                let h = try t.intern(.hyp(0, try shift(side, by: 1, in: &t)))
                return try t.intern(T == .o ? .folSchemaInst(h, x) : .isaAllElim(h, x))
            }
            let forward = try t.intern(.folImpliesIntro(l, body: try t.intern(.isaAllIntro(T, body: try t.intern(.folIffElimL(p, try at(l, &t)))))))
            let backward = try t.intern(.folImpliesIntro(r, body: try t.intern(.isaAllIntro(T, body: try t.intern(.folIffElimR(p, try at(r, &t)))))))
            return try t.intern(.folIffIntro(forward, backward))
        case let .ifolEx(.i, body):
            guard case let .ifolEx(.i, lb) = t[l], case let .ifolEx(.i, rb) = t[r] else { throw CongruenceError.noCongruence(phi) }
            return try quantified(.congExists, .i, body, lb, rb, s, &t)
        case let .folExists(body):
            guard case let .folExists(lb) = t[l], case let .folExists(rb) = t[r] else { throw CongruenceError.noCongruence(phi) }
            return try quantified(.congExistsBare, nil, body, lb, rb, s, &t)
        case let .folForall(body):
            guard case let .folForall(lb) = t[l], case let .folForall(rb) = t[r] else { throw CongruenceError.noCongruence(phi) }
            return try quantified(.congForallBare, nil, body, lb, rb, s, &t)
        case .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaPropAll, .isaPropIntro, .isaPropBound, .folBottom, .folImpliesIntro, .folImpliesElim,
             .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim, .folBound, .folPred,
             .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
             .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
             .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            throw CongruenceError.noCongruence(phi)
        }
    }

    /// ⚠ THE BODY'S EQUIVALENCE IS PROVED ONCE, UNDER ONE VARIABLE, AND THE BINDER'S SCHEMA CARRIES IT: proved in each
    /// direction instead, under each direction's own witness, it is one node the checker derives twice, and twice again
    /// at every binder within (`WF_absolute.rtrancl_alt_FUNC`: 1,238 distinct steps, 3.4·10¹² written).
    private func quantified(_ schema: BaseStatement, _ T: IRType?, _ body: NodeID, _ lb: NodeID, _ rb: NodeID, _ s: Scope,
                            _ t: inout Table) throws -> NodeID {
        var inner = s
        _ = inner.fix(T)
        let p = try proof(body, lb, rb, in: inner, &t)
        let every = try t.intern(T == .i ? .isaAllIntro(.i, body: p) : .folForallIntro(body: p))
        return try base.applied(schema, [try t.intern(.folLetterAbs(body: lb)), try t.intern(.folLetterAbs(body: rb))], [every], in: &t)
    }
}

private func connective(_ n: Node) -> (BaseStatement, NodeID, NodeID)? {
    switch n {
    case let .folAnd(a, b): return (.congAnd, a, b)
    case let .folOr(a, b): return (.congOr, a, b)
    case let .folImplies(a, b): return (.congImp, a, b)
    case let .folIff(a, b): return (.congIff, a, b)
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
         .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaPropAll, .isaPropIntro, .isaPropBound, .folBottom, .folImpliesIntro,
         .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
         .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
         .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
         .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return nil
    }
}
