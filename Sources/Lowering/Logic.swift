import IR

@frozen public enum LogicError: Error, Equatable, Sendable {
    case context(NodeID)
    case notCongruence(NodeID)
}

public struct Logic: Pass {
    public let name = "logic"
    let base: Base

    public init(base: Base) { self.base = base }

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .kernel?, .instance?, .equality?, .context?: return .rule
        case .unbuilt?: return .unbuilt
        case nil: return Reify().owns(p)
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, Steps(base: base, equalities: Equalities(base: base)), in: &t)
    }
}

private enum Piece {
    case kernel(Kernel)
    case instance
    case equality(Equality)
    case context
    case unbuilt
}

private enum Kernel {
    case identity, conjI, conjunct1, conjunct2, disjI1, disjI2, disjE, falseE, iffReflection, classical
}

private enum Equality {
    case reflexive, symmetric, transitive, combination
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .use(.axiom(a), types, _):
        guard isLogic(a.family), !types.contains(where: mentionsTypeVariable) else { return nil }
        guard let k = kernel(a) else { return .unbuilt }
        return .kernel(k)
    case let .isaConst(.primitive(.pure(.eq)), T, _):
        return mentionsTypeVariable(T) ? nil : .unbuilt
    case let .isaReflexive(T):
        return equality(T, .reflexive)
    case let .isaSymmetric(T, _):
        return equality(T, .symmetric)
    case let .isaTransitive(T, _, _):
        return equality(T, .transitive)
    case let .isaCombination(F, _, _):
        if mentionsTypeVariable(F) { return nil }
        return ofPropositions(F) ? .equality(.combination) : .unbuilt
    case let .isaAbstract(F, _):
        return mentionsTypeVariable(F) ? nil : .unbuilt
    case let .isaAbs(T, body: U):
        let F = IRType.fn(T, U)
        return ofPropositions(F) ? .context : beyondObjects(F) ? .unbuilt : nil
    case let .isaAllElim(_, T):
        return T == .o ? .instance : beyondObjects(T) ? .unbuilt : nil
    case let .ifolAll(T, _), let .ifolEx(T, _), let .isaAllIntro(T, _):
        return T != .o && beyondObjects(T) ? .unbuilt : nil
    case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaOfClass, .folImplies, .folAnd, .folOr, .folIff,
         .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall,
         .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
         .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
         .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return nil
    }
}

private func equality(_ T: IRType, _ e: Equality) -> Piece? {
    if mentionsTypeVariable(T) { return nil }
    return T == .o || ofPropositions(T) ? .equality(e) : .unbuilt
}

private func ofPropositions(_ T: IRType) -> Bool {
    guard case let .fn(.o, U) = T else { return false }
    return U == .o || ofPropositions(U)
}

private func arity(_ T: IRType) -> Int {
    guard case let .fn(_, U) = T else { return 0 }
    return 1 + arity(U)
}

private func beyondObjects(_ T: IRType) -> Bool { !isObject(T) && !mentionsTypeVariable(T) }

private func kernel(_ a: Axiom) -> Kernel? {
    switch a {
    case .ifol(.impI), .ifol(.mp): return .identity
    case .ifol(.conjI): return .conjI
    case .ifol(.conjunct1): return .conjunct1
    case .ifol(.conjunct2): return .conjunct2
    case .ifol(.disjI1): return .disjI1
    case .ifol(.disjI2): return .disjI2
    case .ifol(.disjE): return .disjE
    case .ifol(.falseE): return .falseE
    case .ifol(.iffReflection): return .iffReflection
    case .ifol(.refl), .ifol(.subst), .ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE), .ifol(.eqReflection): return nil
    case .fol(.classical): return .classical
    case .zf: return nil
    }
}

private struct Steps: Rule {
    let base: Base
    let equalities: Equalities
    var start: Anywhere { Anywhere() }
    func enter(_ c: Anywhere, _ binder: Node, _ binds: Binds, in t: Table) -> Anywhere { c }

    func after(_ n: Node, was id: NodeID, context: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case let .kernel(k)?:
            return try proof(k, in: &t)
        case .instance?:
            let (p, a) = (children(n)[0], children(n)[1])
            if case let .isaAllIntro(_, body) = t[p] { return try instantiate(body, with: a, in: &t) }
            return try t.intern(.folSchemaInst(p, a))
        case let .equality(e)?:
            return try equalities.rewrite(e, n, in: &t)
        case .context?, .unbuilt?:
            return nil
        case nil:
            return try Reify().after(n, was: id, base: base, in: &t)
        }
    }
}

private struct Equalities {
    let base: Base

    func rewrite(_ e: Equality, _ n: Node, in t: inout Table) throws -> NodeID {
        let first = children(n)[0]
        switch e {
        case .reflexive:
            guard case let .isaReflexive(f) = n, let T = t.type(of: f) else { throw LogicError.notCongruence(first) }
            return T == .o ? try base.instance(.iffRefl, [f], in: &t) : try reflexive(f, arity(T), in: &t)
        case .symmetric:
            guard case let .isaSymmetric(T, p) = n else { throw LogicError.notCongruence(first) }
            guard T != .o else { return try base.applied(.iffSymm, try sidesAtO(p, in: t), [p], in: &t) }
            return try symmetric(p, arity(T), in: &t)
        case .transitive:
            guard case let .isaTransitive(T, p, q) = n else { throw LogicError.notCongruence(first) }
            guard T != .o else {
                let ab = try sidesAtO(p, in: t), bc = try sidesAtO(q, in: t)
                return try base.applied(.iffTrans, ab + [bc[1]], [p, q], in: &t)
            }
            return try transitive(p, q, arity(T), in: &t)
        case .combination:
            guard case let .isaCombination(F, p, q) = n else { throw LogicError.notCongruence(first) }
            return try combination(p, q, arity(F), in: &t)
        }
    }

    private func reflexive(_ f: NodeID, _ m: Int, in t: inout Table) throws -> NodeID {
        var phi = f
        for _ in 0..<m {
            guard case let .isaAbs(.o, body) = t[phi] else { throw LogicError.notCongruence(f) }
            phi = body
        }
        let (ps, qs) = try letters(m, in: &t)
        let shifted = try shift(f, by: 2 * m, in: &t)
        let fp = try beta(shifted, ps, in: &t), fq = try beta(shifted, qs, in: &t)
        var s = Scope()
        for k in 0..<m { _ = s.assume(try t.intern(.folIff(ps[k], qs[k]))) }
        let proof = try Replacement(base: base) { phi, _, _, s, t in
            guard case let .isaBound(k, _) = t[phi], (0..<m).contains(k - s.depth) else { return nil }
            return try s.hypothesis(m - 1 - (k - s.depth), in: &t)
        }.proof(phi, fp, fq, in: s, &t)
        return try fixed(2 * m, try assumed(ps, qs, proof, in: &t), in: &t)
    }

    private func combination(_ e: NodeID, _ q: NodeID, _ m: Int, in t: inout Table) throws -> NodeID {
        var rest = try instantiated(e, try sidesAtO(q, in: t), in: &t)
        let remaining = 2 * (m - 1)
        for _ in 0..<remaining {
            guard case let .isaAllIntro(.o, body) = t[rest] else { throw LogicError.notCongruence(e) }
            rest = body
        }
        return try fixed(remaining, try t.intern(.folImpliesElim(rest, try shift(q, by: remaining, in: &t))), in: &t)
    }

    private func symmetric(_ e: NodeID, _ m: Int, in t: inout Table) throws -> NodeID {
        let (ps, qs) = try letters(m, in: &t)
        let swapped = try instantiated(try shift(e, by: 2 * m, in: &t), interleaved(qs, ps), in: &t)
        guard let form = t.conclusion(of: swapped) else { throw LogicError.notCongruence(e) }
        var chain = try t.intern(.hyp(m, form))
        for k in 0..<m {
            let h = try t.intern(.hyp(m - 1 - k, try t.intern(.folIff(ps[k], qs[k]))))
            chain = try t.intern(.folImpliesElim(chain, try base.applied(.iffSymm, [ps[k], qs[k]], [h], in: &t)))
        }
        let turned = try assumed(ps, qs, try base.applied(.iffSymm, try sidesAtO(chain, in: t), [chain], in: &t), in: &t)
        let closed = try t.intern(.folImpliesIntro(form, body: turned))
        return try fixed(2 * m, try t.intern(.folImpliesElim(closed, swapped)), in: &t)
    }

    private func transitive(_ e1: NodeID, _ e2: NodeID, _ m: Int, in t: inout Table) throws -> NodeID {
        let (ps, qs) = try letters(m, in: &t)
        let first = try instantiated(try shift(e1, by: 2 * m, in: &t), interleaved(ps, qs), in: &t)
        let second = try instantiated(try shift(e2, by: 2 * m, in: &t), interleaved(qs, qs), in: &t)
        guard let form1 = t.conclusion(of: first), let form2 = t.conclusion(of: second) else {
            throw LogicError.notCongruence(e1)
        }
        var c1 = try t.intern(.hyp(m + 1, form1)), c2 = try t.intern(.hyp(m, form2))
        for k in 0..<m {
            c1 = try t.intern(.folImpliesElim(c1, try t.intern(.hyp(m - 1 - k, try t.intern(.folIff(ps[k], qs[k]))))))
            c2 = try t.intern(.folImpliesElim(c2, try base.instance(.iffRefl, [qs[k]], in: &t)))
        }
        let fg = try sidesAtO(c1, in: t), gh = try sidesAtO(c2, in: t)
        let joined = try assumed(ps, qs, try base.applied(.iffTrans, fg + [gh[1]], [c1, c2], in: &t), in: &t)
        let closed = try t.intern(.folImpliesIntro(form1, body: try t.intern(.folImpliesIntro(form2, body: joined))))
        return try fixed(2 * m, try t.intern(.folImpliesElim(try t.intern(.folImpliesElim(closed, first)), second)), in: &t)
    }

    private func letters(_ m: Int, in t: inout Table) throws -> ([NodeID], [NodeID]) {
        let ps = try (0..<m).map { try t.intern(.isaBound(2 * (m - 1 - $0) + 1, .o)) }
        let qs = try (0..<m).map { try t.intern(.isaBound(2 * (m - 1 - $0), .o)) }
        return (ps, qs)
    }

    private func assumed(_ ps: [NodeID], _ qs: [NodeID], _ body: NodeID, in t: inout Table) throws -> NodeID {
        var proof = body
        for k in ps.indices.reversed() { proof = try t.intern(.folImpliesIntro(try t.intern(.folIff(ps[k], qs[k])), body: proof)) }
        return proof
    }

    private func instantiated(_ e: NodeID, _ instances: [NodeID], in t: inout Table) throws -> NodeID {
        var proof = e
        for a in instances {
            guard case let .isaAllIntro(.o, body) = t[proof] else { throw LogicError.notCongruence(e) }
            proof = try instantiate(body, with: a, in: &t)
        }
        return proof
    }
}

private func interleaved(_ xs: [NodeID], _ ys: [NodeID]) -> [NodeID] { zip(xs, ys).flatMap { [$0, $1] } }

private func fixed(_ k: Int, _ body: NodeID, in t: inout Table) throws -> NodeID {
    var proof = body
    for _ in 0..<k { proof = try t.intern(.isaAllIntro(.o, body: proof)) }
    return proof
}

private func sidesAtO(_ p: NodeID, in t: Table) throws -> [NodeID] {
    guard let c = t.conclusion(of: p), let (T, a, b) = t.sides(ofEquation: c), T == .o else {
        throw LogicError.notCongruence(p)
    }
    return [a, b]
}

struct Replacement {
    let base: Base
    let hole: (NodeID, NodeID, NodeID, Scope, inout Table) throws -> NodeID?

    func proof(_ phi: NodeID, _ l: NodeID, _ r: NodeID, in s: Scope, _ t: inout Table) throws -> NodeID {
        if l == r { return try base.instance(.iffRefl, [l], in: &t) }
        if let p = try hole(phi, l, r, s, &t) { return p }
        switch t[phi] {
        case let .folNot(a):
            guard case let .folNot(la) = t[l], case let .folNot(ra) = t[r] else { throw LogicError.context(phi) }
            return try base.applied(.congNot, [la, ra], [try proof(a, la, ra, in: s, &t)], in: &t)
        case .folAnd, .folOr, .folImplies, .folIff:
            guard let (c, a, b) = connective(t[phi]), let (c2, la, lb) = connective(t[l]), let (c3, ra, rb) = connective(t[r]),
                  c == c2, c == c3 else { throw LogicError.context(phi) }
            let left = try proof(a, la, ra, in: s, &t), right = try proof(b, lb, rb, in: s, &t)
            return try base.applied(c, [la, ra, lb, rb], [left, right], in: &t)
        case let .ifolAll(T, body):
            guard T == .o || T == .i, case .ifolAll(T, let lb) = t[l], case .ifolAll(T, let rb) = t[r] else {
                throw LogicError.context(phi)
            }
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
            guard case let .ifolEx(.i, lb) = t[l], case let .ifolEx(.i, rb) = t[r] else { throw LogicError.context(phi) }
            var inner = s
            _ = inner.assume(l)
            _ = inner.fix(.i)
            _ = inner.assume(lb)
            let p = try proof(body, lb, rb, in: inner, &t)
            let x = try t.intern(.isaBound(0, .i))
            let forward = try t.intern(.isaExIntro(try t.intern(.folIffElimL(p, try t.intern(.hyp(0, lb)))), x))
            let backward = try t.intern(.isaExIntro(try t.intern(.folIffElimR(p, try t.intern(.hyp(0, rb)))), x))
            let there = try t.intern(.isaExElim(.i, try t.intern(.hyp(0, l)), body: forward))
            let back = try t.intern(.isaExElim(.i, try t.intern(.hyp(0, r)), body: backward))
            return try t.intern(.folIffIntro(try t.intern(.folImpliesIntro(l, body: there)), try t.intern(.folImpliesIntro(r, body: back))))
        case let .folExists(body):
            guard case let .folExists(lb) = t[l], case let .folExists(rb) = t[r] else { throw LogicError.context(phi) }
            var inner = s
            _ = inner.assume(l)
            _ = inner.fix(nil)
            _ = inner.assume(lb)
            let p = try proof(body, lb, rb, in: inner, &t)
            let x = try t.intern(.folBound(0))
            let forward = try t.intern(.folExistsIntro(try t.intern(.folIffElimL(p, try t.intern(.hyp(0, lb)))), x))
            let backward = try t.intern(.folExistsIntro(try t.intern(.folIffElimR(p, try t.intern(.hyp(0, rb)))), x))
            let there = try t.intern(.folExistsElim(try t.intern(.hyp(0, l)), body: forward))
            let back = try t.intern(.folExistsElim(try t.intern(.hyp(0, r)), body: backward))
            return try t.intern(.folIffIntro(try t.intern(.folImpliesIntro(l, body: there)), try t.intern(.folImpliesIntro(r, body: back))))
        case let .folForall(body):
            guard case let .folForall(lb) = t[l], case let .folForall(rb) = t[r] else { throw LogicError.context(phi) }
            var inner = s
            _ = inner.assume(l)
            _ = inner.fix(nil)
            let p = try proof(body, lb, rb, in: inner, &t)
            let x = try t.intern(.folBound(0))
            let at = { (side: NodeID, t: inout Table) throws -> NodeID in
                try t.intern(.folForallElim(try t.intern(.hyp(0, try shift(side, by: 1, in: &t))), x))
            }
            let forward = try t.intern(.folImpliesIntro(l, body: try t.intern(.folForallIntro(body: try t.intern(.folIffElimL(p, try at(l, &t)))))))
            let backward = try t.intern(.folImpliesIntro(r, body: try t.intern(.folForallIntro(body: try t.intern(.folIffElimR(p, try at(r, &t)))))))
            return try t.intern(.folIffIntro(forward, backward))
        case .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folBottom, .folImpliesIntro, .folImpliesElim,
             .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim, .folBound, .folPred,
             .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
             .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
             .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            throw LogicError.context(phi)
        }
    }
}

private func connective(_ n: Node) -> (BaseStatement, NodeID, NodeID)? {
    switch n {
    case let .folAnd(a, b): return (.congAnd, a, b)
    case let .folOr(a, b): return (.congOr, a, b)
    case let .folImplies(a, b): return (.congImp, a, b)
    case let .folIff(a, b): return (.congIff, a, b)
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
         .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folBottom, .folImpliesIntro,
         .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
         .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
         .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
         .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return nil
    }
}

private func proof(_ k: Kernel, in t: inout Table) throws -> NodeID {
    func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, .o)) }
    func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
    func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folIff(a, b)) }
    func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID { try n(.folImpliesIntro(a, body: body)) }
    func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try n(.hyp(k, a)) }
    let letters: Int, body: NodeID
    switch k {
    case .identity:
        let h = try imp(try v(1), try v(0))
        (letters, body) = (2, try assume(h, try hyp(0, h)))
    case .conjI:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(p, try assume(q, try n(.folAndIntro(try hyp(1, p), try hyp(0, q))))))
    case .conjunct1:
        let h = try n(.folAnd(try v(1), try v(0)))
        (letters, body) = (2, try assume(h, try n(.folAndElimL(try hyp(0, h)))))
    case .conjunct2:
        let h = try n(.folAnd(try v(1), try v(0)))
        (letters, body) = (2, try assume(h, try n(.folAndElimR(try hyp(0, h)))))
    case .disjI1:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(p, try n(.folOrIntroL(try hyp(0, p), q))))
    case .disjI2:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(q, try n(.folOrIntroR(p, try hyp(0, q)))))
    case .disjE:
        let (p, q, r) = (try v(2), try v(1), try v(0))
        let either = try n(.folOr(p, q)), fromP = try imp(p, r), fromQ = try imp(q, r)
        let cases = try n(.folOrElim(try hyp(2, either), try hyp(1, fromP), try hyp(0, fromQ)))
        (letters, body) = (3, try assume(either, try assume(fromP, try assume(fromQ, cases))))
    case .falseE:
        let bottom = try n(.folBottom)
        (letters, body) = (1, try assume(bottom, try n(.folBottomElim(try hyp(0, bottom), try v(0)))))
    case .iffReflection:
        let (p, q) = (try v(1), try v(0)), h = try n(.folAnd(try imp(p, q), try imp(q, p)))
        let (pq, qp) = (try n(.folAndElimL(try hyp(0, h))), try n(.folAndElimR(try hyp(0, h))))
        (letters, body) = (2, try assume(h, try n(.folIffIntro(pq, qp))))
    case .classical:
        let p = try v(0), notP = try n(.folNot(p)), h = try imp(try imp(p, try n(.folBottom)), p)
        let refuted = try assume(p, try n(.folNotElim(try hyp(1, notP), try hyp(0, p))))
        let absurd = try n(.folNotElim(try hyp(0, notP), try n(.folImpliesElim(try hyp(1, h), refuted))))
        (letters, body) = (1, try assume(h, try n(.folClassicalAbsurd(p, body: absurd))))
    }
    var proved = body
    for _ in 0..<letters { proved = try n(.isaAllIntro(.o, body: proved)) }
    return proved
}
