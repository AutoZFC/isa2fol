import IR

@frozen public enum LogicError: Error, Equatable, Sendable {
    case notCongruence(NodeID)
    case notTheRule(NodeID)
}

public struct Logic: Pass {
    public let name = "logic"
    let base: Base

    public init(base: Base) { self.base = base }

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .claimed?, .instance?, .equality?, .classical?, .iffReflection?, .proposition?, .function?: return .rule
        case .unbuilt?: return .unbuilt
        case nil: return Reify().owns(p)
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, Steps(base: base, equalities: Equalities(base: base), truths: Truths(base: base)), in: &t)
    }
}

private enum Piece {
    case claimed(BaseStatement)
    case instance
    case equality(Equality)
    case classical
    case iffReflection
    case proposition(Proposition)
    case function(Function)
    case unbuilt
}

private enum Equality {
    case reflexive, symmetric, transitive
}

private enum Proposition {
    case binder, intro, variable
}

private enum Function {
    case wrapper, equation, combination
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .use(.axiom(a), types, _):
        guard isLogic(a.family), !types.contains(where: mentionsTypeVariable) else { return nil }
        return rule(a)
    case let .isaConst(.primitive(.pure(.eq)), T, _):
        if case let .fn(F, _) = T, propositional(F) { return .function(.equation) }
        return mentionsTypeVariable(T) ? nil : .unbuilt
    case let .isaReflexive(T):
        return equality(T, .reflexive)
    case let .isaSymmetric(T, _):
        return equality(T, .symmetric)
    case let .isaTransitive(T, _, _):
        return equality(T, .transitive)
    case let .isaCombination(F, _, _):
        if propositional(F) { return .function(.combination) }
        return mentionsTypeVariable(F) ? nil : .unbuilt
    case let .isaAbstract(F, _):
        return mentionsTypeVariable(F) ? nil : .unbuilt
    case .isaClassical:
        return .classical
    case .isaIffReflection:
        return .iffReflection
    case let .isaAbs(T, body: U):
        if propositional(.fn(T, U)) { return .function(.wrapper) }
        return beyondObjects(.fn(T, U)) ? .unbuilt : nil
    case let .isaAllElim(_, T):
        return T == .o ? .instance : beyondObjects(T) ? .unbuilt : nil
    case let .ifolAll(T, _), let .ifolEx(T, _), let .isaAllIntro(T, _):
        return T != .o && beyondObjects(T) ? .unbuilt : nil
    case .isaPropAll:
        return .proposition(.binder)
    case .isaPropIntro:
        return .proposition(.intro)
    case .isaPropBound:
        return .proposition(.variable)
    case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaOfClass, .folImplies, .folImpliesIntro, .folImpliesElim, .folAnd,
         .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred,
         .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
         .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim,
         .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
         .folLetterAbs:
        return nil
    }
}

private func equality(_ T: IRType, _ e: Equality) -> Piece? {
    if mentionsTypeVariable(T) { return nil }
    return T == .o || T == .i || propositional(T) ? .equality(e) : .unbuilt
}

private func beyondObjects(_ T: IRType) -> Bool { !isObject(T) && !mentionsTypeVariable(T) }

private func rule(_ a: Axiom) -> Piece {
    switch a {
    case .ifol(.subst):
        return .claimed(.classSubst)
    case .ifol(.refl), .ifol(.impI), .ifol(.mp), .ifol(.conjI), .ifol(.conjunct1), .ifol(.conjunct2), .ifol(.disjI1),
         .ifol(.disjI2), .ifol(.disjE), .ifol(.falseE), .ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE),
         .ifol(.eqReflection), .ifol(.iffReflection), .fol(.classical), .zf:
        return .unbuilt
    }
}

private struct Steps: Rule {
    let base: Base
    let equalities: Equalities
    let truths: Truths
    var start: Anywhere { Anywhere() }
    func enter(_ c: Anywhere, _ binder: Node, _ binds: Binds, in t: Table) -> Anywhere { c }

    func after(_ n: Node, was id: NodeID, context: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case let .claimed(s)?:
            guard case let .use(_, _, root) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.use(.base(s.rawValue), [], root))
        case .instance?:
            let (p, a) = (children(n)[0], children(n)[1])
            if case .ifolAll(.o, _)? = t.conclusion(of: p).map({ t[$0] }) { return try t.intern(.folSchemaInst(p, a)) }
            return try truths.instance(p, at: a, in: &t)
        case let .equality(e)?:
            return try equalities.rewrite(e, n, was: id, in: &t)
        case .classical?:
            guard case let .isaClassical(a, h) = n else { throw LogicError.notTheRule(id) }
            return try reductio(a, h, in: &t)
        case .iffReflection?:
            guard case let .isaIffReflection(_, _, h) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folIffIntro(try t.intern(.folAndElimL(h)), try t.intern(.folAndElimR(h))))
        case .proposition(.binder)?:
            guard case let .isaPropAll(body) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folForall(body: try t.intern(.folImplies(try truth(try t.intern(.folBound(0)), in: &t), body))))
        case .proposition(.intro)?:
            guard case let .isaPropIntro(body) = n, let phi = t.conclusion(of: body) else { throw LogicError.notTheRule(id) }
            let premise = try truth(try t.intern(.folBound(0)), in: &t)
            return try t.intern(.folForallIntro(body: try base.applied(.weaken, [phi, premise], [body], in: &t)))
        case .proposition(.variable)?:
            guard case let .isaPropBound(k) = n else { throw LogicError.notTheRule(id) }
            return try holds(try t.intern(.folBound(k)), in: &t)
        case .function(.wrapper)?:
            return nil
        case .function(.equation)?:
            guard case let .isaConst(_, .fn(F, _), args) = n, args.count == 2 else { throw LogicError.notTheRule(id) }
            return try truths.pointwise(F, args[0], args[1], in: &t)
        case .function(.combination)?:
            guard case let .isaCombination(F, p, q) = n else { throw LogicError.notTheRule(id) }
            return try truths.combination(F, p, q, in: &t)
        case .unbuilt?:
            return nil
        case nil:
            return try Reify().after(n, was: id, base: base, in: &t)
        }
    }
}

private struct Equalities {
    let base: Base

    func rewrite(_ e: Equality, _ n: Node, was id: NodeID, in t: inout Table) throws -> NodeID {
        let first = children(n)[0]
        switch e {
        case .reflexive:
            guard case let .isaReflexive(f) = n, let T = t.type(of: f) else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).reflexive(T, f, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.instance(.iffRefl, [f], in: &t)
        case .symmetric:
            guard case let .isaSymmetric(T, p) = n else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).symmetric(T, p, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.applied(.iffSymm, try sidesAtO(p, in: t), [p], in: &t)
        case .transitive:
            guard case let .isaTransitive(T, p, q) = n else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).transitive(T, p, q, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p, q], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            let ab = try sidesAtO(p, in: t), bc = try sidesAtO(q, in: t)
            return try base.applied(.iffTrans, ab + [bc[1]], [p, q], in: &t)
        }
    }

    private func atI(_ e: Equality, _ sides: [NodeID], _ premises: [NodeID], in t: inout Table) throws -> NodeID {
        let v = try sides.indices.map { try t.intern(.isaBound(sides.count - 1 - $0, .i)) }
        let equated = { (j: Int, k: Int, t: inout Table) throws -> NodeID in try t.equation(.i, v[j], v[k]) }
        var stated: NodeID, proved: NodeID
        switch e {
        case .reflexive:
            stated = try t.intern(.isaReflexive(v[0]))
            proved = try base.claimed(.eqRefl, [v[0]], [], in: &t)
        case .symmetric:
            let xy = try equated(0, 1, &t), xyNamed = try named(formula: xy, in: &t)
            stated = try t.intern(.folImpliesIntro(xy, body: try t.intern(.isaSymmetric(.i, try t.intern(.hyp(0, xy))))))
            proved = try t.intern(.folImpliesIntro(xyNamed, body: try base.claimed(.eqSymm, [v[0], v[1]], [try t.intern(.hyp(0, xyNamed))], in: &t)))
        case .transitive:
            let xy = try equated(0, 1, &t), yz = try equated(1, 2, &t)
            let xyNamed = try named(formula: xy, in: &t), yzNamed = try named(formula: yz, in: &t)
            let both = try t.intern(.isaTransitive(.i, try t.intern(.hyp(1, xy)), try t.intern(.hyp(0, yz))))
            stated = try t.intern(.folImpliesIntro(xy, body: try t.intern(.folImpliesIntro(yz, body: both))))
            let chained = try base.claimed(.eqTrans, v, [try t.intern(.hyp(1, xyNamed)), try t.intern(.hyp(0, yzNamed))], in: &t)
            proved = try t.intern(.folImpliesIntro(xyNamed, body: try t.intern(.folImpliesIntro(yzNamed, body: chained))))
        }
        for _ in sides {
            stated = try t.intern(.isaAllIntro(.i, body: stated))
            proved = try t.intern(.isaAllIntro(.i, body: proved))
        }
        for x in sides {
            let elim = try t.intern(.isaAllElim(stated, x))
            proved = try Reify().instance(proved, was: elim, base: base, in: &t)
            stated = elim
        }
        for p in premises { proved = try t.intern(.folImpliesElim(proved, p)) }
        return proved
    }
}

/// ⚠ BUILT CLOSED OVER `h`'S STATEMENT AND APPLIED TO `h`: built around `h` itself, a proof holding hypotheses would be
/// read under the reductio's own.
private func reductio(_ a: NodeID, _ h: NodeID, in t: inout Table) throws -> NodeID {
    guard let premise = t.conclusion(of: h) else { throw LogicError.notTheRule(h) }
    let notA = try t.intern(.folNot(a))
    let refuted = try t.intern(.folImpliesIntro(a, body: try t.intern(.folNotElim(try t.intern(.hyp(1, notA)), try t.intern(.hyp(0, a))))))
    let absurd = try t.intern(.folNotElim(try t.intern(.hyp(0, notA)),
                                          try t.intern(.folImpliesElim(try t.intern(.hyp(1, premise)), refuted))))
    let closed = try t.intern(.folImpliesIntro(premise, body: try t.intern(.folClassicalAbsurd(a, body: absurd))))
    return try t.intern(.folImpliesElim(closed, h))
}

private func sidesAtI(_ id: NodeID, _ t: Table) throws -> [NodeID] {
    func equated(_ p: NodeID) throws -> (NodeID, NodeID) {
        guard let c = t.conclusion(of: p), let (T, a, b) = t.sides(ofEquation: c), T == .i else { throw LogicError.notCongruence(p) }
        return (a, b)
    }
    if case let .isaReflexive(x) = t[id] { return [x] }
    if case let .isaSymmetric(_, p) = t[id] {
        let (a, b) = try equated(p)
        return [a, b]
    }
    guard case let .isaTransitive(_, p, q) = t[id] else { throw LogicError.notCongruence(id) }
    let (a, b) = try equated(p), (_, c) = try equated(q)
    return [a, b, c]
}

private func sidesAtO(_ p: NodeID, in t: Table) throws -> [NodeID] {
    guard let c = t.conclusion(of: p), let (T, a, b) = t.sides(ofEquation: c), T == .o else {
        throw LogicError.notCongruence(p)
    }
    return [a, b]
}
