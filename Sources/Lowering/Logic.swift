import IR

@frozen
public enum LogicError: Error, Equatable, Sendable {
    case notCongruence(NodeID)
    case notTheRule(NodeID)
}

public struct Logic: Pass {
    public init(base: Base) {
        self.base = base
    }

    public let name = "logic"

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .claimed?, .instance?, .lambda?, .equality?, .classical?, .iffReflection?, .proposition?, .function?,
             .pointwise?: .rule
        case .unbuilt?: .unbuilt
        case nil: Reify().owns(p)
        }
    }

    public func run(_ roots: [NodeID], _: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, Steps(base: base), in: &t)
    }

    let base: Base

}

func walked(_ formula: NodeID, base: Base, in t: inout Table) throws -> NodeID {
    try transform(formula, Steps(base: base), in: &t)
}

private enum Piece {
    case claimed(BaseStatement)
    case instance
    case lambda
    case equality(Equality)
    case classical
    case iffReflection
    case proposition(Proposition)
    case function(Function)
    case pointwise(Pointwise)
    case unbuilt
}

enum Equality {
    case reflexive
    case symmetric
    case transitive
}

private enum Proposition {
    case binder
    case intro
    case variable
    case hidden
}

private enum Function {
    case wrapper
    case equation
    case combination
}

private enum Pointwise {
    case wrapper
    case equation
    case combination
    case abstract
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case .use(.axiom(let a), let types, _):
        guard isLogic(a.family), !types.contains(where: mentionsTypeVariable) else { return nil }
        return rule(a)

    case .isaConst(.primitive(.pure(.eq)), let T, _):
        if case .fn(let F, _) = T, propositional(F) { return .function(.equation) }
        if case .fn(let F, _) = T, overObjects(F) { return .pointwise(.equation) }
        return mentionsTypeVariable(T) ? nil : .unbuilt

    case .isaReflexive(let T):
        return equality(T, .reflexive)

    case .isaSymmetric(let T, _):
        return equality(T, .symmetric)

    case .isaTransitive(let T, _, _):
        return equality(T, .transitive)

    case .isaCombination(let F, _, _):
        if propositional(F) { return .function(.combination) }
        if overObjects(F) { return .pointwise(.combination) }
        return mentionsTypeVariable(F) ? nil : .unbuilt

    case .isaAbstract(let F, _):
        if overObjects(F) { return .pointwise(.abstract) }
        return mentionsTypeVariable(F) ? nil : .unbuilt

    case .isaClassical:
        return .classical

    case .isaIffReflection:
        return .iffReflection

    case .isaAbs(let T, body: let U):
        if propositional(.fn(T, U)) { return .function(.wrapper) }
        if !isObject(.fn(T, U)), overObjects(.fn(T, U)) { return .pointwise(.wrapper) }
        return beyondObjects(.fn(T, U)) ? .unbuilt : nil

    case .isaAllElim(_, let T):
        if T == .o { return .instance }
        if T != .i && isObject(T) { return .lambda }
        return beyondObjects(T) ? .unbuilt : nil

    case .ifolAll(let T, _), .ifolEx(let T, _), .isaAllIntro(let T, _):
        return T != .o && beyondObjects(T) ? .unbuilt : nil

    case .isaPropAll:
        return .proposition(.binder)

    case .isaPropIntro:
        return .proposition(.intro)

    case .isaPropBound:
        return .proposition(.variable)

    case .isaHidden(let T, _):
        if T == .o { return .proposition(.hidden) }
        return beyondObjects(T) ? .unbuilt : nil

    case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaOfClass, .isaDefinition, .folImplies, .folImpliesIntro,
         .folImpliesElim, .folAnd, .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
         .folBound, .folPred,
         .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
         .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim,
         .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll,
         .folLetter,
         .folLetterAbs:
        return nil
    }
}

private func equality(_ T: IRType, _ e: Equality) -> Piece? {
    if mentionsTypeVariable(T) { return nil }
    return T == .o || T == .i || propositional(T) || overObjects(T) ? .equality(e) : .unbuilt
}

private func beyondObjects(_ T: IRType) -> Bool {
    !isObject(T) && !mentionsTypeVariable(T)
}

private func rule(_ a: Axiom) -> Piece {
    switch a {
    case .ifol(.subst):
        .claimed(.classSubst)
    case .ifol(.refl), .ifol(.impI), .ifol(.mp), .ifol(.conjI), .ifol(.conjunct1), .ifol(.conjunct2), .ifol(.disjI1),
         .ifol(.disjI2), .ifol(.disjE), .ifol(.falseE), .ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE),
         .ifol(.eqReflection), .ifol(.iffReflection), .fol(.classical), .zf:
        .unbuilt
    }
}

private struct Steps: Rule {
    init(base: Base) {
        self.base = base
        equalities = Equalities(base: base)
        truths = Truths(base: base)
    }

    let base: Base
    let equalities: Equalities
    let truths: Truths

    var start: Anywhere {
        Anywhere()
    }

    func enter(_ c: Anywhere, _: Node, _: Binds, in _: Table) -> Anywhere {
        c
    }

    func after(_ n: Node, was id: NodeID, context _: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case .claimed(let s)?:
            guard case .use(_, _, let root) = n else { throw LogicError.notTheRule(id) }
            return try claimed(s, root, was: id, in: &t)

        case .instance?:
            let p = children(n)[0]
            let a = children(n)[1]
            if case .ifolAll(.o, _)? = t.conclusion(of: p).map({ t[$0] }) { return try t.intern(.folSchemaInst(p, a)) }
            return try truths.instance(p, at: a, in: &t)

        case .lambda?:
            return try LambdaInstance(base: base).proof(children(n)[0], was: id, in: &t)

        case .equality(let e)?:
            return try equalities.rewrite(e, n, was: id, in: &t)

        case .classical?:
            guard case .isaClassical(let a, let h) = n else { throw LogicError.notTheRule(id) }
            return try reductio(a, h, in: &t)

        case .iffReflection?:
            guard case .isaIffReflection(_, _, let h) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folIffIntro(try t.intern(.folAndElimL(h)), try t.intern(.folAndElimR(h))))

        case .proposition(.binder)?:
            guard case .isaPropAll(let body) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folForall(body: try t.intern(.folImplies(
                try truth(try t.intern(.folBound(0)), in: &t),
                body,
            ))))

        case .proposition(.intro)?:
            guard
                case .isaPropIntro(let body) = n,
                let phi = t.conclusion(of: body)
            else { throw LogicError.notTheRule(id) }
            let premise = try truth(try t.intern(.folBound(0)), in: &t)
            return try t.intern(.folForallIntro(body: try base.applied(.weaken, [phi, premise], [body], in: &t)))

        case .proposition(.variable)?:
            guard case .isaPropBound(let k) = n else { throw LogicError.notTheRule(id) }
            return try holds(try t.intern(.folBound(k)), in: &t)

        case .proposition(.hidden)?:
            guard case .isaHidden(.o, let body) = n else { throw LogicError.notTheRule(id) }
            return try hiddenProposition(body, base, in: &t)

        case .function(.wrapper)?:
            return nil

        case .function(.equation)?:
            guard
                case .isaConst(_, .fn(let F, _), let args) = n,
                args.count == 2
            else { throw LogicError.notTheRule(id) }
            return try truths.pointwise(F, args[0], args[1], in: &t)

        case .function(.combination)?:
            guard case .isaCombination(let F, let p, let q) = n else { throw LogicError.notTheRule(id) }
            return try truths.combination(F, p, q, in: &t)

        case .pointwise(.wrapper)?:
            return nil

        case .pointwise(.equation)?:
            guard
                case .isaConst(_, .fn(let F, _), let args) = n,
                args.count == 2
            else { throw LogicError.notTheRule(id) }
            return try Functions(base: base).pointwise(F, args[0], args[1], in: &t)

        case .pointwise(.combination)?:
            guard case .isaCombination(let F, let p, let q) = n else { throw LogicError.notTheRule(id) }
            return try Functions(base: base).combination(F, p, q, was: id, in: &t)

        case .pointwise(.abstract)?:
            guard case .isaAbstract(_, let p) = n else { throw LogicError.notTheRule(id) }
            return try Functions(base: base).abstract(p, was: id, in: &t)

        case .unbuilt?:
            return nil

        case nil:
            return try Reify().after(n, was: id, base: base, in: &t)
        }
    }

    /// ⚠ AN AXIOM BASE CLAIMS STATES ITS CLASS PREMISES, AND BASE'S CLAIM NONE: relabelled whole, the citation
    /// concludes
    /// in the IR what base's claim does not, and only the kernel sees it.
    private func claimed(_ s: BaseStatement, _ root: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        let cited = try base.cite(s, in: &t)
        guard case .use(_, _, let stated) = t[cited] else { throw LogicError.notTheRule(id) }
        func premises(_ x: NodeID) -> [NodeID] {
            var x = x
            var found = [NodeID]()
            while case .folImplies(let a, let b) = t[x] { (found, x) = (found + [a], b) }
            return found
        }
        let axiom = premises(root)
        let claim = premises(stated)
        guard axiom.count >= claim.count else { throw LogicError.notTheRule(id) }
        var body = root
        for _ in 0..<(axiom.count - claim.count) {
            guard case .folImplies(_, let b) = t[body] else { throw LogicError.notTheRule(id) }
            body = b
        }
        var proof = try t.intern(.use(.base(s.rawValue), [], body))
        for a in axiom[..<(axiom.count - claim.count)].reversed() { proof = try t.intern(.folImpliesIntro(
            a,
            body: proof,
        )) }
        return proof
    }
}

struct Equalities {
    let base: Base

    func rewrite(_ e: Equality, _ n: Node, was id: NodeID, in t: inout Table) throws -> NodeID {
        let first = children(n)[0]
        switch e {
        case .reflexive:
            guard case .isaReflexive(let f) = n, let T = t.type(of: f) else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).reflexive(T, f, in: &t) }
            if overObjects(T) {
                guard case .isaReflexive(let stated) = t[id] else { throw LogicError.notCongruence(first) }
                return try Functions(base: base).reflexive(T, stated, in: &t)
            }
            if T == .i { return try atI(e, try sidesAtI(id, t), [], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.instance(.iffRefl, [f], in: &t)

        case .symmetric:
            guard case .isaSymmetric(let T, let p) = n else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).symmetric(T, p, in: &t) }
            if overObjects(T) { return try Functions(base: base).symmetric(T, p, was: id, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.applied(.iffSymm, try sidesAtO(p, in: t), [p], in: &t)

        case .transitive:
            guard case .isaTransitive(let T, let p, let q) = n else { throw LogicError.notCongruence(first) }
            if propositional(T) { return try Truths(base: base).transitive(T, p, q, in: &t) }
            if overObjects(T) { return try Functions(base: base).transitive(T, p, q, was: id, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p, q], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            let ab = try sidesAtO(p, in: t)
            let bc = try sidesAtO(q, in: t)
            return try base.applied(.iffTrans, ab + [bc[1]], [p, q], in: &t)
        }
    }

    func atI(_ e: Equality, _ sides: [NodeID], _ premises: [NodeID], in t: inout Table) throws -> NodeID {
        let v = try sides.indices.map { try t.intern(.isaBound(sides.count - 1 - $0, .i)) }
        let equated = { (j: Int, k: Int, t: inout Table) throws -> NodeID in try t.equation(.i, v[j], v[k]) }
        var stated: NodeID
        var proved: NodeID
        switch e {
        case .reflexive:
            stated = try t.intern(.isaReflexive(v[0]))
            proved = try base.claimed(.eqRefl, [v[0]], [], in: &t)

        case .symmetric:
            let xy = try equated(0, 1, &t)
            let xyNamed = try named(formula: xy, in: &t)
            stated = try t.intern(.folImpliesIntro(
                xy,
                body: try t.intern(.isaSymmetric(.i, try t.intern(.hyp(0, xy)))),
            ))
            proved = try t.intern(.folImpliesIntro(
                xyNamed,
                body: try base.claimed(.eqSymm, [v[0], v[1]], [try t.intern(.hyp(0, xyNamed))], in: &t),
            ))

        case .transitive:
            let xy = try equated(0, 1, &t)
            let yz = try equated(1, 2, &t)
            let xyNamed = try named(formula: xy, in: &t)
            let yzNamed = try named(formula: yz, in: &t)
            let both = try t.intern(.isaTransitive(.i, try t.intern(.hyp(1, xy)), try t.intern(.hyp(0, yz))))
            stated = try t.intern(.folImpliesIntro(xy, body: try t.intern(.folImpliesIntro(yz, body: both))))
            let chained = try base.claimed(
                .eqTrans,
                v,
                [try t.intern(.hyp(1, xyNamed)), try t.intern(.hyp(0, yzNamed))],
                in: &t,
            )
            proved = try t.intern(.folImpliesIntro(
                xyNamed,
                body: try t.intern(.folImpliesIntro(yzNamed, body: chained)),
            ))
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

/// ⚠ AN `exists_elim` WRAPPED STRAIGHT AROUND `body` SHIFTS ITS HYPOTHESES, AND THE TABLE CHECKS NONE AGAINST ITS
/// BINDER: generalized first, `body` keeps them where they are.
private func hiddenProposition(_ body: NodeID, _ base: Base, in t: inout Table) throws -> NodeID {
    let general = try t.intern(.folForallIntro(body: body))
    guard let stated = t.conclusion(of: general) else { throw LogicError.notTheRule(body) }
    let opened = try t.intern(.folExistsElim(
        try base.cite(.truthInhabited, in: &t),
        body: try t.intern(.folForallElim(
            try t.intern(.hyp(1, try shift(stated, by: 1, in: &t))),
            try t.intern(.folBound(0)),
        )),
    ))
    return try t.intern(.folImpliesElim(try t.intern(.folImpliesIntro(stated, body: opened)), general))
}

/// ⚠ BUILT CLOSED OVER `h`'S STATEMENT AND APPLIED TO `h`: built around `h` itself, a proof holding hypotheses would be
/// read under the reductio's own.
private func reductio(_ a: NodeID, _ h: NodeID, in t: inout Table) throws -> NodeID {
    guard let premise = t.conclusion(of: h) else { throw LogicError.notTheRule(h) }
    let notA = try t.intern(.folNot(a))
    let refuted = try t.intern(.folImpliesIntro(
        a,
        body: try t.intern(.folNotElim(try t.intern(.hyp(1, notA)), try t.intern(.hyp(0, a)))),
    ))
    let absurd = try t.intern(.folNotElim(
        try t.intern(.hyp(0, notA)),
        try t.intern(.folImpliesElim(try t.intern(.hyp(1, premise)), refuted)),
    ))
    let closed = try t.intern(.folImpliesIntro(premise, body: try t.intern(.folClassicalAbsurd(a, body: absurd))))
    return try t.intern(.folImpliesElim(closed, h))
}

private func sidesAtI(_ id: NodeID, _ t: Table) throws -> [NodeID] {
    func equated(_ p: NodeID) throws -> (NodeID, NodeID) {
        guard
            let c = t.conclusion(of: p), let (T, a, b) = t.sides(ofEquation: c),
            T == .i
        else { throw LogicError.notCongruence(p) }
        return (a, b)
    }
    if case .isaReflexive(let x) = t[id] { return [x] }
    if case .isaSymmetric(_, let p) = t[id] {
        let (a, b) = try equated(p)
        return [a, b]
    }
    guard case .isaTransitive(_, let p, let q) = t[id] else { throw LogicError.notCongruence(id) }
    let (a, b) = try equated(p), (_, c) = try equated(q)
    return [a, b, c]
}

private func sidesAtO(_ p: NodeID, in t: Table) throws -> [NodeID] {
    guard let c = t.conclusion(of: p), let (T, a, b) = t.sides(ofEquation: c), T == .o else {
        throw LogicError.notCongruence(p)
    }
    return [a, b]
}
