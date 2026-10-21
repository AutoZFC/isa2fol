import IR

@frozen
public enum LogicError: Error, Equatable, Sendable {
    case notCongruence(NodeID)
    case notTheRule(NodeID)
    case notAFormula(NodeID)
    case uncited(NodeID)
}

public struct Logic: Pass, Walk {
    public init(base: Base) {
        self.base = base
    }

    public let name = "logic"

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .claimed?, .axiom?, .instance?, .lambda?, .equality?, .classical?, .iffReflection?, .proposition?,
             .pointwise?: .rule
        case .unbuilt?: .unbuilt
        case nil: Reify().owns(p)
        }
    }

    public func walk(_: [Definition], in _: inout Table) throws -> any Walk {
        self
    }

    public func run(_ roots: [NodeID], citing forms: [NodeID: NodeID], sharing memo: inout Memo, in t: inout Table)
        throws -> [NodeID]
    {
        let proofs = roots.filter { t.conclusion(of: $0) != nil }
        let lowered = try transform(proofs, Steps(base: base, forms: forms), sharing: &memo, in: &t)
        var byRoot = [NodeID: NodeID]()
        for (p, q) in zip(proofs, lowered) {
            guard let c = t.conclusion(of: p) else { throw LogicError.notTheRule(p) }
            byRoot[p] = try finished(q, c, base: base, in: &t)
        }
        return try roots.map { r in try byRoot[r] ?? formula(r, .statement, in: &t) }
    }

    let base: Base

}

/// A formula's form where it stands: a statement's, every term named; a proof's, each term holding no variable the
/// formula binds its value.
func formula(_ x: NodeID, _ mode: Mode, in t: inout Table) throws -> NodeID {
    try transform(x, Formulas(mode: mode), in: &t)
}

func valued(_ x: NodeID, in t: inout Table) throws -> NodeID {
    try formula(x, .proof(0), in: &t)
}

/// A proof's last step: its statement's S1 form from its value form, below the statement's letters, which stay on its
/// spine — the values holding a letter fixed under them, the closed values above those.
private func finished(_ p: NodeID, _ statement: NodeID, base: Base, in t: inout Table) throws -> NodeID {
    var letters = 0
    var proof = p
    var matrix = statement
    while case .ifolAll(.o, let body) = t[matrix], case .isaAllIntro(.o, let inner) = t[proof] {
        (letters, proof, matrix) = (letters + 1, inner, body)
    }
    let named = try met(proof, matrix, moving: .closed, toValues: false, in: &t)
    let lettered = try fixing(
        try scoped(named, closed: false, below: letters, in: &t),
        in: named,
        by: .existence(base),
        in: &t,
    )
    var done = try fixing(try scoped(lettered, closed: true, in: &t), in: lettered, by: .existence(base), in: &t)
    for _ in 0..<letters { done = try t.intern(.isaAllIntro(.o, body: done)) }
    return done
}

/// `p` proving a cited statement's S1 form at its letters' `instances`: its value form, its matrix met once below the
/// letters, the closed terms and those holding a letter crossing to their values.
func metBelowLetters(_ p: NodeID, _ stated: NodeID, at instances: [NodeID], in t: inout Table) throws -> NodeID {
    var matrix = stated
    for _ in instances {
        guard case .ifolAll(.o, let body) = t[matrix] else { throw LogicError.notTheRule(stated) }
        matrix = body
    }
    var sites = [Int: NodeID]()
    for (j, a) in instances.reversed().enumerated() { sites[j] = a }
    return try met(p, matrix, moving: .closed, at: sites, drop: instances.count, toValues: true, in: &t)
}

/// The letters a statement binds at its top.
func letters(_ stated: NodeID, _ t: Table) -> Int {
    guard case .ifolAll(.o, let body) = t[stated] else { return 0 }
    return 1 + letters(body, t)
}

private enum Piece {
    case claimed(BaseStatement)
    case axiom
    case instance
    case lambda
    case equality(Equality)
    case classical
    case iffReflection
    case proposition(Proposition)
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

private enum Pointwise {
    case wrapper
    case equation
    case combination
    case abstract
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case .use(.axiom(let a), let types, _):
        guard !types.contains(where: mentionsTypeVariable) else { return nil }
        return rule(a)

    case .isaConst(.primitive(.pure(.eq)), let T, _):
        if case .fn(let F, _) = T, overArguments(F) { return .pointwise(.equation) }
        return mentionsTypeVariable(T) ? nil : .unbuilt

    case .isaReflexive(let T):
        return equality(T, .reflexive)

    case .isaSymmetric(let T, _):
        return onlyReflexive(T) ? nil : equality(T, .symmetric)

    case .isaTransitive(let T, _, _):
        return onlyReflexive(T) ? nil : equality(T, .transitive)

    case .isaCombination(let F, _, _):
        if overArguments(F) { return .pointwise(.combination) }
        if overArguments(F) { return .unbuilt }
        return mentionsTypeVariable(F) || onlyReflexive(F) ? nil : .unbuilt

    case .isaAbstract(let F, _):
        if overObjects(F) { return .pointwise(.abstract) }
        return mentionsTypeVariable(F) ? nil : .unbuilt

    case .isaClassical:
        return .classical

    case .isaIffReflection:
        return .iffReflection

    case .isaAbs(let T, body: let U):
        if !isObject(.fn(T, U)), overArguments(.fn(T, U)) { return .pointwise(.wrapper) }
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
        return T == .o ? .proposition(.hidden) : nil

    case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaOfClass, .isaDefinition, .folImplies, .folImpliesIntro,
         .folImpliesElim, .folAnd, .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot,
         .folBound, .folPred,
         .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
         .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim,
         .folExistsIntro, .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll,
         .folLetter,
         .folLetterAbs, .isaValue, .isaValueFact:
        return nil
    }
}

private func equality(_ T: IRType, _ e: Equality) -> Piece? {
    if mentionsTypeVariable(T) { return nil }
    if overArguments(T) { return .equality(e) }
    return T == .o || T == .i ? .equality(e) : .unbuilt
}

private func beyondObjects(_ T: IRType) -> Bool {
    !isObject(T) && !mentionsTypeVariable(T)
}

private func rule(_ a: Axiom) -> Piece {
    switch a {
    case .ifol(.subst):
        .claimed(.classSubst)
    case .zf(let z):
        z.inNBG == nil ? .unbuilt : .axiom
    case .ifol(.refl), .ifol(.impI), .ifol(.mp), .ifol(.conjI), .ifol(.conjunct1), .ifol(.conjunct2), .ifol(.disjI1),
         .ifol(.disjI2), .ifol(.disjE), .ifol(.falseE), .ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE),
         .ifol(.eqReflection), .ifol(.iffReflection), .fol(.classical):
        .unbuilt
    }
}

private struct Formulas: Rule {
    let mode: Mode

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard t.conclusion(of: id) == nil else { throw LogicError.notAFormula(id) }
        let p = Pattern(t[id], in: t)
        if Reify().names(p) { return try named(atom: t[id], mode: mode.deeper(depth.terms), in: &t) }
        if case .pointwise(.equation)? = piece(p) {
            guard case .isaConst(_, .fn(let F, _), let args) = t[id], args.count == 2 else {
                throw LogicError.notTheRule(id)
            }
            return try formula(
                try Functions.isaPointwise(F, args[0], args[1], in: &t),
                mode.deeper(depth.terms),
                in: &t,
            )
        }
        return nil
    }

    func after(_ n: Node, was id: NodeID, context _: Depth, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case .proposition(.binder)?:
            guard case .isaPropAll(let body) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folForall(body: try t.intern(.folImplies(
                try truth(try t.intern(.folBound(0)), in: &t),
                body,
            ))))

        case .proposition(.variable)?:
            guard case .isaPropBound(let k) = n else { throw LogicError.notTheRule(id) }
            return try holds(try t.intern(.folBound(k)), in: &t)

        case .pointwise(.wrapper)?, .unbuilt?, nil:
            return nil

        case .pointwise(.equation)?, .claimed?, .axiom?, .instance?, .lambda?, .equality?, .classical?,
             .iffReflection?, .proposition(.intro)?, .proposition(.hidden)?, .pointwise(.combination)?,
             .pointwise(.abstract)?:
            throw LogicError.notAFormula(id)
        }
    }
}

private enum Place: Hashable {
    case proof
    case formula
}

/// ⚠ A FORMULA A STEP HOLDS IS VALUED AT THE STEP, NEVER WALKED BELOW IT: under a binder of its own, as an `∃`-intro's
/// body, its variable would read as the proof's.
private struct Steps: Rule {
    init(base: Base, forms: [NodeID: NodeID]) {
        self.base = base
        self.forms = forms
        equalities = Equalities(base: base)
        truths = Truths(base: base)
    }

    let base: Base
    let forms: [NodeID: NodeID]
    let equalities: Equalities
    let truths: Truths

    var start: Place {
        .proof
    }

    func enter(_ c: Place, _ binder: Node, _: Binds, in _: Table) -> Place {
        if case .isaExIntro = binder { return .formula }
        return c
    }

    func before(_ id: NodeID, context c: Place, in t: inout Table) throws -> NodeID? {
        if c == .formula { return id }
        guard t.conclusion(of: id) != nil else { return t.type(of: id) == .o ? try valued(id, in: &t) : id }
        switch t[id] {
        case .use(let cited, let types, let root):
            let stated: NodeID
            if case .theorem = cited {
                guard let form = forms[root] else { throw LogicError.uncited(root) }
                stated = form
            } else {
                stated = try formula(root, .statement, in: &t)
            }
            let citation: NodeID =
                switch piece(Pattern(t[id], in: t)) {
                case .claimed(let s)?: try claimed(s, stated, was: id, in: &t)
                case .axiom?: try axiomCited(.use(cited, types, stated), was: id, in: &t)
                default: try t.intern(.use(cited, types, stated))
                }
            return letters(root, t) == 0 ? try metBelowLetters(citation, root, at: [], in: &t) : citation

        case .isaDefinition(_, .constant(let c), _, let stated, let args):
            guard Reify().owns(Pattern(t[id], in: t)) == .rule else { return nil }
            let statement = try formula(stated, .statement, in: &t)
            return try definition(c, stated: stated, statement: statement, at: args, base: base, in: &t).proof

        default:
            return nil
        }
    }

    func after(_ n: Node, was id: NodeID, context _: Place, in t: inout Table) throws -> NodeID? {
        let instances = Instances(base: base)
        switch piece(Pattern(n, in: t)) {
        case .claimed?, .axiom?:
            throw LogicError.notTheRule(id)

        case .instance?, .lambda?:
            guard
                case .isaAllElim(let original, let a) = t[id], let stated = t.conclusion(of: original),
                case .ifolAll(let T, let body) = t[stated]
            else {
                if
                    case .isaAllElim(let original, let a) = t[id], let stated = t.conclusion(of: original),
                    case .isaPropAll = t[stated]
                {
                    return try truths.instance(children(n)[0], at: try valued(a, in: &t), in: &t)
                }
                throw LogicError.notTheRule(id)
            }
            if T == .o { return try letterInstance(children(n)[0], body, at: a, was: id, in: &t) }
            if T != .i { return try instantiatedAtLambda(children(n)[0], body, T, at: a, base: base, in: &t) }
            return try instances.instance(children(n)[0], body, T, at: a, in: &t)

        case .equality(let e)?:
            return try equalities.rewrite(e, n, was: id, in: &t)

        case .classical?:
            guard case .isaClassical(let a, let h) = n else { throw LogicError.notTheRule(id) }
            return try reductio(a, h, in: &t)

        case .iffReflection?:
            guard case .isaIffReflection(_, _, let h) = n else { throw LogicError.notTheRule(id) }
            return try t.intern(.folIffIntro(try t.intern(.folAndElimL(h)), try t.intern(.folAndElimR(h))))

        case .proposition(.binder)?, .proposition(.variable)?, .pointwise(.wrapper)?, .pointwise(.equation)?:
            throw LogicError.notTheRule(id)

        case .proposition(.intro)?:
            guard
                case .isaPropIntro(let body) = n, case .isaPropIntro(let original) = t[id],
                let phi = t.conclusion(of: original)
            else { throw LogicError.notTheRule(id) }
            let named = try met(body, phi, moving: .variables([0]), toValues: false, in: &t)
            let bound = try fixing(try scoped(named, closed: false, in: &t), in: named, by: .existence(base), in: &t)
            guard let stated = t.conclusion(of: bound) else { throw LogicError.notTheRule(id) }
            let premise = try truth(try t.intern(.folBound(0)), in: &t)
            return try t.intern(.folForallIntro(body: try base.applied(.weaken, [stated, premise], [bound], in: &t)))

        case .proposition(.hidden)?:
            guard case .isaHidden(.o, let body) = n else { throw LogicError.notTheRule(id) }
            let bound = try fixing(try scoped(body, closed: false, in: &t), in: body, by: .existence(base), in: &t)
            return try hiddenProposition(bound, base, in: &t)

        case .pointwise(.combination)?:
            guard case .isaCombination(let F, let p, let q) = n else { throw LogicError.notTheRule(id) }
            return try Functions(base: base).combination(F, p, q, was: id, in: &t)

        case .pointwise(.abstract)?:
            guard case .isaAbstract(_, let p) = n else { throw LogicError.notTheRule(id) }
            return try Functions(base: base).abstract(p, was: id, in: &t)

        case .unbuilt?:
            return nil

        case nil:
            switch t[id] {
            case .isaAllElim(let original, let a):
                guard let stated = t.conclusion(of: original), case .ifolAll(.i, let body) = t[stated] else {
                    return nil
                }
                return try instances.instance(children(n)[0], body, .i, at: a, in: &t)

            case .isaAllIntro(let T, let original):
                guard let phi = t.conclusion(of: original) else { throw LogicError.notTheRule(id) }
                return try instances.generalized(children(n)[0], phi, T, in: &t)

            case .isaHidden(let T, _):
                let body = children(n)[0]
                let bound = try fixing(try scoped(body, closed: false, in: &t), in: body, by: .existence(base), in: &t)
                return try t.intern(.isaHidden(T, body: bound))

            case .isaExElim(let T, let premise, let original):
                guard
                    let some = t.conclusion(of: premise), case .ifolEx(_, let psi) = t[some]
                else { throw LogicError.notTheRule(id) }
                _ = original
                return try instances.eliminated(children(n)[0], children(n)[1], psi, T, in: &t)

            case .isaExIntro(_, let a, let psi):
                return try instances.introduced(children(n)[0], psi, at: a, in: &t)

            default:
                return nil
            }
        }
    }

    /// `p`, a citation with its earlier letters instantiated, at its next letter `a`: `schema_inst`; at its last, the
    /// citation's matrix met at its letters' instances. A letter below another binder, off its statement's spine,
    /// meets its own terms where it is instantiated.
    private func letterInstance(_ p: NodeID, _ body: NodeID, at a: NodeID, was id: NodeID, in t: inout Table) throws
        -> NodeID
    {
        let at = try t.intern(.folSchemaInst(p, try valued(a, in: &t)))
        var instances = [NodeID]()
        var head = id
        while
            case .isaAllElim(let q, let x) = t[head], let c = t.conclusion(of: q), case .ifolAll(.o, _) = t[c]
        {
            instances.insert(x, at: 0)
            head = q
        }
        guard case .use(_, _, let root) = t[head] else {
            return try met(at, body, moving: .variables([0]), at: [0: a], drop: 1, toValues: true, in: &t)
        }
        if case .ifolAll(.o, _) = t[body] { return at }
        return try metBelowLetters(at, root, at: instances, in: &t)
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

/// Isabelle's binders and instances on values: each meets the proof's values through its formula's lemma.
struct Instances {
    let base: Base

    /// `p` proving `∀x. ψ`'s value form, at `a`: `ψ[a/x]`'s.
    func instance(_ p: NodeID, _ psi: NodeID, _ T: IRType, at a: NodeID, in t: inout Table) throws -> NodeID {
        let at: NodeID
        switch T {
        case .i: at = try t.intern(.isaAllElim(p, try value(of: a, in: &t)))
        case .o, .fn, .variable: throw LogicError.notTheRule(p)
        }
        return try met(at, psi, moving: .variables([0]), at: [0: a], drop: 1, toValues: true, in: &t)
    }

    /// `body` proving `ψ`'s value form below a new variable: `∀x. ψ`'s. A letter's intro leaves its body's values to
    /// the proof's last step, below every letter.
    func generalized(_ body: NodeID, _ psi: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
        if T == .o { return try t.intern(.isaAllIntro(.o, body: body)) }
        let named = try met(body, psi, moving: .variables([0]), toValues: false, in: &t)
        let bound = try fixing(try scoped(named, closed: false, in: &t), in: named, by: .existence(base), in: &t)
        return try t.intern(.isaAllIntro(T, body: bound))
    }

    /// `exists_elim` over `p`, proving `∃y. ψ`'s value form, of `body`, which assumes `ψ`'s at `y`: a cut from the
    /// elimination's own assumption, `ψ` naming `y`'s terms, where the two differ.
    func eliminated(_ p: NodeID, _ body: NodeID, _ psi: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
        let own = try formula(psi, .proof(0, naming: [0]), in: &t)
        let assumed = try valued(psi, in: &t)
        var proof = body
        if own != assumed {
            let moved = try met(try t.intern(.hyp(0, own)), psi, moving: .variables([0]), toValues: true, in: &t)
            proof = try t.intern(.folCut(moved, body: try transform(body, Inserting(), in: &t)))
        }
        let bound = try fixing(try scoped(proof, closed: false, in: &t), in: proof, by: .existence(base), in: &t)
        return try t.intern(.isaExElim(T, p, body: bound))
    }

    /// `p` proving `ψ[a/y]`'s value form: `∃y. ψ`'s.
    func introduced(_ p: NodeID, _ psi: NodeID, at a: NodeID, in t: inout Table) throws -> NodeID {
        let named = try met(p, psi, moving: .variables([0]), at: [0: a], drop: 1, toValues: false, in: &t)
        let body = try formula(psi, .proof(0, naming: [0]), in: &t)
        return try t.intern(.isaExIntro(named, try value(of: a, in: &t), body: body))
    }

}

/// ⚠ A CUT INSERTED BELOW A BODY'S HYPOTHESIS 0 TAKES ITS PLACE: 0 stays the cut's, and every hypothesis beyond moves
/// one further out.
private struct Inserting: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        t.looseHyps(of: id) <= depth.hyps + 1 ? id : nil
    }

    func after(_ n: Node, was _: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .hyp(let h, let a) = n, h > depth.hyps else { return nil }
        return try t.intern(.hyp(h + 1, a))
    }
}

struct Equalities {
    let base: Base

    func rewrite(_ e: Equality, _ n: Node, was id: NodeID, in t: inout Table) throws -> NodeID {
        let first = children(n)[0]
        switch e {
        case .reflexive:
            guard case .isaReflexive(let f) = n, let T = t.type(of: f) else { throw LogicError.notCongruence(first) }
            if overArguments(T) {
                guard case .isaReflexive(let stated) = t[id] else { throw LogicError.notCongruence(first) }
                return try Functions(base: base).reflexive(T, stated, in: &t)
            }
            if T == .i { return try atI(e, try sidesAtI(id, t), [], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.instance(.iffRefl, [f], in: &t)

        case .symmetric:
            guard case .isaSymmetric(let T, let p) = n else { throw LogicError.notCongruence(first) }
            if overArguments(T) { return try Functions(base: base).symmetric(T, p, was: id, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            return try base.applied(.iffSymm, try sidesAtO(p, in: t), [p], in: &t)

        case .transitive:
            guard case .isaTransitive(let T, let p, let q) = n else { throw LogicError.notCongruence(first) }
            if overArguments(T) { return try Functions(base: base).transitive(T, p, q, was: id, in: &t) }
            if T == .i { return try atI(e, try sidesAtI(id, t), [p, q], in: &t) }
            guard T == .o else { throw LogicError.notCongruence(first) }
            let ab = try sidesAtO(p, in: t)
            let bc = try sidesAtO(q, in: t)
            return try base.applied(.iffTrans, ab + [bc[1]], [p, q], in: &t)
        }
    }

    /// Pure's equality at `i` on values: base's `eq_*` at the sides' values.
    func atI(_ e: Equality, _ sides: [NodeID], _ premises: [NodeID], in t: inout Table) throws -> NodeID {
        let values = try sides.map { try value(of: $0, in: &t) }
        switch e {
        case .reflexive: return try base.claimed(.eqRefl, [values[0]], [], in: &t)
        case .symmetric: return try base.claimed(.eqSymm, values, premises, in: &t)
        case .transitive: return try base.claimed(.eqTrans, values, premises, in: &t)
        }
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
    return try t.intern(.folCut(general, body: opened))
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
    return try t.intern(.folCut(h, body: try t.intern(.folClassicalAbsurd(a, body: absurd))))
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
