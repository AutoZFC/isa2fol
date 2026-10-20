import IR

@frozen
public enum MeetingError: Error, Equatable, Sendable {
    case unmet(NodeID)
    case misaligned(NodeID)
    case misproved(String)
}

/// Which terms cross between their naming and their values: those holding the free variables at these positions of
/// the lemma, or the closed ones.
enum Moving: Hashable {
    case variables([Int])
    case closed
}

/// DESIGN "Linear proof size", 2: a formula's form naming the moving terms against its form holding their values, over
/// its skeleton — its other fixed terms plain variables — premised on the values' facts. `toValues`: from the named.
struct Meeting: Request {
    let formula: NodeID
    let types: [IRType]
    let moving: Moving
    let keep: [Int]
    let toValues: Bool
    let name: String

    var named: Mode {
        switch moving {
        case .closed: .statement
        case .variables(let positions): .proof(0, naming: Set((positions + keep).map { types.count - 1 - $0 }))
        }
    }

    var valued: Mode {
        .proof(0, naming: Set(keep.map { types.count - 1 - $0 }))
    }

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Meeting {
        Meeting(formula: try f(formula), types: types, moving: moving, keep: keep, toValues: toValues, name: name)
    }

}

func statement(_ m: Meeting, in t: inout Table) throws -> NodeID {
    let a = try formula(m.formula, m.named, in: &t)
    let b = try formula(m.formula, m.valued, in: &t)
    let crossing = try ordered(try values(in: b, &t), &t)
    let body = try t.intern(.folImplies(m.toValues ? a : b, m.toValues ? b : a))
    return try universal(m.types, guards: true, try fixing(crossing, in: body, by: .premise, in: &t), in: &t)
}

/// The values, each after the values its fact holds.
func ordered(_ roots: [NodeID], _ t: inout Table) throws -> [NodeID] {
    var found = [NodeID]()
    var met = Set<NodeID>()
    func add(_ v: NodeID, _ t: inout Table) throws {
        guard !met.contains(v) else { return }
        for w in try values(in: try valueFact(v, in: &t), &t) where w != v { try add(w, &t) }
        if met.insert(v).inserted { found.append(v) }
    }
    for v in roots { try add(v, &t) }
    return found
}

/// `p`, proving the formula `psi`'s form naming its moving terms (or, `toValues` false, holding their values), at a
/// proof's site; `at(k)` the term standing for `psi`'s free variable `k` there. The other form, through the formula's
/// lemma; `p` itself where nothing moves.
func met(
    _ p: NodeID,
    _ psi: NodeID,
    moving: Moving,
    at: [Int: NodeID] = [:],
    drop: Int = 0,
    keep: Set<Int> = [],
    toValues: Bool,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    in t: inout Table,
) throws -> NodeID {
    let rootMoving: Mode =
        switch moving {
        case .closed: .statement
        case .variables(let ks): .proof(0, naming: Set(ks).union(keep))
        }
    let s = try skeleton(psi, { x, d, t in isValued(x, t) && rootMoving.deeper(d).valued(x, in: t) }, in: &t)
    let c = try closed(s.formula, in: &t)
    let positions: Moving =
        switch moving {
        case .closed: .closed
        case .variables(let ks):
            .variables(c.variables.indices.filter { j in
                if case .isaBound(let k, _) = t[c.variables[j]], k < s.width { return ks.contains(k) }
                if case .isaPropBound(let k) = t[c.variables[j]], k < s.width { return ks.contains(k) }
                return false
            })
        }
    let kept = c.variables.indices.filter { j in
        if case .isaBound(let k, _) = t[c.variables[j]], k < s.width { return keep.contains(k) }
        if case .isaPropBound(let k) = t[c.variables[j]], k < s.width { return keep.contains(k) }
        return false
    }
    let request = Meeting(
        formula: c.term,
        types: c.types,
        moving: positions,
        keep: kept,
        toValues: toValues,
        name: "MEET_\(fingerprint(c.term, t))_\(name(positions))_K\(kept.map(String.init).joined(separator: "_"))\(toValues ? "" : "_N")",
    )
    if try formula(c.term, request.named, in: &t) == formula(c.term, request.valued, in: &t) { return p }
    var replacement = [Int: NodeID]()
    for k in 0..<s.width {
        if let a = at[k] { replacement[k] = a
            continue
        }
        guard k >= drop else { throw MeetingError.unmet(psi) }
        replacement[k] = try variable(psi, k, minus: drop, &t)
    }
    for (j, param) in s.params.enumerated() { replacement[s.width + j] = try substitute(param, replacement, in: &t) }
    let frees = try c.variables.map { x -> NodeID in
        let k: Int
        switch t[x] {
        case .isaBound(let i, _), .isaPropBound(let i): k = i
        default: throw MeetingError.unmet(x)
        }
        guard let term = replacement[k] else { throw MeetingError.unmet(x) }
        if t.type(of: term) == .o { return try formula(term, .proof(0), in: &t) }
        return try value(of: term, in: &t)
    }
    let b = try formula(c.term, request.valued, in: &t)
    let crossing = try ordered(try values(in: b, &t), &t)
    var lemma = try instantiated(
        try cited(request, try statement(request, in: &t), &t),
        at: frees,
        c.types,
        guards: true,
        guardOf: guardOf,
        in: &t,
    )
    let skeletonVariables = c.variables
    for v in crossing {
        guard case .isaValue(let term) = t[v] else { throw MeetingError.unmet(v) }
        let site = try valueNode(
            try substitute(try instantiateClosed(term, skeletonVariables, replacement, &t), [:], in: &t),
            in: &t,
        )
        lemma = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(lemma, site)), try fact(of: site, in: &t)))
    }
    return try t.intern(.folImpliesElim(lemma, p))
}

/// `psi`'s loose variable `k` as it stands at its root, `minus` binders shallower.
private func variable(_ psi: NodeID, _ k: Int, minus: Int, _ t: inout Table) throws -> NodeID {
    for v in freeVariables(psi, in: t) where v.index == k {
        switch v.variable {
        case .isaBound(_, let T): return try t.intern(.isaBound(k - minus, T))
        case .isaPropBound: return try t.intern(.isaPropBound(k - minus))
        default: break
        }
    }
    return try t.intern(.folBound(k - minus))
}

private func name(_ m: Moving) -> String {
    switch m {
    case .closed: "C"
    case .variables(let ks): ks.map(String.init).joined(separator: "_")
    }
}

/// A term at the closed formula's root, its variables those of `variables`, at the site: each replaced by its term
/// there.
private func instantiateClosed(
    _ term: NodeID,
    _ variables: [NodeID],
    _ replacement: [Int: NodeID],
    _ t: inout Table,
) throws -> NodeID {
    var site = [Int: NodeID]()
    let n = variables.count
    for (j, x) in variables.enumerated() {
        let k: Int
        switch t[x] {
        case .isaBound(let i, _), .isaPropBound(let i): k = i
        default: throw MeetingError.unmet(x)
        }
        guard let r = replacement[k] else { throw MeetingError.unmet(x) }
        site[n - 1 - j] = r
    }
    return try substitute(term, site, in: &t)
}

/// `x` with each loose variable `k` replaced by `replacement[k]`, as it stands at `x`'s root.
func substitute(_ x: NodeID, _ replacement: [Int: NodeID], in t: inout Table) throws -> NodeID {
    if replacement.isEmpty || t.looseBound(of: x) == 0 { return x }
    return try transform(x, Substitute(replacement: replacement), in: &t)
}

private struct Substitute: Rule {
    let replacement: [Int: NodeID]

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard let v = t[id].boundVariable, v.namespace == .term, v.index >= depth.terms else { return nil }
        guard let r = replacement[v.index - depth.terms] else { throw MeetingError.unmet(id) }
        return try shift(r, by: depth.terms, in: &t)
    }

    func after(_ n: Node, was _: NodeID, context _: Depth, in t: inout Table) throws -> NodeID? {
        guard case .isaVarApp(let head, let args) = n, case .isaAbs = t[head] else { return nil }
        return try beta(head, args, in: &t)
    }
}

public struct MeetingProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "meeting"

    public func owns(_ l: Lemma) -> Owned? {
        l.request is Meeting || l.request is Instantiation || l.request is Arguments || l.request is Leibniz
            ? .rule
            : nil
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _: [Definition],
        _: [String: NodeID],
        in t: inout Table,
    ) throws -> Proved {
        let proofs = MeetingProofs(base: base)
        let proof: NodeID
        do {
            switch l.request {
            case let m as Meeting: proof = try proofs.prove(m, in: &t)
            case let m as Instantiation: proof = try proofs.prove(m, in: &t)
            case let a as Arguments: proof = try proofs.prove(a, in: &t)
            case let l as Leibniz: proof = try proofs.prove(l, in: &t)
            default: throw MeetingError.misproved(l.name)
            }
        } catch MeetingError.unmet {
            return .unbuilt
        }
        guard t.conclusion(of: proof) == statement else { throw MeetingError.misproved(l.name) }
        return .proof(proof)
    }

    public func defines(_: Defined) -> Owned? {
        nil
    }

    public func define(_ c: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        throw MeetingError.misproved(c.definitionName)
    }

    let base: Base
}

struct MeetingProofs {
    let base: Base

    func prove(_ a: Arguments, in t: inout Table) throws -> NodeID {
        var f = Frame()
        let guards = try frees(a.types, &f, &t)
        let depth = f.scope.depth
        let k = f.fix(nil)
        let h = f.assume(try classDefinition(
            try f.scope.lift(a.lambda, from: depth, in: &t),
            K: try f.variable(k, in: &t),
            in: &t,
        ))
        let frame = f
        let at = try LambdaProofs(base: base).classAtArguments(a.lambda, from: depth, k, h, f, guardOf: { x, _, t in
            for (level, g) in guards where try frame.variable(level, in: &t) == x { return try frame.hypothesis(
                g,
                in: &t,
            ) }
            throw MeetingError.unmet(x)
        }, in: &t)
        return try f.close(at, in: &t)
    }

    func prove(_ m: Instantiation, in t: inout Table) throws -> NodeID {
        var outer = Frame()
        let guards = try frees(m.types, &outer, &t)
        let k = m.types.count - 1 - m.variable
        let P = try t.intern(.isaBound(k, m.types[m.variable]))
        let h = outer.assume(try classDefinition(m.lambda, K: P, in: &t))
        let a = try formula(m.formula, m.named, in: &t)
        let b = try formula(try m.reduced(m.formula, &t), m.valued, in: &t)
        let crossing = try ordered(try values(in: b, &t), &t)
        var f = Frame(outer.scope)
        let ha = f.assume(m.forward ? a : b)
        let walk = Meet(
            base: base,
            beta: Meet.Beta(
                variable: k,
                lambda: m.lambda,
                definition: try outer.hypothesis(h, in: &t),
                root: outer.scope,
            ),
            guards: guards,
            root: outer.scope,
            premised: Set(crossing),
        )
        let p = try walk.convert(
            m.formula,
            named: m.named,
            valued: m.valued,
            forward: m.forward,
            try f.hypothesis(ha, in: &t),
            f.scope,
            &t,
        )
        let inner = try f.close(p, in: &t)
        return try outer.close(try fixing(crossing, in: inner, by: .premise, in: &t), in: &t)
    }

    func prove(_ m: Meeting, in t: inout Table) throws -> NodeID {
        var outer = Frame()
        let guards = try frees(m.types, &outer, &t)
        let a = try formula(m.formula, m.named, in: &t)
        let b = try formula(m.formula, m.valued, in: &t)
        let crossing = try ordered(try values(in: b, &t), &t)
        var f = Frame(outer.scope)
        let h = f.assume(m.toValues ? a : b)
        let walk = Meet(base: base, guards: guards, root: outer.scope)
        let p = try walk.convert(
            m.formula,
            named: m.named,
            valued: m.valued,
            forward: m.toValues,
            try f.hypothesis(h, in: &t),
            f.scope,
            &t,
        )
        let inner = try f.close(p, in: &t)
        return try outer.close(try fixing(crossing, in: inner, by: .premise, in: &t), in: &t)
    }

    private func frees(_ types: [IRType], _ f: inout Frame, _ t: inout Table) throws -> [Int: Int] {
        var guards = [Int: Int]()
        for T in types {
            let v = f.fix(T)
            if T != .i, T != .o, let g = try guarded(try f.variable(v, in: &t), T, in: &t) { guards[v] = f.assume(g) }
        }
        return guards
    }

}

/// One walk over a formula, from its named form to its valued form (`forward`) or back: each connective by its own
/// introduction and elimination, each atom by aligning its two namings.
struct Meet {
    /// The class variable `P` the named form holds where the valued form holds the λ, `λ`'s definition at `P`
    /// proved at `root`.
    struct Beta {
        let variable: Int
        let lambda: NodeID
        let definition: NodeID
        let root: Scope
    }

    let base: Base
    var beta: Beta?
    var guards = [Int: Int]()
    var root = Scope()
    var premised = Set<NodeID>()

    /// ⚠ A LEMMA'S OWN VARIABLE HAS ITS GUARD AS A HYPOTHESIS OF ITS PROOF, NEVER `isaGuard`: Fol finds no guarded
    /// binder for it.
    func guardOf(_ x: NodeID, _ T: IRType, _ s: Scope, _ t: inout Table) throws -> NodeID {
        if case .isaBound(let k, _) = t[x], s.depth - 1 - k < root.depth, let h = guards[s.depth - 1 - k] {
            return try lifted(try root.hypothesis(h, in: &t), from: root, to: s, in: &t)
        }
        return try isaGuard(x, T, &t)
    }

    func reduced(_ x: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID {
        guard let beta else { return x }
        let k = beta.variable + s.depth - beta.root.depth
        guard looseIndices(x, in: t).contains(k) else { return x }
        let lambda = try lifted(beta.lambda, from: beta.root, to: s, in: &t)
        return try instantiate(try abstractIndex(x, k, in: &t), with: lambda, in: &t)
    }

    func holdsP(_ x: NodeID, _ s: Scope, _ t: Table) -> Bool {
        guard let beta else { return false }
        return looseIndices(x, in: t).contains(beta.variable + s.depth - beta.root.depth)
    }

    func convert(
        _ phi: NodeID,
        named: Mode,
        valued: Mode,
        forward: Bool,
        _ p: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let a = try formula(phi, named, in: &t)
        let b = try formula(try reduced(phi, s, &t), valued, in: &t)
        if a == b { return p }
        let target = forward ? b : a
        let source = forward ? a : b
        let back = { (x: NodeID, q: NodeID, s: Scope, t: inout Table) throws -> NodeID in
            try convert(x, named: named, valued: valued, forward: !forward, q, s, &t)
        }
        let on = { (x: NodeID, q: NodeID, s: Scope, t: inout Table) throws -> NodeID in
            try convert(x, named: named, valued: valued, forward: forward, q, s, &t)
        }
        let toForm = { (x: NodeID, t: inout Table) throws -> NodeID in
            forward ? try formula(try reduced(x, s, &t), valued, in: &t) : try formula(x, named, in: &t)
        }
        let fromForm = { (x: NodeID, t: inout Table) throws -> NodeID in
            forward ? try formula(x, named, in: &t) : try formula(try reduced(x, s, &t), valued, in: &t)
        }
        if Reify().names(Pattern(t[phi], in: t)) {
            if try applies(phi, named, s, &t) {
                return try atValues(phi, named: named, valued: valued, forward: forward, p, s, &t)
            }
            return try Atom(meet: self, named: named, valued: valued)
                .convert(phi, to: try reduced(phi, s, &t), forward: forward, p, s, &t)
        }
        if
            case .isaConst(.primitive(.pure(.eq)), .fn(let F, _), let args) = t[phi], args.count == 2,
            overArguments(F)
        {
            return try on(try Functions.isaPointwise(F, args[0], args[1], in: &t), p, s, &t)
        }
        switch t[phi] {
        case .folAnd(let x, let y):
            return try t.intern(.folAndIntro(
                try on(x, try t.intern(.folAndElimL(p)), s, &t),
                try on(y, try t.intern(.folAndElimR(p)), s, &t),
            ))

        case .folOr(let x, let y):
            let tx = try toForm(x, &t)
            let ty = try toForm(y, &t)
            var gx = Frame(s)
            let hx = gx.assume(try fromForm(x, &t))
            let left = try gx.close(
                try t.intern(.folOrIntroL(try on(x, try gx.hypothesis(hx, in: &t), gx.scope, &t), ty)),
                in: &t,
            )
            var gy = Frame(s)
            let hy = gy.assume(try fromForm(y, &t))
            let right = try gy.close(
                try t.intern(.folOrIntroR(tx, try on(y, try gy.hypothesis(hy, in: &t), gy.scope, &t))),
                in: &t,
            )
            return try t.intern(.folOrElim(p, left, right))

        case .folImplies(let x, let y):
            var g = Frame(s)
            let h = g.assume(try toForm(x, &t))
            let premise = try back(x, try g.hypothesis(h, in: &t), g.scope, &t)
            let applied = try t.intern(.folImpliesElim(try lifted(p, from: s, to: g.scope, in: &t), premise))
            return try g.close(try on(y, applied, g.scope, &t), in: &t)

        case .folNot(let x):
            let tx = try toForm(x, &t)
            var g = Frame(s)
            let h = g.assume(tx)
            let premise = try back(x, try g.hypothesis(h, in: &t), g.scope, &t)
            let absurd = try t.intern(.folNotElim(try lifted(p, from: s, to: g.scope, in: &t), premise))
            return try t.intern(.folNotIntro(tx, body: absurd))

        case .folIff(let x, let y):
            let one = { (l: NodeID, r: NodeID, elim: (NodeID, NodeID) -> Node, t: inout Table) throws -> NodeID in
                var g = Frame(s)
                let h = g.assume(try toForm(l, &t))
                let premise = try back(l, try g.hypothesis(h, in: &t), g.scope, &t)
                let q = try t.intern(elim(try lifted(p, from: s, to: g.scope, in: &t), premise))
                return try g.close(try on(r, q, g.scope, &t), in: &t)
            }
            return try t.intern(.folIffIntro(
                try one(x, y, { .folIffElimL($0, $1) }, &t),
                try one(y, x, { .folIffElimR($0, $1) }, &t),
            ))

        case .ifolAll(.i, let body):
            var g = Frame(s)
            let x = g.fix(.i)
            let at = try t.intern(.isaAllElim(try lifted(p, from: s, to: g.scope, in: &t), try g.variable(x, in: &t)))
            let q = try convert(
                body,
                named: named.deeper(1),
                valued: valued.deeper(1),
                forward: forward,
                at,
                g.scope,
                &t,
            )
            return try g.close(q, in: &t)

        case .ifolAll(let T, let body) where T != .o && isObject(T):
            var g = Frame(s)
            let x = g.fix(T)
            let v = try g.variable(x, in: &t)
            var at = try t.intern(.folForallElim(try lifted(p, from: s, to: g.scope, in: &t), v))
            if let guardFormula = try guarded(v, T, in: &t) {
                at = try t.intern(.folImpliesElim(at, try t.intern(.isaGuard(v, guardFormula))))
            }
            let q = try convert(
                body,
                named: named.deeper(1),
                valued: valued.deeper(1),
                forward: forward,
                at,
                g.scope,
                &t,
            )
            return try t.intern(.isaAllIntro(T, body: q))

        case .ifolEx(.i, let body):
            var g = Frame(s)
            let (w, h) = try g.open(p, in: &t)
            let q = try convert(
                body,
                named: named.deeper(1),
                valued: valued.deeper(1),
                forward: forward,
                try g.hypothesis(h, in: &t),
                g.scope,
                &t,
            )
            let lifted = try g.scope.lift(target, from: s.depth, in: &t)
            guard case .ifolEx(.i, let shape) = t[lifted] else { throw MeetingError.unmet(phi) }
            return try g.close(try t.intern(.isaExIntro(q, try g.variable(w, in: &t), body: shape)), in: &t)

        case .isaPropAll(let body):
            var g = Frame(s)
            let e = g.fix(nil)
            let h = g.assume(try truth(try g.variable(e, in: &t), in: &t))
            let at = try t.intern(.folImpliesElim(
                try t.intern(.folForallElim(try lifted(p, from: s, to: g.scope, in: &t), try g.variable(e, in: &t))),
                try g.hypothesis(h, in: &t),
            ))
            let q = try convert(
                body,
                named: named.deeper(1),
                valued: valued.deeper(1),
                forward: forward,
                at,
                g.scope,
                &t,
            )
            return try g.close(q, in: &t)

        case .folBottom, .folPred:
            guard source == target else { throw MeetingError.unmet(phi) }
            return p

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
             .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropIntro, .isaPropBound, .isaHidden, .folImpliesIntro,
             .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .folAndIntro, .folAndElimL, .folAndElimR,
             .folOrIntroL, .folOrIntroR, .folOrElim, .folBottomElim, .isaGuard, .isaExIntro, .isaExElim, .folNot,
             .folBound, .folForall, .folExists, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro,
             .folForallElim,
             .folExistsIntro, .folExistsElim, .folCut, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
             .folLetterAbs, .isaValue, .isaValueFact:
            throw MeetingError.unmet(phi)
        }
    }

    /// The λ's class `P` at `refs`: `P(refs) ↔ body(refs)`, the body naming the terms holding them; for a function
    /// λ, `function(P) ∧ ∀τ. tuple(refs, τ) → ∀r. apply(τ, r, P) ↔ ⟦r = body(refs)⟧`.
    func arguments(
        _ lambda: NodeID,
        _ P: NodeID,
        _ definition: NodeID,
        _ refs: [NodeID],
        _ scope: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let s = try skeleton(lambda, { x, d, t in isValued(x, t) && Mode.proof(d).valued(x, in: t) }, in: &t)
        let c = try closed(s.formula, in: &t)
        let request = Arguments(lambda: c.term, types: c.types, name: "ARGS_" + fingerprint(c.term, t))
        let at = try c.variables.map { x -> NodeID in
            guard case .isaBound(let k, _) = t[x], k >= s.width else { return try formula(x, .proof(0), in: &t) }
            return try valueNode(s.params[k - s.width], in: &t)
        }
        var lemma = try instantiated(
            try cited(request, try statement(request, base: base, in: &t), &t),
            at: at,
            c.types,
            guards: true,
            guardOf: { x, T, t in try guardOf(x, T, scope, &t) },
            in: &t,
        )
        lemma = try t.intern(.folImpliesElim(try t.intern(.folForallElim(lemma, P)), definition))
        for r in refs { lemma = try t.intern(.isaAllElim(lemma, r)) }
        return lemma
    }

    /// Whether the atom applies the class variable at its own level: `P(t⃗)`, or a term `F(t⃗)` its naming holds.
    private func applies(_ phi: NodeID, _ named: Mode, _ s: Scope, _ t: inout Table) throws -> Bool {
        guard beta != nil else { return false }
        if case .isaVarApp(let head, _) = t[phi], holdsP(head, s, t) { return true }
        var a = Naming(mode: named)
        _ = try a.atom(t[phi], in: &t)
        return a.ranges.contains { r in
            guard case .isaVarApp(let head, _) = t[r.term] else { return false }
            return holdsP(head, s, t)
        }
    }

    /// An atom applying the class variable, against its reduced form: through the reduced form's value form at `s`,
    /// each term at its level a value, met to the reduced form's names by its own lemma. The values fixed at the atom
    /// are those only its conversion holds: the lemma premises the others, or the atom's premise or conclusion holds
    /// them, an enclosing atom fixing those.
    private func atValues(
        _ phi: NodeID,
        named: Mode,
        valued: Mode,
        forward: Bool,
        _ p: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let target = try reduced(phi, s, &t)
        let moving: Moving = if case .statement = valued { .closed } else { .variables(Array(0..<depth(of: valued))) }
        let guards = { (x: NodeID, T: IRType, t: inout Table) throws -> NodeID in try guardOf(x, T, s, &t) }
        let proof: NodeID
        if forward {
            let q = try crossed(phi, named, forward: true, p, s, &t)
            proof = try met(q, target, moving: moving, toValues: false, guardOf: guards, in: &t)
        } else {
            let q = try met(p, target, moving: moving, toValues: true, guardOf: guards, in: &t)
            proof = try crossed(phi, named, forward: false, q, s, &t)
        }
        guard let given = t.conclusion(of: p), let concluded = t.conclusion(of: proof) else {
            throw TableError.expectedStep(proof)
        }
        let outside = Set(try ordered(try values(in: given, &t) + values(in: concluded, &t), &t))
        let depth = s.depth - root.depth
        let here = try ordered(try values(in: proof, &t), &t).filter { v in
            guard !outside.contains(v) else { return false }
            return try lowestLoose(v, in: t) < depth || !premised.contains(try shift(v, by: -depth, in: &t))
        }
        return try fixing(here, in: proof, by: .existence(base), guardOf: guards, in: &t)
    }

    /// The atom against its reduced form's value form at `s`: `P(t⃗)` by β at its arguments' values, any other atom by
    /// its terms' values.
    private func crossed(
        _ phi: NodeID,
        _ named: Mode,
        forward: Bool,
        _ p: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let atom = Atom(meet: self, named: named, valued: .proof(0))
        guard case .isaVarApp(let head, let args) = t[phi], holdsP(head, s, t) else {
            return try atom.convert(phi, to: try reduced(phi, s, &t), forward: forward, p, s, &t)
        }
        let sites = try args.map { try reduced($0, s, &t) }
        let refs = try sites.map { try value(of: $0, in: &t) }
        let atValues = try t.intern(.isaVarApp(head: head, args: sites))
        if forward {
            let q = try atom.convert(phi, to: atValues, forward: true, p, s, &t)
            return try betaCore(refs, sites: sites, forward: true, q, s, &t)
        }
        let q = try betaCore(refs, sites: sites, forward: false, p, s, &t)
        return try atom.convert(phi, to: atValues, forward: false, q, s, &t)
    }

    /// `P(refs)` against the λ's body there, `sites` the terms the refs hold: the λ's class at its arguments (`ARGS`),
    /// then the body's own lemma moving them to their values.
    private func betaCore(
        _ refs: [NodeID],
        sites args: [NodeID],
        forward: Bool,
        _ p: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        guard let beta else { throw MeetingError.unmet(p) }
        let lambda = try lifted(beta.lambda, from: beta.root, to: s, in: &t)
        let P = try t.intern(.isaBound(beta.variable + s.depth - beta.root.depth, t.type(of: beta.lambda)!))
        let definition = try lifted(beta.definition, from: beta.root, to: s, in: &t)
        let at = try arguments(lambda, P, definition, refs, s, &t)
        let n = args.count
        let xs = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
        let body = try IR.beta(try shift(lambda, by: n, in: &t), xs, in: &t)
        var sites = [Int: NodeID]()
        for j in 0..<n { sites[n - 1 - j] = args[j] }
        let moving = Moving.variables(Array(0..<n))
        let guards = { (x: NodeID, T: IRType, t: inout Table) throws -> NodeID in try guardOf(x, T, s, &t) }
        if forward {
            let named = try t.intern(.folIffElimL(at, p))
            return try met(named, body, moving: moving, at: sites, drop: n, toValues: true, guardOf: guards, in: &t)
        }
        let back = try met(p, body, moving: moving, at: sites, drop: n, toValues: false, guardOf: guards, in: &t)
        return try t.intern(.folIffElimR(at, back))
    }

}

/// An atom's two namings, aligned: a term the named form names and the valued form holds the value of is a block of
/// the named form's binders the valued form lacks, its top value equal to the value by the value's fact; every other
/// binder both have, its constraint carried between the two by TUPLE_CONG at a tuple, by the walk at a class or a truth
/// set.
private struct Atom {
    let meet: Meet
    let named: Mode
    let valued: Mode

    var base: Base {
        meet.base
    }

    /// `p` proving `phi`'s named form, or `target`'s valued form: the other. `target` is `phi` as the valued form holds
    /// it, the class variable reduced.
    func convert(_ phi: NodeID, to target: NodeID, forward: Bool, _ p: NodeID, _ s: Scope, _ t: inout Table) throws
        -> NodeID
    {
        var a = Naming(mode: named)
        let coreA = try a.atom(t[phi], in: &t)
        var b = Naming(mode: valued)
        let coreB = try b.atom(t[target], in: &t)
        let formA = try a.chain.formula(coreA, in: &t)
        let formB = try b.chain.formula(coreB, in: &t)
        if formA == formB { return p }
        var crossing = [(binders: Range<Int>, term: NodeID)]()
        for r in a.ranges {
            let reduced = try meet.reduced(r.term, s, &t)
            if isVariable(reduced, t) || valued.valued(reduced, in: t) {
                crossing.append(r)
            } else if case .isaVarApp(let head, _) = t[r.term], meet.holdsP(head, s, t) {
                throw MeetingError.misaligned(r.term)
            }
        }
        var owner = [Int?](repeating: nil, count: a.chain.binders.count)
        for (j, r) in crossing.enumerated() {
            for k in r.binders where owner[k] == nil || crossing[owner[k]!].binders.count > r.binders.count {
                owner[k] = j
            }
        }
        guard a.chain.binders.indices.count(where: { owner[$0] == nil }) == b.chain.binders.count else {
            throw MeetingError.unmet(phi)
        }
        var st = State(
            f: Frame(s),
            levels: Array(repeating: nil, count: a.chain.binders.count),
            facts: Array(repeating: nil, count: a.chain.binders.count),
        )
        var held = p
        var heldScope = s
        var rest = forward ? formB : formA
        var restScope = s
        for k in a.chain.binders.indices {
            if let j = owner[k] {
                if forward {
                    let (w, h) = try st.f.open(try opening(a.pieces, k, st, s, &t), in: &t)
                    (st.levels[k], st.facts[k]) = (w, h)
                    let at = try eliminate(
                        try lifted(held, from: heldScope, to: st.f.scope, in: &t),
                        try st.ref(k, &t),
                        &t,
                    )
                    held = try t.intern(.folImpliesElim(at, try st.fact(k, &t)))
                    heldScope = st.f.scope
                } else {
                    (st.levels[k], st.facts[k]) = try fixAssume(&rest, &restScope, &st.f, &t)
                }
                if k == crossing[j].binders.upperBound - 1 {
                    let term = try lifted(try meet.reduced(crossing[j].term, s, &t), from: s, to: st.f.scope, in: &t)
                    let v = isVariable(term, t) ? term : try valueNode(term, in: &t)
                    if case .isaVarApp(let head, _) = t[crossing[j].term], meet.holdsP(head, s, t) {
                        st.equal[k] = (v, try appliedEquality(v, crossing[j], a, st, s, &t), st.f.scope)
                    } else {
                        st.equal[k] = (v, try valueEquality(v, crossing[j], a, st, s, &t), st.f.scope)
                    }
                }
                continue
            }
            (st.levels[k], st.facts[k]) = try fixAssume(&rest, &restScope, &st.f, &t)
            let at = try eliminate(try lifted(held, from: heldScope, to: st.f.scope, in: &t), try st.ref(k, &t), &t)
            guard case .folImplies(let wanted, _)? = t.conclusion(of: at).map({ t[$0] }) else {
                throw MeetingError.misaligned(phi)
            }
            let premise = try carried(a.pieces[k], k, try st.fact(k, &t), wanted, toValued: !forward, st, s, &t)
            held = try t.intern(.folImpliesElim(at, premise))
            heldScope = st.f.scope
        }
        let have = try lifted(held, from: heldScope, to: st.f.scope, in: &t)
        let want = try lifted(rest, from: restScope, to: st.f.scope, in: &t)
        guard let haveCore = t.conclusion(of: have) else { throw MeetingError.misaligned(phi) }
        var core = have
        if haveCore != want {
            let state = st
            let moved = try congruent(haveCore, want, base, { l, r, t in try equality(l, r, state, &t) }, &t)
            core = try t.intern(.folIffElimL(moved, have))
        }
        return try st.f.close(core, in: &t)
    }

    /// ⚠ A BINDER'S VARIABLE AND HYPOTHESIS ARE KEPT AS LEVELS, NEVER AS NODES: the frame grows past them, and a node
    /// taken earlier names another binder.
    private struct State {
        var f: Frame
        var levels: [Int?]
        var facts: [Int?]
        var equal = [Int: (value: NodeID, proof: NodeID, scope: Scope)]()

        func ref(_ k: Int, _ t: inout Table) throws -> NodeID {
            guard let l = levels[k] else { throw MeetingError.misaligned(try t.intern(.folBottom)) }
            return try f.variable(l, in: &t)
        }

        func fact(_ k: Int, _ t: inout Table) throws -> NodeID {
            guard let h = facts[k] else { throw MeetingError.misaligned(try t.intern(.folBottom)) }
            return try f.hypothesis(h, in: &t)
        }
    }

    /// `⟦r = body(t⃗)⟧`'s valued form, `r` the named form's value of `P(t⃗)` at `τ`: the λ's class at the arguments,
    /// then the body's lemma moving them to their values.
    private func applied(
        _ term: NodeID,
        _ tau: NodeID,
        _ tauFact: NodeID,
        _ r: NodeID,
        _ rFact: NodeID,
        _ st: State,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        guard let beta = meet.beta, case .isaVarApp(_, let args) = t[term] else { throw MeetingError.unmet(term) }
        let inner = st.f.scope
        guard let tupled = t.conclusion(of: tauFact) else { throw TableError.expectedStep(tauFact) }
        let (entries, _) = try tupleEntries(tupled, &t)
        let refs = try entries.map { try valuedName($0, st, &t) }
        let atRefs = refs == entries ? tauFact : try tupleCarried(
            tauFact,
            tupled,
            try tuple(refs, tau, in: &t),
            st,
            &t,
        )
        let lambda = try lifted(beta.lambda, from: beta.root, to: inner, in: &t)
        guard let T = t.type(of: beta.lambda) else { throw MeetingError.unmet(term) }
        let P = try t.intern(.isaBound(beta.variable + inner.depth - beta.root.depth, T))
        let definition = try lifted(beta.definition, from: beta.root, to: inner, in: &t)
        let both = try meet.arguments(lambda, P, definition, [], inner, &t)
        var at = try t.intern(.folAndElimR(both))
        for x in refs { at = try t.intern(.isaAllElim(at, x)) }
        at = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(at, tau)), atRefs))
        at = try t.intern(.isaAllElim(at, r))
        let named = try t.intern(.folIffElimL(at, rFact))
        let n = args.count
        let xs = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
        let equation = try Lowering.equation(
            try shift(r, by: n, in: &t),
            try IR.beta(try shift(lambda, by: n, in: &t), xs, in: &t),
            in: &t,
        )
        let bound = depth(of: valued) + inner.depth - s.depth
        var sites = [Int: NodeID]()
        var moving = [Int]()
        var keep = Set(n..<(n + bound))
        for j in 0..<n {
            let site = if case .isaValue(let x) = t[refs[j]] { x } else { refs[j] }
            sites[n - 1 - j] = site
            if looseIndices(site, in: t).contains(where: { $0 < bound }) { keep.insert(n - 1 - j) } else {
                moving.append(n - 1 - j)
            }
        }
        return try met(
            named,
            equation,
            moving: .variables(moving),
            at: sites,
            drop: n,
            keep: keep,
            toValues: true,
            guardOf: { x, T, t in try meet.guardOf(x, T, inner, &t) },
            in: &t,
        )
    }

    /// An argument's name in the valued form: where the walk has met the named form's variable to the valued form's —
    /// a crossing term's value, a β block's top — that one, else the variable both forms hold.
    private func valuedName(_ x: NodeID, _ st: State, _ t: inout Table) throws -> NodeID {
        for (k, e) in st.equal where try st.ref(k, &t) == x {
            return try lifted(e.value, from: e.scope, to: st.f.scope, in: &t)
        }
        return x
    }

    /// `eq(v, r)`, `v` what the valued form holds for `λ(t⃗)` — its value, or a variable — and `r` the named form's
    /// value of `P(t⃗)`.
    private func appliedEquality(
        _ v: NodeID,
        _ range: (binders: Range<Int>, term: NodeID),
        _: Naming,
        _ st: State,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let tauLevel = range.binders.upperBound - 2
        let rLevel = range.binders.upperBound - 1
        let r = try st.ref(rLevel, &t)
        let equal = try applied(
            range.term,
            try st.ref(tauLevel, &t),
            try st.fact(tauLevel, &t),
            r,
            try st.fact(rLevel, &t),
            st,
            s,
            &t,
        )
        return try base.claimed(.eqSymm, [r, v], [equal], in: &t)
    }

    /// `eq(l, r)` at the state's scope: by a crossing value's fact, in either direction, or reflexivity.
    private func equality(_ l: NodeID, _ r: NodeID, _ st: State, _ t: inout Table) throws -> NodeID {
        if l == r { return try base.claimed(.eqRefl, [l], [], in: &t) }
        for (k, e) in st.equal {
            let at = try st.ref(k, &t)
            let v = try lifted(e.value, from: e.scope, to: st.f.scope, in: &t)
            let proof = try lifted(e.proof, from: e.scope, to: st.f.scope, in: &t)
            if v == l, at == r { return proof }
            if at == l, v == r { return try base.claimed(.eqSymm, [v, at], [proof], in: &t) }
        }
        throw MeetingError.misaligned(l)
    }

    private func eliminate(_ p: NodeID, _ x: NodeID, _ t: inout Table) throws -> NodeID {
        guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        if case .ifolAll(.i, _) = t[c] { return try t.intern(.isaAllElim(p, x)) }
        return try t.intern(.folForallElim(p, x))
    }

    /// The next binder of `rest`, a universal naming at `scope`, fixed in `f`, its constraint assumed.
    private func fixAssume(_ rest: inout NodeID, _ scope: inout Scope, _ f: inout Frame, _ t: inout Table) throws
        -> (Int, Int)
    {
        let here = try lifted(rest, from: scope, to: f.scope, in: &t)
        let body: NodeID
        let set: Bool
        switch t[here] {
        case .ifolAll(.i, let b): (body, set) = (b, true)
        case .folForall(let b): (body, set) = (b, false)
        default: throw MeetingError.misaligned(here)
        }
        let w = f.fix(set ? .i : nil)
        guard case .folImplies(let c, let after) = t[body] else { throw MeetingError.misaligned(here) }
        let h = f.assume(c)
        rest = after
        scope = f.scope
        return (w, h)
    }

    /// The existence of a crossing block's piece, its fact the named form's constraint at the binders so far.
    private func opening(
        _ pieces: [NamedPiece],
        _ k: Int,
        _ st: State,
        _ s: Scope,
        mode: Mode? = nil,
        _ t: inout Table,
    ) throws -> NodeID {
        let named = mode ?? named
        let inner = st.f.scope
        let ref = { (r: Ref, t: inout Table) throws -> NodeID in
            switch r {
            case .outer(let x): try lifted(x, from: s, to: inner, in: &t)
            case .bound(let j): try st.ref(j, &t)
            }
        }
        switch pieces[k] {
        case .setConstant(let c):
            return try setConstantExistence(c, base, &t)

        case .constantClass(let c, let T, let classes):
            let f = ConstantFact(constant: c, type: T, fact: .classExists)
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try classes.map { try ref($0, &t) },
                in: &t,
            )

        case .lambdaClass(let lambda):
            return try classExistence(
                try lifted(lambda, from: s, to: inner, in: &t),
                named.deeper(inner.depth - s.depth),
                base,
                &t,
            )

        case .tuple(let entries):
            let f = TupleFact(arity: entries.count, fact: .existence)
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try entries.map { try ref($0, &t) },
                in: &t,
            )

        case .value(tuple: let tau, cls: let C):
            guard
                case .bound(let kc) = C, case .constantClass(let c, let T, let classes) = pieces[kc],
                case .bound(let kt) = tau, case .tuple(let entries) = pieces[kt]
            else { throw MeetingError.misaligned(try ref(tau, &t)) }
            let f = ConstantFact(constant: c, type: T, fact: .totality)
            let guards = try zip(classes, T.domains.filter { !isEntry($0) }).compactMap { k, D -> NodeID? in
                guard isFunctionClass(D) else { return nil }
                guard case .bound(let kk) = k, case .lambdaClass(let lambda) = pieces[kk] else {
                    throw MeetingError.misaligned(try ref(k, &t))
                }
                let at = try lifted(lambda, from: s, to: inner, in: &t)
                let fact = try functionFact(
                    at,
                    mode: named.deeper(inner.depth - s.depth),
                    base,
                    guardOf: { x, T, t in try meet.guardOf(x, T, inner, &t) },
                    &t,
                )
                return try t.intern(.folImpliesElim(
                    try t.intern(.folForallElim(fact, try ref(k, &t))),
                    try st.fact(kk, &t),
                ))
            }
            let total = try eliminated(
                try eliminated(
                    try cited(f, try statement(f, in: &t), &t),
                    at: try classes.map { try ref($0, &t) },
                    premises: guards,
                    in: &t,
                ),
                at: [try ref(C, &t)],
                premises: [try st.fact(kc, &t)],
                in: &t,
            )
            return try eliminated(
                total,
                at: try (entries + [tau]).map { try ref($0, &t) },
                premises: [try st.fact(kt, &t)],
                in: &t,
            )

        case .applied(tuple: let tau, function: let fn):
            return try eliminated(
                try base.cite(.applyEX, in: &t),
                at: [try lifted(fn, from: s, to: inner, in: &t), try ref(tau, &t)],
                in: &t,
            )

        case .truthSet(let proposition):
            let read = try formula(
                try lifted(proposition, from: s, to: inner, in: &t),
                named.deeper(inner.depth - s.depth),
                in: &t,
            )
            return try base.instance(.truthSetEX, [read], in: &t)
        }
    }

    /// The constraint `wanted` a binder states in one form, from `h`, the other form's at it: `toValued` from the
    /// named.
    private func carried(
        _ piece: NamedPiece,
        _ k: Int,
        _ h: NodeID,
        _ wanted: NodeID,
        toValued: Bool,
        _ st: State,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        guard let have = t.conclusion(of: h) else { throw TableError.expectedStep(h) }
        if have == wanted { return h }
        let inner = st.f.scope
        let d = inner.depth - s.depth
        let raw: NodeID
        switch piece {
        case .tuple:
            return try tupleCarried(h, have, wanted, st, &t)

        case .lambdaClass(let lambda):
            raw = try classDefinition(
                try lifted(lambda, from: s, to: inner, in: &t),
                K: try st.ref(k, &t),
                raw: true,
                in: &t,
            )

        case .truthSet(let proposition):
            let e = try st.ref(k, &t)
            raw = try t.intern(.folAnd(
                try truth(e, in: &t),
                try t.intern(.folIff(try holds(e, in: &t), try lifted(proposition, from: s, to: inner, in: &t))),
            ))

        case .setConstant, .constantClass, .value, .applied:
            throw MeetingError.misaligned(wanted)
        }
        return try meet.convert(
            raw,
            named: named.deeper(d),
            valued: valued.deeper(d),
            forward: toValued,
            h,
            inner,
            &t,
        )
    }

    private func tupleCarried(_ h: NodeID, _ have: NodeID, _ wanted: NodeID, _ st: State, _ t: inout Table) throws
        -> NodeID
    {
        let (xs, tau) = try tupleEntries(have, &t)
        let (ys, tau2) = try tupleEntries(wanted, &t)
        guard tau == tau2, xs.count == ys.count else { throw MeetingError.misaligned(wanted) }
        let eqs = try zip(xs, ys).map { try equality($0, $1, st, &t) }
        let f = TupleFact(arity: xs.count, fact: .congruence)
        let at = try eliminated(try cited(f, try statement(f, in: &t), &t), at: xs + ys, premises: eqs, in: &t)
        return try eliminated(at, at: [tau], premises: [h], in: &t)
    }

    /// `eq(v, r)`, `v` a crossing term's value and `r` its top value in the named form: the value's fact at the term's
    /// own pieces there, each constraint carried to the valued form.
    private func valueEquality(
        _ v: NodeID,
        _ range: (binders: Range<Int>, term: NodeID),
        _ a: Naming,
        _ st: State,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let inner = a.ranges.filter {
            $0.binders != range.binders && $0.binders.lowerBound >= range.binders.lowerBound
                && $0.binders.upperBound <= range.binders.upperBound
        }
        let own = range.binders.filter { k in !inner.contains { $0.binders.contains(k) } }
        var p = try fact(of: v, in: &t)
        for k in own {
            p = try eliminate(p, try st.ref(k, &t), &t)
            guard case .folImplies(let wanted, _)? = t.conclusion(of: p).map({ t[$0] }) else {
                throw MeetingError.misaligned(v)
            }
            let premise = try carried(a.pieces[k], k, try st.fact(k, &t), wanted, toValued: true, st, s, &t)
            p = try t.intern(.folImpliesElim(p, premise))
        }
        return p
    }
}

/// A tuple's formula's entries and its value, as they stand at the formula's root.
func tupleEntries(_ formula: NodeID, _ t: inout Table) throws -> ([NodeID], NodeID) {
    var xs = [NodeID]()
    var x = formula
    var depth = 0
    while true {
        switch t[x] {
        case .ifolAll(.i, let b):
            depth += 1
            x = b

        case .folImplies(let c, let rest):
            if case .folPred(.base("snoc"), let args) = t[c], args.count == 4 {
                xs.append(try shift(args[2], by: -depth, in: &t))
            }
            x = rest

        case .folPred(.base("snoc"), let args) where args.count == 4:
            xs.append(try shift(args[2], by: -depth, in: &t))
            return (xs, try shift(args[3], by: -depth, in: &t))

        case .folPred(.base("zero"), let args) where args.count == 1:
            return ([], try shift(args[0], by: -depth, in: &t))

        default:
            throw MeetingError.misaligned(formula)
        }
    }
}

func setConstantExistence(_ c: Constant, _ base: Base, _ t: inout Table) throws -> NodeID {
    switch c {
    case .primitive(.zf(.zero)): return try base.cite(.zfZeroEX, in: &t)

    case .primitive(.zf(.inf)): return try base.cite(.zfInfEX, in: &t)

    case .defined:
        let f = ConstantFact(constant: c, type: .i, fact: .existence)
        return try cited(f, try statement(f, in: &t), &t)

    case .primitive(.zf(.mem)), .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)),
         .primitive(.pure), .primitive(.ifol), .declared:
        throw TermsError.noFact("\(c.name), a set constant")
    }
}

/// `∃K. def(λ, K)`, `λ` as `mode` holds it: CLASS of its skeleton, the terms `mode` holds the values of its variables.
func classExistence(_ lambda: NodeID, _ mode: Mode, _ base: Base, _ t: inout Table) throws -> NodeID {
    let s = try skeleton(lambda, { x, d, t in isValued(x, t) && mode.deeper(d).valued(x, in: t) }, in: &t)
    let (f, c) = try lambdaFact(s.formula, .classExists, in: &t)
    let at = try c.variables.map { x -> NodeID in
        guard case .isaBound(let k, _) = t[x], k >= s.width else { return try formula(x, .proof(0), in: &t) }
        return try valueNode(s.params[k - s.width], in: &t)
    }
    return try instantiated(
        try cited(f, try statement(f, base: base, in: &t), &t),
        at: at,
        c.types,
        guards: false,
        guardOf: isaGuard,
        in: &t,
    )
}

/// DESIGN "Linear proof size", 2, at a λ: `∀P. ψ` instantiated at `λ`, `P`'s value the λ's class: `ψ` naming the
/// terms holding `P`, against `ψ[λ/P]` holding their values, premised on the class's definition — one lemma per formula
/// and λ, over their skeleton.
struct Instantiation: Request {
    let formula: NodeID
    let lambda: NodeID
    let types: [IRType]
    let variable: Int
    let stated: Bool
    let forward: Bool
    let name: String

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Instantiation {
        Instantiation(
            formula: try f(formula),
            lambda: try f(lambda),
            types: types,
            variable: variable,
            stated: stated,
            forward: forward,
            name: name,
        )
    }
}

/// The binders a mode treats as the formula's own, counted from where it stands.
func depth(of mode: Mode) -> Int {
    switch mode {
    case .statement: 0
    case .proof(let d, _): d
    }
}

/// `ARGS ⟨λ⟩`: a λ's class at its arguments, from its definition.
struct Arguments: Request {
    let lambda: NodeID
    let types: [IRType]
    let name: String

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Arguments {
        Arguments(lambda: try f(lambda), types: types, name: name)
    }
}

func statement(_ a: Arguments, base: Base, in t: inout Table) throws -> NodeID {
    let n = a.types.count
    let K = try t.intern(.folBound(0))
    let lambda = try shift(a.lambda, by: 1, in: &t)
    let body = try t.intern(.folImplies(
        try classDefinition(lambda, K: K, in: &t),
        try atArguments(lambda, K, base: base, in: &t),
    ))
    _ = n
    return try universal(a.types, guards: true, try t.intern(.folForall(body: body)), in: &t)
}

extension Instantiation {
    var named: Mode {
        stated ? .statement : .proof(0, naming: [types.count - 1 - variable])
    }

    var valued: Mode {
        stated ? .statement : .proof(0)
    }

    /// `ψ` and `λ` at the lemma's root, the variables its frees.
    var reduced: (NodeID, inout Table) throws -> NodeID {
        { psi, t in
            let k = types.count - 1 - variable
            return try instantiate(try abstractIndex(psi, k, in: &t), with: lambda, in: &t)
        }
    }
}

func statement(_ m: Instantiation, in t: inout Table) throws -> NodeID {
    let k = m.types.count - 1 - m.variable
    let P = try t.intern(.isaBound(k, m.types[m.variable]))
    let a = try formula(m.formula, m.named, in: &t)
    let b = try formula(try m.reduced(m.formula, &t), m.valued, in: &t)
    let crossing = try ordered(try values(in: b, &t), &t)
    let body = try fixing(
        crossing,
        in: try t.intern(m.forward ? .folImplies(a, b) : .folImplies(b, a)),
        by: .premise,
        in: &t,
    )
    let premised = try t.intern(.folImplies(try classDefinition(m.lambda, K: P, in: &t), body))
    return try universal(m.types, guards: true, premised, in: &t)
}

/// `p`, proving `∀P. ψ`'s value form at a site, at `λ`: the class fixed by its existence, the premise at it, the
/// formula's lemma. `ψ` below the binder, `lambda` at the site.
func instantiatedAtLambda(
    _ p: NodeID,
    _ psi: NodeID,
    _ T: IRType,
    at lambda: NodeID,
    base: Base,
    in t: inout Table,
) throws -> NodeID {
    guard looseIndices(psi, in: t).contains(0) else { return try atClass(p, T, lambda, .proof(0), base, &t) }
    let under = try shift(lambda, by: 1, in: &t)
    let both = try t.intern(.folAnd(psi, try t.intern(.isaConst(
        .primitive(.pure(.eq)),
        .fn(T, .fn(T, .o)),
        args: [under, under],
    ))))
    let named = Mode.proof(0, naming: [0])
    let s = try skeleton(both, { x, d, t in isValued(x, t) && named.deeper(d).valued(x, in: t) }, in: &t)
    let c = try closed(s.formula, in: &t)
    guard
        case .folAnd(let phi, let pair) = t[c.term], case .isaConst(_, _, let args) = t[pair],
        let position = try c.variables.firstIndex(where: { x in
            if case .isaBound(0, _) = t[x] { return true }
            return false
        })
    else { throw MeetingError.unmet(psi) }
    let k = c.types.count - 1 - position
    let lambdaClosed = args[0]
    _ = k
    let request = Instantiation(
        formula: phi,
        lambda: lambdaClosed,
        types: c.types,
        variable: position,
        stated: false,
        forward: true,
        name: "BETA_\(fingerprint(c.term, t))_\(position)",
    )
    var g = Frame()
    let ex = try classExistence(lambda, .proof(0), base, &t)
    let (K, h) = try g.open(ex, in: &t)
    let cls = try g.variable(K, in: &t)
    var replacement = [Int: NodeID]()
    for j in 0..<s.width where j > 0 { replacement[j] = try variable(both, j, minus: 1, &t) }
    for (j, param) in s.params.enumerated() {
        replacement[s.width + j] = try substitute(param, replacement.merging([0: cls]) { a, _ in a }, in: &t)
    }
    let frees = try c.variables.map { x -> NodeID in
        let i: Int
        switch t[x] {
        case .isaBound(let j, _), .isaPropBound(let j): i = j
        default: throw MeetingError.unmet(x)
        }
        if i == 0 { return cls }
        guard let term = replacement[i] else { throw MeetingError.unmet(x) }
        let at = try lifted(term, terms: 1, hyps: 0, in: &t)
        if t.type(of: term) == .o { return try formula(at, .proof(0), in: &t) }
        return try value(of: at, in: &t)
    }
    var functional: NodeID?
    if try guarded(cls, T, in: &t) != nil {
        let function = try functionFact(try lifted(lambda, terms: 1, hyps: 0, in: &t), base, &t)
        let atK = try t.intern(.folForallElim(function, cls))
        functional = try t.intern(.folImpliesElim(atK, try g.hypothesis(h, in: &t)))
    }
    var lemma = try instantiated(
        try cited(request, try statement(request, in: &t), &t),
        at: frees,
        c.types,
        guards: true,
        guardOf: { x, U, t in
            if x == cls, let functional { return functional }
            return try isaGuard(x, U, &t)
        },
        in: &t,
    )
    lemma = try t.intern(.folImpliesElim(lemma, try g.hypothesis(h, in: &t)))
    let b = try formula(try request.reduced(phi, &t), .proof(0), in: &t)
    for v in try ordered(try values(in: b, &t), &t) {
        guard case .isaValue(let term) = t[v] else { throw MeetingError.unmet(v) }
        let site = try valueNode(try lifted(
            try instantiateClosed(term, c.variables, replacement.merging([0: lambda]) { a, _ in a }, &t),
            terms: 1,
            hyps: 0,
            in: &t,
        ), in: &t)
        lemma = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(lemma, site)), try fact(of: site, in: &t)))
    }
    var at = try t.intern(.folForallElim(try lifted(p, terms: 1, hyps: 1, in: &t), cls))
    if let functional { at = try t.intern(.folImpliesElim(at, functional)) }
    at = try t.intern(.folImpliesElim(lemma, at))
    return try g.close(at, in: &t)
}

/// `p`, proving `∀P. ψ` with every term named, at `λ`: the class fixed by its existence, the premise at it, `BETA` at
/// it stated. `ψ` below the binder, `lambda` at the site.
func instantiatedStated(
    _ p: NodeID,
    _ psi: NodeID,
    _ T: IRType,
    at lambda: NodeID,
    base: Base,
    in t: inout Table,
) throws -> NodeID {
    guard looseIndices(psi, in: t).contains(0) else { return try atClass(p, T, lambda, .statement, base, &t) }
    var g = Frame()
    let (K, h) = try g.open(try classExistence(lambda, .statement, base, &t), in: &t)
    let cls = try g.variable(K, in: &t)
    let site = try shift(lambda, by: 1, in: &t)
    let definition = try g.hypothesis(h, in: &t)
    let wrapped = try shift(try t.intern(.isaAbs(T, body: psi)), by: 1, in: &t)
    guard case .isaAbs(_, let below) = t[wrapped] else { throw MeetingError.unmet(psi) }
    var functional: NodeID?
    if try guarded(cls, T, in: &t) != nil {
        let function = try functionFact(site, mode: .statement, base, &t)
        functional = try t.intern(.folImpliesElim(try t.intern(.folForallElim(function, cls)), definition))
    }
    var at = try t.intern(.folForallElim(try lifted(p, terms: 1, hyps: 1, in: &t), cls))
    if let functional { at = try t.intern(.folImpliesElim(at, functional)) }
    let lemma = try betaCited(
        below,
        T,
        at: site,
        cls: cls,
        definition: definition,
        stated: true,
        forward: true,
        guardOf: { x, U, t in
            if x == cls, let functional { return functional }
            return try isaGuard(x, U, &t)
        },
        in: &t,
    )
    return try g.close(try t.intern(.folImpliesElim(lemma, at)), in: &t)
}

/// `p`, proving `∀P. ψ` with `ψ` free of `P`, at the λ's class: `ψ` itself.
private func atClass(_ p: NodeID, _ T: IRType, _ lambda: NodeID, _ mode: Mode, _ base: Base, _ t: inout Table) throws
    -> NodeID
{
    var g = Frame()
    let (K, h) = try g.open(try classExistence(lambda, mode, base, &t), in: &t)
    let cls = try g.variable(K, in: &t)
    var at = try t.intern(.folForallElim(try lifted(p, terms: 1, hyps: 1, in: &t), cls))
    if try guarded(cls, T, in: &t) != nil {
        let function = try functionFact(try shift(lambda, by: 1, in: &t), mode: mode, base, &t)
        let guardProof = try t.intern(.folImpliesElim(
            try t.intern(.folForallElim(function, cls)),
            try g.hypothesis(h, in: &t),
        ))
        at = try t.intern(.folImpliesElim(at, guardProof))
    }
    return try g.close(at, in: &t)
}

/// `∀K. def(λ, K) → function(K)`, `λ` holding its fixed terms' values: FUNC of its skeleton.
func functionFact(
    _ lambda: NodeID,
    mode: Mode = .proof(0),
    _ base: Base,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    _ t: inout Table,
) throws -> NodeID {
    let s = try skeleton(lambda, { x, d, t in isValued(x, t) && mode.deeper(d).valued(x, in: t) }, in: &t)
    let (f, c) = try lambdaFact(s.formula, .function, in: &t)
    let at = try c.variables.map { x -> NodeID in
        guard case .isaBound(let k, _) = t[x], k >= s.width else { return try formula(x, .proof(0), in: &t) }
        return try valueNode(s.params[k - s.width], in: &t)
    }
    return try instantiated(
        try cited(f, try statement(f, base: base, in: &t), &t),
        at: at,
        c.types,
        guards: true,
        guardOf: guardOf,
        in: &t,
    )
}

/// `SUBST ⟨ψ⟩`: Leibniz for a formula in one variable, `x = y → ψ(x) → ψ(y)`, `ψ` naming the terms holding it.
struct Leibniz: Request {
    let formula: NodeID
    let types: [IRType]
    let variable: Int
    let name: String

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Leibniz {
        Leibniz(formula: try f(formula), types: types, variable: variable, name: name)
    }
}

func statement(_ l: Leibniz, in t: inout Table) throws -> NodeID {
    let n = l.types.count
    let k = n - 1 - l.variable
    let T = l.types[l.variable]
    let named = try formula(l.formula, .proof(0, naming: [k]), in: &t)
    let x = try t.intern(.isaBound(k + 1, T))
    let y = try t.intern(.isaBound(0, T))
    let at = try shift(named, by: 1, in: &t)
    let moved = try instantiate(try abstractIndex(at, k + 1, in: &t), with: y, in: &t)
    let body = try t.intern(.folImplies(try equal(T, x, y, in: &t), try t.intern(.folImplies(at, moved))))
    let bound = try t.intern(T == .i || T == .o ? .ifolAll(T, body: body) : .folForall(body: body))
    return try universal(l.types, guards: true, bound, in: &t)
}

/// `x` and `y` equal at `T`: `eq` at `i`, `↔` at `o`, the same members at a class.
private func equal(_ T: IRType, _ x: NodeID, _ y: NodeID, in t: inout Table) throws -> NodeID {
    switch T {
    case .i: return try t.intern(.folPred(.base("eq"), args: [x, y]))
    case .o: return try t.intern(.folIff(x, y))
    case .fn, .variable:
        if isFunctionClass(T) {
            let a = try t.intern(.isaBound(1, .i))
            let r = try t.intern(.isaBound(0, .i))
            let pair = { (c: NodeID, t: inout Table) throws -> NodeID in
                try t.intern(.folPred(.base("pmem"), args: [a, r, try shift(c, by: 2, in: &t)]))
            }
            let same = try t.intern(.folIff(try pair(x, &t), try pair(y, &t)))
            return try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: same))))
        }
        let z = try t.intern(.isaBound(0, .i))
        let member = { (c: NodeID, t: inout Table) throws -> NodeID in
            try t.intern(.folPred(.base("elem"), args: [z, try shift(c, by: 1, in: &t)]))
        }
        return try t.intern(.ifolAll(.i, body: try t.intern(.folIff(try member(x, &t), try member(y, &t)))))
    }
}

extension MeetingProofs {
    func prove(_ l: Leibniz, in t: inout Table) throws -> NodeID {
        var f = Frame()
        for T in l.types {
            let v = f.fix(T)
            if T != .i, T != .o, let g = try guarded(try f.variable(v, in: &t), T, in: &t) { _ = f.assume(g) }
        }
        let n = l.types.count
        let k = n - 1 - l.variable
        let T = l.types[l.variable]
        let named = try formula(l.formula, .proof(0, naming: [k]), in: &t)
        let y = f.fix(T)
        let x = try f.variable(l.variable, in: &t)
        let yv = try f.variable(y, in: &t)
        let e = f.assume(try equal(T, x, yv, in: &t))
        let at = try f.scope.lift(named, from: n, in: &t)
        let h = f.assume(at)
        guard T != .i else {
            let walk = LeibnizWalk(base: base, from: x, to: yv, equal: try f.hypothesis(e, in: &t), scope: f.scope)
            return try f.close(try walk.carried(at, try f.hypothesis(h, in: &t), forward: true, f.scope, &t), in: &t)
        }
        guard case .isaBound(let kx, _) = t[x] else { throw MeetingError.unmet(x) }
        let moved = try instantiate(try abstractIndex(at, kx, in: &t), with: yv, in: &t)
        let depth = f.scope.depth
        let walk = Replacement(base: base) { _, l, r, inner, t in
            let from = try inner.lift(x, from: depth, in: &t)
            let to = try inner.lift(yv, from: depth, in: &t)
            if T == .o {
                guard l == from, r == to else { return nil }
                return try inner.hypothesis(e, in: &t)
            }
            guard
                case .folPred(let p, let ls) = t[l], case .folPred(p, let rs) = t[r], ls.count == rs.count,
                ls.last == from, rs.last == to, ls.dropLast() == rs.dropLast()
            else { return nil }
            let hypothesis = try inner.hypothesis(e, in: &t)
            switch (p, ls.count) {
            case (.base("elem"), 2):
                return try t.intern(.isaAllElim(hypothesis, ls[0]))

            case (.base("pmem"), 3):
                return try t.intern(.isaAllElim(try t.intern(.isaAllElim(hypothesis, ls[0])), ls[1]))

            case (.base("apply"), 3):
                let cong = try base.claimed(.applyClassCong, [from, to], [hypothesis], in: &t)
                return try t.intern(.isaAllElim(try t.intern(.isaAllElim(cong, ls[0])), ls[1]))

            default:
                return nil
            }
        }
        let iff: NodeID
        do { iff = try walk.proof(at, at, moved, in: f.scope, &t) } catch is CongruenceError {
            throw MeetingError.unmet(at)
        }
        return try f.close(try t.intern(.folIffElimL(iff, try f.hypothesis(h, in: &t))), in: &t)
    }
}

/// Carries a formula from `from` to `to` (`forward`) or back, at each atom by membership's congruence.
private struct LeibnizWalk {
    let base: Base
    let from: NodeID
    let to: NodeID
    let equal: NodeID
    let scope: Scope

    func carried(_ phi: NodeID, _ p: NodeID, forward: Bool, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let target = try moved(phi, forward, s, &t)
        if target == phi { return p }
        let other = { (x: NodeID, q: NodeID, s: Scope, t: inout Table) throws -> NodeID in
            try carried(x, q, forward: forward, s, &t)
        }
        let back = { (x: NodeID, q: NodeID, s: Scope, t: inout Table) throws -> NodeID in
            try carried(try moved(x, forward, s, &t), q, forward: !forward, s, &t)
        }
        switch t[phi] {
        case .folPred:
            let (l, r) = try ends(forward, s, &t)
            let iff = try congruent(phi, target, base, { a, b, t in
                guard a == l, b == r else { throw MeetingError.unmet(phi) }
                return try equality(forward, s, &t)
            }, &t)
            return try t.intern(.folIffElimL(iff, p))

        case .folAnd(let a, let b):
            return try t.intern(.folAndIntro(
                try other(a, try t.intern(.folAndElimL(p)), s, &t),
                try other(b, try t.intern(.folAndElimR(p)), s, &t),
            ))

        case .folOr(let a, let b):
            let ta = try moved(a, forward, s, &t)
            let tb = try moved(b, forward, s, &t)
            var ga = Frame(s)
            let ha = ga.assume(a)
            let left = try ga.close(
                try t.intern(.folOrIntroL(try other(a, try ga.hypothesis(ha, in: &t), ga.scope, &t), tb)),
                in: &t,
            )
            var gb = Frame(s)
            let hb = gb.assume(b)
            let right = try gb.close(
                try t.intern(.folOrIntroR(ta, try other(b, try gb.hypothesis(hb, in: &t), gb.scope, &t))),
                in: &t,
            )
            return try t.intern(.folOrElim(p, left, right))

        case .folImplies(let a, let b):
            var g = Frame(s)
            let h = g.assume(try moved(a, forward, s, &t))
            let premise = try back(a, try g.hypothesis(h, in: &t), g.scope, &t)
            let applied = try t.intern(.folImpliesElim(try lifted(p, from: s, to: g.scope, in: &t), premise))
            return try g.close(try other(b, applied, g.scope, &t), in: &t)

        case .folNot(let a):
            let ta = try moved(a, forward, s, &t)
            var g = Frame(s)
            let h = g.assume(ta)
            let premise = try back(a, try g.hypothesis(h, in: &t), g.scope, &t)
            return try t.intern(.folNotIntro(
                ta,
                body: try t.intern(.folNotElim(try lifted(p, from: s, to: g.scope, in: &t), premise)),
            ))

        case .folIff(let a, let b):
            let one = { (l: NodeID, r: NodeID, elim: (NodeID, NodeID) -> Node, t: inout Table) throws -> NodeID in
                var g = Frame(s)
                let h = g.assume(try moved(l, forward, s, &t))
                let premise = try back(l, try g.hypothesis(h, in: &t), g.scope, &t)
                let q = try t.intern(elim(try lifted(p, from: s, to: g.scope, in: &t), premise))
                return try g.close(try other(r, q, g.scope, &t), in: &t)
            }
            return try t.intern(.folIffIntro(
                try one(a, b, { .folIffElimL($0, $1) }, &t),
                try one(b, a, { .folIffElimR($0, $1) }, &t),
            ))

        case .ifolAll(let T, let body) where T != .i && T != .o && isObject(T):
            var g = Frame(s)
            let level = g.fix(T)
            let v = try g.variable(level, in: &t)
            var at = try t.intern(.folForallElim(try lifted(p, from: s, to: g.scope, in: &t), v))
            if let guardFormula = try guarded(v, T, in: &t) {
                at = try t.intern(.folImpliesElim(at, try t.intern(.isaGuard(v, guardFormula))))
            }
            return try t.intern(.isaAllIntro(T, body: try carried(body, at, forward: forward, g.scope, &t)))

        case .ifolAll(.i, let body), .folForall(let body):
            let set = if case .ifolAll = t[phi] { true } else { false }
            var g = Frame(s)
            let x = g.fix(set ? .i : nil)
            let v = try g.variable(x, in: &t)
            let lifted = try lifted(p, from: s, to: g.scope, in: &t)
            let at = try t.intern(set ? .isaAllElim(lifted, v) : .folForallElim(lifted, v))
            let q = try carried(body, at, forward: forward, g.scope, &t)
            return try t.intern(set ? .isaAllIntro(.i, body: q) : .folForallIntro(body: q))

        case .ifolEx(.i, let body), .folExists(let body):
            let set = if case .ifolEx = t[phi] { true } else { false }
            var g = Frame(s)
            let (w, h) = try g.open(p, in: &t)
            let q = try carried(body, try g.hypothesis(h, in: &t), forward: forward, g.scope, &t)
            let shape = try g.scope.lift(target, from: s.depth, in: &t)
            let witness = try g.variable(w, in: &t)
            if set {
                guard case .ifolEx(.i, let b) = t[shape] else { throw MeetingError.unmet(phi) }
                return try g.close(try t.intern(.isaExIntro(q, witness, body: b)), in: &t)
            }
            return try g.close(try t.intern(.folExistsIntro(q, witness)), in: &t)

        default:
            throw MeetingError.unmet(phi)
        }
    }

    private func ends(_ forward: Bool, _ s: Scope, _ t: inout Table) throws -> (NodeID, NodeID) {
        let x = try s.lift(from, from: scope.depth, in: &t)
        let y = try s.lift(to, from: scope.depth, in: &t)
        return forward ? (x, y) : (y, x)
    }

    private func equality(_ forward: Bool, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let e = try lifted(equal, from: scope, to: s, in: &t)
        guard forward else {
            let (x, y) = try ends(true, s, &t)
            return try base.claimed(.eqSymm, [x, y], [e], in: &t)
        }
        return e
    }

    /// `phi` with `from` replaced by `to` (or back), as it stands at `s`.
    private func moved(_ phi: NodeID, _ forward: Bool, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let (x, y) = try ends(forward, s, &t)
        guard case .isaBound(let k, _) = t[x] else { throw MeetingError.unmet(x) }
        return try instantiate(try abstractIndex(phi, k, in: &t), with: y, in: &t)
    }
}

/// `p`, proving `ψ` naming the terms holding its variable 0, at `a` (`ψ` below that binder): the same at `b`, by
/// `q`, `a = b`'s value form, through the formula's Leibniz lemma.
func leibniz(
    _ p: NodeID,
    _ psi: NodeID,
    from a: NodeID,
    to b: NodeID,
    by q: NodeID,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    in t: inout Table,
) throws -> NodeID {
    guard looseIndices(psi, in: t).contains(0) else { return p }
    let named = Mode.proof(0, naming: [0])
    let s = try skeleton(psi, { x, d, t in isValued(x, t) && named.deeper(d).valued(x, in: t) }, in: &t)
    let c = try closed(s.formula, in: &t)
    guard
        let position = c.variables.firstIndex(where: { x in
            switch t[x] {
            case .isaBound(0, _), .isaPropBound(0): true
            default: false
            }
        })
    else { return p }
    let request = Leibniz(
        formula: c.term,
        types: c.types,
        variable: position,
        name: "SUBST_\(fingerprint(c.term, t))_\(position)",
    )
    var replacement = [Int: NodeID]()
    replacement[0] = a
    for k in 1..<max(s.width, 1) { replacement[k] = try variable(psi, k, minus: 1, &t) }
    for (j, param) in s.params.enumerated() { replacement[s.width + j] = try substitute(param, replacement, in: &t) }
    let frees = try c.variables.map { x -> NodeID in
        let k: Int
        switch t[x] {
        case .isaBound(let i, _), .isaPropBound(let i): k = i
        default: throw MeetingError.unmet(x)
        }
        guard let term = replacement[k] else { throw MeetingError.unmet(x) }
        if t.type(of: term) == .o { return try formula(term, .proof(0), in: &t) }
        return try value(of: term, in: &t)
    }
    var lemma = try instantiated(
        try cited(request, try statement(request, in: &t), &t),
        at: frees,
        c.types,
        guards: true,
        guardOf: guardOf,
        in: &t,
    )
    switch c.types[position] {
    case .o: lemma = try t.intern(.folSchemaInst(lemma, try formula(b, .proof(0), in: &t)))
    case .i: lemma = try t.intern(.isaAllElim(lemma, try value(of: b, in: &t)))
    case .fn, .variable: lemma = try t.intern(.folForallElim(lemma, b))
    }
    lemma = try t.intern(.folImpliesElim(lemma, q))
    return try t.intern(.folImpliesElim(lemma, p))
}

/// `BETA`'s citation at a site holding the λ's class `cls` and its definition `definition`: `ψ` (below one binder,
/// the class variable) named at `cls` against `ψ` at the λ — `stated`, every term named on both sides — in the
/// direction `forward`.
func betaCited(
    _ psi: NodeID,
    _ T: IRType,
    at lambda: NodeID,
    cls: NodeID,
    definition: NodeID,
    stated: Bool,
    forward: Bool,
    classes: [Int: NodeID] = [:],
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    in t: inout Table,
) throws -> NodeID {
    let under = try shift(lambda, by: 1, in: &t)
    let both = try t.intern(.folAnd(psi, try t.intern(.isaConst(
        .primitive(.pure(.eq)),
        .fn(T, .fn(T, .o)),
        args: [under, under],
    ))))
    let named: Mode = stated ? .statement : .proof(0, naming: [0])
    let s = try skeleton(both, { x, d, t in isValued(x, t) && named.deeper(d).valued(x, in: t) }, in: &t)
    let c = try closed(s.formula, in: &t)
    guard
        case .folAnd(let phi, let pair) = t[c.term], case .isaConst(_, _, let args) = t[pair],
        let position = c.variables.firstIndex(where: { x in
            if case .isaBound(0, _) = t[x] { return true }
            return false
        })
    else { throw MeetingError.unmet(psi) }
    let request = Instantiation(
        formula: phi,
        lambda: args[0],
        types: c.types,
        variable: position,
        stated: stated,
        forward: forward,
        name: "BETA_\(fingerprint(c.term, t))_\(position)\(stated ? "_S" : "")\(forward ? "" : "_N")",
    )
    var replacement = [Int: NodeID]()
    for j in 1..<max(s.width, 1) { replacement[j] = try classes[j] ?? variable(both, j, minus: 1, &t) }
    for (j, param) in s.params.enumerated() {
        replacement[s.width + j] = try substitute(param, replacement.merging([0: cls]) { a, _ in a }, in: &t)
    }
    let frees = try c.variables.map { x -> NodeID in
        let i: Int
        switch t[x] {
        case .isaBound(let j, _), .isaPropBound(let j): i = j
        default: throw MeetingError.unmet(x)
        }
        if i == 0 { return cls }
        guard let term = replacement[i] else { throw MeetingError.unmet(x) }
        if classes[i] != nil { return term }
        if t.type(of: term) == .o { return try formula(term, stated ? .statement : .proof(0), in: &t) }
        return stated ? term : try value(of: term, in: &t)
    }
    var lemma = try instantiated(
        try cited(request, try statement(request, in: &t), &t),
        at: frees,
        c.types,
        guards: true,
        guardOf: guardOf,
        in: &t,
    )
    lemma = try t.intern(.folImpliesElim(lemma, definition))
    let b = try formula(try request.reduced(phi, &t), request.valued, in: &t)
    for v in try ordered(try values(in: b, &t), &t) {
        guard case .isaValue(let term) = t[v] else { throw MeetingError.unmet(v) }
        let site = try valueNode(
            try instantiateClosed(term, c.variables, replacement.merging([0: lambda]) { a, _ in a }, &t),
            in: &t,
        )
        lemma = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(lemma, site)), try fact(of: site, in: &t)))
    }
    return lemma
}
