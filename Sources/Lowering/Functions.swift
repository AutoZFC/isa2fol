import IR

@frozen
public enum FunctionsError: Error, Equatable, Sendable {
    case notAFunction(NodeID)
    case notMine(NodeID)
    case misproved(NodeID)
    case noReading(NodeID)
}

func overObjects(_ T: IRType) -> Bool {
    guard case .fn(let A, let B) = T, isObject(A) else { return false }
    return B == .i || B == .o || overObjects(B)
}

func overArguments(_ T: IRType) -> Bool {
    guard case .fn(let A, let B) = T, isObject(A) || A == .o else { return false }
    return B == .i || B == .o || overArguments(B)
}

struct Functions {
    let base: Base

    static func isaPointwise(_ U: IRType, _ a: NodeID, _ b: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let T, let V) = U else { return try t.equation(U, a, b) }
        let x = try argument(T, 0, in: &t)
        let fa = try beta(try shift(a, by: 1, in: &t), [x], in: &t)
        let fb = try beta(try shift(b, by: 1, in: &t), [x], in: &t)
        let inner = try isaPointwise(V, fa, fb, in: &t)
        return try t.intern(T == .o ? .isaPropAll(body: inner) : .ifolAll(T, body: inner))
    }

    func reflexive(_ F: IRType, _ f: NodeID, in t: inout Table) throws -> NodeID {
        try underBinders(F, [], (f, f), [f], in: &t) { values, _, t in
            try atValue(.reflexive, result(F), values, [], in: &t)
        }
    }

    func symmetric(_ F: IRType, _ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .isaSymmetric(_, let p0) = t[id] else { throw FunctionsError.notMine(id) }
        let (f, g) = try sides(p0, t)
        let premise = try Self.isaPointwise(F, f, g, in: &t)
        return try underBinders(F, [(p, premise)], (g, f), [f, g], in: &t) { values, hs, t in
            try atValue(.symmetric, result(F), values, hs, in: &t)
        }
    }

    func transitive(_ F: IRType, _ p: NodeID, _ q: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .isaTransitive(_, let p0, let q0) = t[id] else { throw FunctionsError.notMine(id) }
        let (f, g) = try sides(p0, t)
        let (_, h) = try sides(q0, t)
        let premises = [(p, try Self.isaPointwise(F, f, g, in: &t)), (q, try Self.isaPointwise(F, g, h, in: &t))]
        return try underBinders(F, premises, (f, h), [f, g, h], in: &t) { values, hs, t in
            try atValue(.transitive, result(F), values, hs, in: &t)
        }
    }

    func abstract(_ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        try concluding(p, id, in: &t)
    }

    /// `combination` at an object or a proposition argument: the premise at `a` — a proposition by its truth set —
    /// `a`'s terms then moved to `b` by the formula's Leibniz lemma — `f a ≡ g x` named at `x`, carried, valued again.
    func combination(_ F: IRType, _ p: NodeID, _ q: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let A, let U) = F, case .isaCombination(_, let p0, let q0) = t[id] else {
            throw FunctionsError.notMine(id)
        }
        let (f, g) = try sides(p0, t)
        let (a, b) = try sides(q0, t)
        guard A == .i || A == .o else { return try atClasses(A, U, p, q, (f, g), (a, b), was: id, in: &t) }
        let pointwise = try Self.isaPointwise(F, f, g, in: &t)
        let atA: NodeID
        switch t[pointwise] {
        case .ifolAll(.i, let inner):
            atA = try Instances(base: base).instance(p, inner, .i, at: a, in: &t)

        case .isaPropAll(let inner):
            let opened = try Truths(base: base).instance(p, at: try valued(a, in: &t), in: &t)
            atA = try met(opened, inner, moving: .variables([0]), at: [0: a], drop: 1, toValues: true, in: &t)

        default:
            throw FunctionsError.notAFunction(p0)
        }
        let x = try Self.argument(A, 0, in: &t)
        let fa = try beta(try shift(f, by: 1, in: &t), [try shift(a, by: 1, in: &t)], in: &t)
        let gx = try beta(try shift(g, by: 1, in: &t), [x], in: &t)
        let psi = try Self.isaPointwise(U, fa, gx, in: &t)
        let named = try met(atA, psi, moving: .variables([0]), at: [0: a], drop: 1, toValues: false, in: &t)
        let carried = try leibniz(named, psi, from: a, to: b, by: q, in: &t)
        let valued = try met(carried, psi, moving: .variables([0]), at: [0: b], drop: 1, toValues: true, in: &t)
        return try concluding(valued, id, in: &t)
    }

    /// `combination` at `o` under a function whose argument takes a function or a proposition, read whole from its
    /// head, its links never stated: the Replacement walk over the head's body at the two argument lists, each hole an
    /// argument applied, filled by its equation at the hole's variables.
    func chain(_ id: NodeID, lowered: (NodeID, inout Table) throws -> NodeID, in t: inout Table) throws -> NodeID {
        var equations = [NodeID]()
        var link = id
        while case .isaCombination(let G, let p, let q) = t[link], onlyReflexive(G) {
            equations.insert(q, at: 0)
            link = p
        }
        guard case .isaReflexive(let head) = t[link], let H = t.type(of: head) else {
            throw FunctionsError.noReading(id)
        }
        let holes = try H.domains.prefix(equations.count).enumerated()
            .map { k, A in try t.intern(.isaFree("chain.\(k)", A)) }
        let ends = try equations.map { try sides($0, t) }
        let proofs = try equations.map { try lowered($0, &t) }
        let l = try valued(try beta(head, ends.map(\.0), in: &t), in: &t)
        let r = try valued(try beta(head, ends.map(\.1), in: &t), in: &t)
        let walk = Replacement(base: base) { phi, l, r, inner, t in
            guard case .isaVarApp(let h, let xs) = t[phi], let k = holes.firstIndex(of: h) else { return nil }
            var proof = try lifted(proofs[k], from: Scope(), to: inner, in: &t)
            for x in xs {
                guard
                    let v = try variable(x, in: &t), let c = t.conclusion(of: proof),
                    case .ifolAll(let T, _) = t[c]
                else { throw FunctionsError.noReading(id) }
                let e = try t.intern(.folForallElim(proof, v))
                proof = try guarded(v, T, in: &t)
                    .map { try t.intern(.folImpliesElim(e, try t.intern(.isaGuard(v, $0)))) }
                    ?? e
            }
            guard t.conclusion(of: proof) == (try t.intern(.folIff(l, r))) else { throw FunctionsError.misproved(id) }
            return proof
        }
        return try concluding(try walk.proof(try beta(head, holes, in: &t), l, r, in: Scope(), &t), id, in: &t)
    }

    private static func argument(_ T: IRType, _ k: Int, in t: inout Table) throws -> NodeID {
        try t.intern(T == .o ? .isaPropBound(k) : .isaBound(k, T))
    }

    /// The variable an argument read η-long applies: `λz⃗. K z⃗` is `K`.
    private func variable(_ x: NodeID, in t: inout Table) throws -> NodeID? {
        var body = x
        var m = 0
        while case .isaAbs(_, let b) = t[body] { (body, m) = (b, m + 1) }
        if m == 0 { return if case .isaBound = t[x] { x } else { nil } }
        guard
            case .isaVarApp(let h, let args) = t[body], case .isaBound(let j, let T) = t[h], j >= m, args.count == m,
            args.enumerated().allSatisfy({ k, a in if case .isaBound(m - 1 - k, _) = t[a] { true } else { false } })
        else { return nil }
        return try t.intern(.isaBound(j - m, T))
    }

    /// `combination` at a class argument: the premise at `a`, `BETA` back to `a`'s class, the formula `f a ≡ g Q`
    /// carried to `b`'s class by its Leibniz lemma — the classes' members the same by their definitions and `a ≡ b` —
    /// and `BETA` at `b`.
    private func atClasses(
        _ T: IRType,
        _ U: IRType,
        _ p: NodeID,
        _ q: NodeID,
        _ fg: (NodeID, NodeID),
        _ ab: (NodeID, NodeID),
        was id: NodeID,
        in t: inout Table,
    ) throws -> NodeID {
        let (f, g) = fg
        let (a, b) = ab
        let pointwise = try Self.isaPointwise(.fn(T, U), f, g, in: &t)
        guard case .ifolAll(_, let inner) = t[pointwise] else { throw FunctionsError.notAFunction(id) }
        let atA = try instantiatedAtLambda(p, inner, T, at: a, base: base, in: &t)
        let fa = try beta(try shift(f, by: 1, in: &t), [try shift(a, by: 1, in: &t)], in: &t)
        let gQ = try beta(try shift(g, by: 1, in: &t), [try t.intern(.isaBound(0, T))], in: &t)
        var psi = try Self.isaPointwise(U, fa, gQ, in: &t)
        guard looseIndices(psi, in: t).contains(0) else { return try concluding(atA, id, in: &t) }
        var frame = Frame()
        let (ka, ha) = try frame.open(try classExistence(a, .proof(0), base, &t), in: &t)
        let (kb, hb) = try frame.open(
            try classExistence(try lifted(b, terms: 1, hyps: 1, in: &t), .proof(0), base, &t),
            in: &t,
        )
        let Ka = try frame.variable(ka, in: &t)
        let Kb = try frame.variable(kb, in: &t)
        let up = { (x: NodeID, t: inout Table) throws -> NodeID in try lifted(x, terms: 2, hyps: 2, in: &t) }
        var functions = [NodeID: NodeID]()
        if isFunctionClass(T) {
            for (K, lambda, h) in [(Ka, a, ha), (Kb, b, hb)] {
                let fact = try functionFact(try shift(lambda, by: 2, in: &t), base, &t)
                functions[K] = try t.intern(.folImpliesElim(
                    try t.intern(.folForallElim(fact, K)),
                    try frame.hypothesis(h, in: &t),
                ))
            }
        }
        let guardOf = { (x: NodeID, U: IRType, t: inout Table) throws -> NodeID in
            try functions[x] ?? isaGuard(x, U, &t)
        }
        let wrapped = try shift(try t.intern(.isaAbs(T, body: psi)), by: 2, in: &t)
        guard case .isaAbs(_, let below) = t[wrapped] else { throw FunctionsError.notAFunction(id) }
        psi = below
        let back = try betaCited(
            psi,
            T,
            at: try shift(a, by: 2, in: &t),
            cls: Ka,
            definition: try frame.hypothesis(ha, in: &t),
            stated: false,
            forward: false,
            guardOf: guardOf,
            in: &t,
        )
        let atKa = try t.intern(.folImpliesElim(back, try up(atA, &t)))
        let same = try members(
            T,
            (try shift(a, by: 2, in: &t), try shift(b, by: 2, in: &t)),
            ha,
            hb,
            try up(q, &t),
            frame,
            in: &t,
        )
        let atKb = try leibniz(atKa, psi, from: Ka, to: Kb, by: same, guardOf: guardOf, in: &t)
        let forward = try betaCited(
            psi,
            T,
            at: try shift(b, by: 2, in: &t),
            cls: Kb,
            definition: try frame.hypothesis(hb, in: &t),
            stated: false,
            forward: true,
            guardOf: guardOf,
            in: &t,
        )
        return try concluding(try frame.close(try t.intern(.folImpliesElim(forward, atKb)), in: &t), id, in: &t)
    }

    /// The classes of two λs with the same members — `∀z. z ∈ Ka ↔ z ∈ Kb`, at a function `∀τ r. pmem(τ, r, Ka) ↔ …` —
    /// by `q`, the λs equal pointwise: each class's definition there, the λs' bodies by `q` at the definition's own
    /// variables; at a function through the bodies' values.
    private func members(
        _ T: IRType,
        _ lambdas: (NodeID, NodeID),
        _ ha: Int,
        _ hb: Int,
        _ q: NodeID,
        _ frame: Frame,
        in t: inout Table,
    ) throws -> NodeID {
        let n = T.domains.count
        let outside = isFunctionClass(T) ? 2 : 1
        var g = Frame(frame.scope)
        let levels = (0..<outside).map { _ in g.fix(.i) }
        var atA = try g.hypothesis(ha, in: &t)
        var atB = try g.hypothesis(hb, in: &t)
        for level in levels {
            let v = try g.variable(level, in: &t)
            atA = try t.intern(.isaAllElim(atA, v))
            atB = try t.intern(.isaAllElim(atB, v))
        }
        guard
            case .folIff(let inA, let da)? = t.conclusion(of: atA).map({ t[$0] }),
            case .folIff(let inB, let db)? = t.conclusion(of: atB).map({ t[$0] })
        else { throw FunctionsError.notAFunction(lambdas.0) }
        let pointwise = try lifted(q, from: frame.scope, to: g.scope, in: &t)
        let depth = g.scope.depth
        let bodies = try Replacement(base: base) { _, l, r, inner, t in
            guard inner.depth >= depth + n else { return nil }
            var at = try lifted(pointwise, from: g.scope, to: inner, in: &t)
            let xs = try (0..<n).map { try inner.variable(inner.depth - n + $0, in: &t) }
            for x in xs { at = try t.intern(.isaAllElim(at, x)) }
            guard outside == 2 else {
                guard t.conclusion(of: at) == (try t.intern(.folIff(l, r))) else { return nil }
                return at
            }
            let value = try inner.variable(levels[1], in: &t)
            let terms = try [lambdas.0, lambdas.1].map { lambda in
                try beta(try lifted(lambda, from: frame.scope, to: inner, in: &t), xs, in: &t)
            }
            return try values(l, r, value, terms, at, n, inner, in: &t)
        }.proof(da, da, db, in: g.scope, &t)
        let toB = try base.applied(.iffTrans, [inA, da, db], [atA, bodies], in: &t)
        let both = try base.applied(
            .iffTrans,
            [inA, db, inB],
            [toB, try base.applied(.iffSymm, [inB, db], [atB], in: &t)],
            in: &t,
        )
        return try g.close(both, in: &t)
    }

    /// `⟦r = a⟧ ↔ ⟦r = b⟧`, `a` and `b` named at the innermost `n` variables, from `same`, `⟦a = b⟧`: each through the
    /// terms' values, the values bound here.
    private func values(
        _ l: NodeID,
        _ r: NodeID,
        _ rv: NodeID,
        _ terms: [NodeID],
        _ same: NodeID,
        _ n: Int,
        _ s: Scope,
        in t: inout Table,
    ) throws -> NodeID? {
        let moving = Moving.variables(Array(0..<n))
        let ra = try equation(rv, terms[0], in: &t)
        let rb = try equation(rv, terms[1], in: &t)
        let ab = try equation(terms[0], terms[1], in: &t)
        guard
            l == (try formula(ra, .proof(0, naming: Set(0..<n)), in: &t)),
            r == (try formula(rb, .proof(0, naming: Set(0..<n)), in: &t))
        else { return nil }
        let one = { (from: NodeID, fromTerm: Int, to: NodeID, t: inout Table) throws -> NodeID in
            var f = Frame(s)
            let h = f.assume(from == ra ? l : r)
            let held = try met(try f.hypothesis(h, in: &t), from, moving: moving, toValues: true, in: &t)
            var equal = try met(
                try lifted(same, from: s, to: f.scope, in: &t),
                ab,
                moving: moving,
                toValues: true,
                in: &t,
            )
            let va = try value(of: terms[0], in: &t)
            let vb = try value(of: terms[1], in: &t)
            if fromTerm == 1 { equal = try base.claimed(.eqSymm, [va, vb], [equal], in: &t) }
            let ends = fromTerm == 0 ? [rv, va, vb] : [rv, vb, va]
            let moved = try base.claimed(.eqTrans, ends, [held, equal], in: &t)
            let named = try met(moved, to, moving: moving, toValues: false, in: &t)
            let bound = try fixing(
                try scoped(named, closed: false, below: n, in: &t),
                in: named,
                by: .existence(base),
                in: &t,
            )
            return try f.close(bound, in: &t)
        }
        return try t.intern(.folIffIntro(try one(ra, 0, rb, &t), try one(rb, 1, ra, &t)))
    }

    private func concluding(_ proof: NodeID, _ id: NodeID, in t: inout Table) throws -> NodeID {
        let wanted = try valued(try conclusion(id, t), in: &t)
        guard t.conclusion(of: proof) == wanted else { throw FunctionsError.misproved(id) }
        return proof
    }

    /// Below one fresh variable per argument — a truth set at a proposition, its `truth` assumed — each premise at
    /// them, `body` at the functions applied, each binder concluded again, every crossing through its formula's lemma.
    private func underBinders(
        _ F: IRType,
        _ premises: [(proof: NodeID, stated: NodeID)],
        _ concluded: (NodeID, NodeID),
        _ functions: [NodeID],
        in t: inout Table,
        _ body: ([NodeID], [NodeID], inout Table) throws -> NodeID,
    ) throws -> NodeID {
        let domains = F.domains
        let n = domains.count
        let instances = Instances(base: base)
        let truths = domains.count(where: { $0 == .o })
        let arguments = try (0..<n).map { j in try Self.argument(domains[j], n - 1 - j, in: &t) }
        var truthHyps = [Int: NodeID]()
        var seen = 0
        for j in 0..<n where domains[j] == .o {
            seen += 1
            truthHyps[j] = try t.intern(.hyp(truths - seen, try truth(try t.intern(.folBound(n - 1 - j)), in: &t)))
        }
        var held = [NodeID]()
        for (p, P) in premises {
            var at = try lifted(p, terms: n, hyps: truths, in: &t)
            var stated = try shift(P, by: n, in: &t)
            for j in 0..<n {
                switch t[stated] {
                case .ifolAll(.i, let inner):
                    at = try instances.instance(at, inner, .i, at: arguments[j], in: &t)
                    stated = try instantiate(inner, with: arguments[j], in: &t)

                case .ifolAll(let T, let inner):
                    var opened = try t.intern(.folForallElim(at, arguments[j]))
                    if let g = try guarded(arguments[j], T, in: &t) {
                        opened = try t.intern(.folImpliesElim(opened, try t.intern(.isaGuard(arguments[j], g))))
                    }
                    at = try met(
                        opened,
                        inner,
                        moving: .variables([0]),
                        at: [0: arguments[j]],
                        drop: 1,
                        toValues: true,
                        in: &t,
                    )
                    stated = try instantiate(inner, with: arguments[j], in: &t)

                case .isaPropAll(let inner):
                    guard let h = truthHyps[j] else { throw FunctionsError.notAFunction(p) }
                    let E = try t.intern(.folBound(n - 1 - j))
                    let opened = try t.intern(.folImpliesElim(try t.intern(.folForallElim(at, E)), h))
                    at = try met(
                        opened,
                        inner,
                        moving: .variables([0]),
                        at: [0: arguments[j]],
                        drop: 1,
                        toValues: true,
                        in: &t,
                    )
                    stated = try instantiate(inner, with: arguments[j], in: &t)

                default:
                    throw FunctionsError.notAFunction(p)
                }
            }
            held.append(at)
        }
        let applied = try functions.map { try beta(try shift($0, by: n, in: &t), arguments, in: &t) }
        var proof = try body(applied, held, &t)
        for j in (0..<n).reversed() {
            let f = try shift(concluded.0, by: j + 1, in: &t)
            let g = try shift(concluded.1, by: j + 1, in: &t)
            let bound = try (0...j).map { try Self.argument(domains[$0], j - $0, in: &t) }
            var V = F
            for _ in 0...j {
                guard case .fn(_, let W) = V else { throw FunctionsError.notAFunction(f) }
                V = W
            }
            let psi = try Self.isaPointwise(V, try beta(f, bound, in: &t), try beta(g, bound, in: &t), in: &t)
            if domains[j] == .o {
                let named = try met(proof, psi, moving: .variables([0]), toValues: false, in: &t)
                let fixed = try fixing(
                    try scoped(named, closed: false, in: &t),
                    in: named,
                    by: .existence(base),
                    in: &t,
                )
                let premise = try truth(try t.intern(.folBound(0)), in: &t)
                proof = try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(premise, body: fixed))))
            } else {
                proof = try instances.generalized(proof, psi, domains[j], in: &t)
            }
        }
        return proof
    }

    private func atValue(
        _ e: Equality,
        _ V: IRType,
        _ sides: [NodeID],
        _ premises: [NodeID],
        in t: inout Table,
    ) throws -> NodeID {
        if V == .i { return try Equalities(base: base).atI(e, sides, premises, in: &t) }
        let named = try premises.map { p -> (NodeID, NodeID) in
            guard case .folIff(let l, let r)? = t.conclusion(of: p).map({ t[$0] }) else {
                throw FunctionsError.notAFunction(p)
            }
            return (l, r)
        }
        switch e {
        case .reflexive: return try base.instance(.iffRefl, [try valued(sides[0], in: &t)], in: &t)
        case .symmetric: return try base.applied(.iffSymm, [named[0].0, named[0].1], premises, in: &t)
        case .transitive: return try base.applied(.iffTrans, [named[0].0, named[0].1, named[1].1], premises, in: &t)
        }
    }

    private func sides(_ p: NodeID, _ t: Table) throws -> (NodeID, NodeID) {
        guard let c = t.conclusion(of: p), let (_, a, b) = t.sides(ofEquation: c) else {
            throw FunctionsError.notAFunction(p)
        }
        return (a, b)
    }

    private func conclusion(_ p: NodeID, _ t: Table) throws -> NodeID {
        guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        return c
    }
}
