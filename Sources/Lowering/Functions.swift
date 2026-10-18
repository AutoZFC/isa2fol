import IR

@frozen
public enum FunctionsError: Error, Equatable, Sendable {
    case notAFunction(NodeID)
    case notMine(NodeID)
    case misproved(NodeID)
}

func overObjects(_ T: IRType) -> Bool {
    guard case .fn(let A, let B) = T, isObject(A) else { return false }
    return B == .i || B == .o || overObjects(B)
}

struct Functions {
    let base: Base

    func pointwise(_ F: IRType, _ f: NodeID, _ g: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let T, let U) = F, case .isaAbs(T, let a) = t[f], case .isaAbs(T, let b) = t[g] else {
            throw FunctionsError.notAFunction(f)
        }
        let body: NodeID =
            switch U {
            case .fn: try pointwise(U, a, b, in: &t)
            case .o: try t.intern(.folIff(a, b))
            case .i: try walked(try t.equation(.i, a, b), base: base, in: &t)
            case .variable: throw FunctionsError.notAFunction(f)
            }
        return try t.intern(.ifolAll(T, body: body))
    }

    func reflexive(_ F: IRType, _ f: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let T, let U) = F, case .isaAbs(T, let body) = t[f] else { throw FunctionsError.notAFunction(f) }
        let inner: NodeID =
            switch U {
            case .fn: try reflexive(U, body, in: &t)
            case .o: try base.instance(.iffRefl, [try walked(body, base: base, in: &t)], in: &t)
            case .i: try Equalities(base: base).atI(.reflexive, [body], [], in: &t)
            case .variable: throw FunctionsError.notAFunction(f)
            }
        return try t.intern(.isaAllIntro(T, body: inner))
    }

    func symmetric(_ F: IRType, _ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .isaSymmetric(_, let p0) = t[id] else { throw FunctionsError.notMine(id) }
        let (f, g) = try sides(p0, t)
        return try underBinders(F, [p], in: &t) { s, hs, xs, t in
            let fg = try eliminated(hs[0], xs, F, in: &t)
            return try atValue(.symmetric, result(F), try applied([f, g], xs, s, &t), [fg], in: &t)
        }
    }

    func transitive(_ F: IRType, _ p: NodeID, _ q: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .isaTransitive(_, let p0, let q0) = t[id] else { throw FunctionsError.notMine(id) }
        let (f, g) = try sides(p0, t)
        let (_, h) = try sides(q0, t)
        return try underBinders(F, [p, q], in: &t) { s, hs, xs, t in
            let fg = try eliminated(hs[0], xs, F, in: &t)
            let gh = try eliminated(hs[1], xs, F, in: &t)
            return try atValue(.transitive, result(F), try applied([f, g, h], xs, s, &t), [fg, gh], in: &t)
        }
    }

    func abstract(_ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        try concluding(p, id, in: &t)
    }

    func combination(_ F: IRType, _ p: NodeID, _ q: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let T, let U) = F, case .isaCombination(_, let p0, let q0) = t[id] else {
            throw FunctionsError.notMine(id)
        }
        let (f, g) = try sides(p0, t)
        let (a, b) = try sides(q0, t)
        let context = { (x: NodeID, y: NodeID, d: Int, t: inout Table) throws -> NodeID in
            try isaPointwise(
                U,
                try beta(try shift(f, by: d, in: &t), [x], in: &t),
                try beta(try shift(g, by: d, in: &t), [y], in: &t),
                in: &t,
            )
        }
        let x = try t.intern(.isaBound(0, T))
        let diagonal = try t.intern(.ifolAll(T, body: try context(x, x, 1, &t)))
        let atA = try instance(p, of: diagonal, at: a, T, in: &t)
        let substituted =
            if T == .i {
                try atSet({ y, d, t in try context(try shift(a, by: d, in: &t), y, d, &t) }, a, b, q, in: &t)
            } else {
                try atClass(T, { y, d, t in try context(try shift(a, by: d, in: &t), y, d, &t) }, a, b, q, in: &t)
            }
        return try concluding(try t.intern(.folIffElimL(substituted, atA)), id, in: &t)
    }

    func atSet(
        _ context: (NodeID, Int, inout Table) throws -> NodeID,
        _ a: NodeID,
        _ b: NodeID,
        _ equation: NodeID,
        in t: inout Table,
    ) throws -> NodeID {
        var s = Scope()
        let v = s.fix(.i)
        let w = s.fix(.i)
        let x = try s.variable(v, in: &t)
        let y = try s.variable(w, in: &t)
        let equal = try t.equation(.i, x, y)
        let named = try walked(equal, base: base, in: &t)
        let h = s.assume(named)
        let left = try context(x, 2, &t)
        let right = try context(y, 2, &t)
        let l = try walked(left, base: base, in: &t)
        let r = try walked(right, base: base, in: &t)
        let walk = try Replacement(base: base) { phi, l, r, s, t in
            guard case .folPred = t[phi] else { return nil }
            let e = try s.hypothesis(h, in: &t)
            return try congruent(l, r, base, { _, _, _ in e }, &t)
        }.proof(l, l, r, in: s, &t)
        let proved = try t.intern(.isaAllIntro(.i, body: try t.intern(.isaAllIntro(.i, body: try t.intern(
            .folImpliesIntro(named, body: walk)
        )))))
        let stated = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(
            equal,
            try t.intern(.folIff(left, right)),
        ))))))
        let atA = try t.intern(.isaAllElim(try t.intern(.hyp(0, stated)), a))
        let first = try Reify().instance(proved, was: atA, base: base, in: &t)
        let second = try Reify().instance(first, was: try t.intern(.isaAllElim(atA, b)), base: base, in: &t)
        return try t.intern(.folImpliesElim(second, equation))
    }

    func isaPointwise(_ U: IRType, _ a: NodeID, _ b: NodeID, in t: inout Table) throws -> NodeID {
        guard case .fn(let T, let V) = U else { return try t.equation(U, a, b) }
        let x = try t.intern(.isaBound(0, T))
        let fa = try beta(try shift(a, by: 1, in: &t), [x], in: &t)
        let fb = try beta(try shift(b, by: 1, in: &t), [x], in: &t)
        return try t.intern(.ifolAll(T, body: try isaPointwise(V, fa, fb, in: &t)))
    }

    func instance(
        _ p: NodeID,
        of statement: NodeID,
        at a: NodeID,
        _ T: IRType,
        in t: inout Table,
    ) throws -> NodeID {
        let elim = try t.intern(.isaAllElim(try t.intern(.hyp(0, statement)), a))
        if T == .i { return try Reify().instance(p, was: elim, base: base, in: &t) }
        return try LambdaInstance(base: base).proof(p, was: elim, in: &t)
    }

    private func atClass(
        _ T: IRType,
        _ context: (NodeID, Int, inout Table) throws -> NodeID,
        _ a: NodeID,
        _ b: NodeID,
        _ q: NodeID,
        in t: inout Table,
    ) throws -> NodeID {
        let stated = try conclusion(q, t)
        var s = Scope()
        let h = s.assume(stated)
        let y = s.fix(T)
        let z = s.fix(T)
        let template = try context(try s.variable(y, in: &t), 2, &t)
        let l = try s.lift(try walked(try context(a, 0, &t), base: base, in: &t), in: &t)
        let r = try s.lift(try walked(try context(b, 0, &t), base: base, in: &t), in: &t)
        let hole = Substitution(
            functions: self,
            type: T,
            variable: y,
            carried: z,
            source: try s.lift(a, in: &t),
            target: try s.lift(b, in: &t),
            depth: s.depth,
            assumption: h,
            statement: try s.lift(try isaPointwise(T, a, b, in: &t), in: &t),
        )
        let walk = try Replacement(base: base, hole: hole.atom).proof(template, l, r, in: s, &t)
        let lowered = try unshift(try unshift(walk, in: &t), in: &t)
        return try t.intern(.folImpliesElim(try t.intern(.folImpliesIntro(stated, body: lowered)), q))
    }

    private func concluding(_ proof: NodeID, _ id: NodeID, in t: inout Table) throws -> NodeID {
        let wanted = try walked(try conclusion(id, t), base: base, in: &t)
        guard t.conclusion(of: proof) == wanted else { throw FunctionsError.misproved(id) }
        return proof
    }

    private func underBinders(
        _ F: IRType,
        _ premises: [NodeID],
        in t: inout Table,
        _ body: (Scope, [NodeID], [NodeID], inout Table) throws -> NodeID,
    ) throws -> NodeID {
        var s = Scope()
        let stated = try premises.map { try conclusion($0, t) }
        let levels = stated.map { s.assume($0) }
        let fixed = F.domains.map { s.fix($0) }
        let hs = try levels.map { try s.hypothesis($0, in: &t) }
        let xs = try fixed.map { try s.variable($0, in: &t) }
        var proof = try body(s, hs, xs, &t)
        for T in F.domains.reversed() { proof = try t.intern(.isaAllIntro(T, body: proof)) }
        for c in stated.reversed() { proof = try t.intern(.folImpliesIntro(c, body: proof)) }
        for p in premises { proof = try t.intern(.folImpliesElim(proof, p)) }
        return proof
    }

    private func eliminated(_ p: NodeID, _ xs: [NodeID], _ F: IRType, in t: inout Table) throws -> NodeID {
        var step = p
        for (x, T) in zip(xs, F.domains) {
            step = try t.intern(.folForallElim(step, x))
            if let g = try guarded(x, T, in: &t) {
                step = try t.intern(.folImpliesElim(step, try t.intern(.isaGuard(x, g))))
            }
        }
        return step
    }

    private func applied(_ fs: [NodeID], _ xs: [NodeID], _ s: Scope, _ t: inout Table) throws -> [NodeID] {
        try fs.map { try beta(try s.lift($0, in: &t), xs, in: &t) }
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
        case .reflexive: throw FunctionsError.notAFunction(premises[0])
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

private struct Substitution {
    let functions: Functions
    let type: IRType
    let variable: Int
    let carried: Int
    let source: NodeID
    let target: NodeID
    let depth: Int
    let assumption: Int
    let statement: NodeID

    func atom(_ phi: NodeID, _: NodeID, _: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID? {
        guard Reify().names(Pattern(t[phi], in: t)) else { return nil }
        let x = s.depth - 1 - variable
        let z = try t.intern(.isaBound(s.depth - 1 - carried, type))
        var form = phi
        var current = try placed(form, s, &t)
        var joined: NodeID?
        for u in units(phi, x, [], in: t) {
            let unit = try argument(at: u.path, in: form, t)
            let renamed: NodeID
            switch u.kind {
            case .applied:
                guard case .isaVarApp(_, let args) = t[unit] else { throw FunctionsError.notAFunction(unit) }
                renamed = try t.intern(.isaVarApp(head: z, args: args))

            case .lambda:
                renamed = try instantiate(try abstractIndex(unit, x, in: &t), with: z, in: &t)

            case .term:
                throw FunctionsError.notAFunction(phi)
            }
            let carriedForm = try replacing(form, at: u.path[...], with: renamed, in: &t)
            let next = try placed(carriedForm, s, &t)
            let step: NodeID =
                switch u.kind {
                case .applied: try applied(current, unit, u.path, s, &t)

                case .lambda: try slotConverted(
                        current,
                        next,
                        u.path,
                        base: functions.base,
                        in: s,
                        &t,
                        hole: atom,
                        template: form,
                    )

                case .term: throw FunctionsError.notAFunction(phi)
                }
            joined = try joined.map { try chained($0, step, functions.base, &t) } ?? step
            (form, current) = (carriedForm, next)
        }
        return joined
    }

    private func placed(_ form: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let a = try s.lift(source, from: depth, in: &t)
        let b = try s.lift(target, from: depth, in: &t)
        let atA = try instantiate(try abstractIndex(form, s.depth - 1 - variable, in: &t), with: a, in: &t)
        return try instantiate(try abstractIndex(atA, s.depth - 1 - carried, in: &t), with: b, in: &t)
    }

    private func applied(
        _ current: NodeID,
        _ unit: NodeID,
        _ path: [Int],
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let assumed = try s.hypothesis(assumption, in: &t)
        guard
            case .isaVarApp(_, let args) = t[unit],
            case .hyp(let index, _) = t[assumed]
        else { throw FunctionsError.notAFunction(unit) }
        var q = try t.intern(.hyp(index, try s.lift(statement, from: depth, in: &t)))
        for arg in args { q = try t.intern(.isaAllElim(q, try placed(arg, s, &t))) }
        let equal = try walked(q, base: functions.base, in: &t)
        if path.isEmpty { return equal }
        guard let c = t.conclusion(of: q), let (_, l, r) = t.sides(ofEquation: c) else {
            throw FunctionsError.notAFunction(unit)
        }
        return try functions.atSet({ y, d, t in
            try replacing(try shift(current, by: d, in: &t), at: path[...], with: y, in: &t)
        }, l, r, equal, in: &t)
    }
}
