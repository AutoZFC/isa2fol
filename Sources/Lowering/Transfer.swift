import IR

@frozen
public enum TransferError: Error, Equatable, Sendable {
    case notItsConstraint(NodeID)
    case notAnAtom(NodeID)
    case notMonotone(NodeID)
}

struct OpenedTerm {
    let term: NodeID
    let depth: Int
    let pieces: [Int]
    let binders: [Binder]
    let constraints: [Fact]
    let value: Int
}

func openedTerm(_ term: NodeID, at depth: Int, _ o: Opened, in t: inout Table) throws -> OpenedTerm {
    var naming = Naming(occurrences: [[]])
    _ = try naming.name(term, [], &t)
    guard case .bound(let k)? = naming.sites[[]]?.value, o.witnesses.count == naming.chain.binders.count else {
        throw TransferError.notAnAtom(term)
    }
    return OpenedTerm(
        term: term,
        depth: depth,
        pieces: o.witnesses,
        binders: naming.chain.binders,
        constraints: o.constraints,
        value: o.witnesses[k],
    )
}

struct EquationSide {
    let term: NodeID
    let opened: OpenedTerm?

    func value(_ s: Scope, _ t: inout Table) throws -> NodeID {
        guard let o = opened else { return try s.lift(term, in: &t) }
        return try s.variable(o.value, in: &t)
    }
}

func openedExistence(_ a: NodeID, base: Base, in f: inout Frame, _ t: inout Table) throws -> OpenedTerm {
    let c = try closed(a, in: &t)
    let r = try existence(of: a, in: &t)
    let ex = try t.intern(.use(.lemma(Lemma(r)), [], try statement(r, in: &t)))
    let exists = try instantiated(
        ex,
        at: try c.variables.map { try walked(try f.scope.lift($0, in: &t), base: base, in: &t) },
        c.types,
        guards: false,
        guardOf: isaGuard,
        in: &t,
    )
    let (y, h) = try f.open(exists, in: &t)
    let equated = try equation(try f.variable(y, in: &t), try f.scope.lift(a, in: &t), in: &t)
    var naming = Naming()
    _ = try naming.atom(t[equated], in: &t)
    let o = try f.open(chain: .hypothesis(h), naming.chain.binders, in: &t)
    return try openedTerm(a, at: 0, o, in: &t)
}

func openedEquation(
    _ a: NodeID,
    _ b: NodeID,
    _ h: Int,
    in f: inout Frame,
    _ t: inout Table,
) throws -> (left: EquationSide, right: EquationSide, core: Fact) {
    let equated = try equation(try f.scope.lift(a, in: &t), try f.scope.lift(b, in: &t), in: &t)
    var naming = Naming(occurrences: [[0], [1]])
    _ = try naming.atom(t[equated], in: &t)
    let o = try f.open(chain: .hypothesis(h), naming.chain.binders, in: &t)
    let side = { (term: NodeID, path: [Int]) throws -> EquationSide in
        guard let site = naming.sites[path] else { throw TransferError.notAnAtom(equated) }
        guard case .bound(let v) = site.value else { return EquationSide(term: term, opened: nil) }
        return EquationSide(term: term, opened: OpenedTerm(
            term: term,
            depth: 0,
            pieces: site.binders.map { o.witnesses[$0] },
            binders: site.binders.map { naming.chain.binders[$0] },
            constraints: site.binders.map { o.constraints[$0] },
            value: o.witnesses[v],
        ))
    }
    return (try side(a, [0]), try side(b, [1]), o.core)
}

func closedEquation(
    _ left: EquationSide,
    _ right: EquationSide,
    _ core: NodeID,
    in f: Frame,
    _ t: inout Table,
) throws -> NodeID {
    let equated = try equation(left.term, right.term, in: &t)
    let formula = try f.scope.lift(try named(atom: t[equated], in: &t), in: &t)
    var witnesses = [NodeID]()
    var facts = [NodeID]()
    for side in [left, right] {
        guard let o = side.opened else { continue }
        witnesses += try o.pieces.map { try f.variable($0, in: &t) }
        facts += try o.constraints.map { try f.proof($0, in: &t) }
    }
    return try closing(formula, witnesses, facts, core, in: &t)
}

func uniquenessApplied(
    _ first: OpenedTerm,
    _ second: OpenedTerm,
    base: Base,
    in s: Scope,
    _ t: inout Table,
) throws -> NodeID {
    let c = try closed(first.term, in: &t)
    let r = try uniqueness(of: first.term, in: &t)
    var p = try instantiated(
        try t.intern(.use(.lemma(Lemma(r)), [], try statement(r, in: &t))),
        at: try c.variables.map { try walked(try s.lift($0, from: first.depth, in: &t), base: base, in: &t) },
        c.types,
        guards: true,
        guardOf: isaGuard,
        in: &t,
    )
    for o in [first, second] {
        for (j, w) in o.pieces.enumerated() {
            let v = try s.variable(w, in: &t)
            p = try t.intern(first.binders[j] == .set ? .isaAllElim(p, v) : .folForallElim(p, v))
            p = try t.intern(.folImpliesElim(p, try s.proof(o.constraints[j], in: &t)))
        }
    }
    return p
}

struct Transfer {
    let base: Base
    let terms: [OpenedTerm]

    func implication(
        _ phi: NodeID,
        from l: NodeID,
        to r: NodeID,
        forward: Bool,
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        if l == r { return try t.intern(.folImpliesIntro(l, body: try t.intern(.hyp(0, l)))) }
        if let p = try atom(phi, from: l, to: r, forward: forward, in: s, &t) { return p }
        if
            case .isaConst(.primitive(.pure(.eq)), .fn(let F, _), let args) = t[phi], args.count == 2,
            overArguments(F)
        {
            let pointwise = try Functions.isaPointwise(F, args[0], args[1], in: &t)
            return try implication(pointwise, from: l, to: r, forward: forward, in: s, &t)
        }
        switch t[phi] {
        case .folNot(let a):
            guard case .folNot(let la) = t[l], case .folNot(let ra) = t[r] else { throw TransferError.notMonotone(phi) }
            let inner = try implication(a, from: ra, to: la, forward: !forward, in: s, &t)
            return try base.applied(.monoNot, [la, ra], [inner], in: &t)

        case .folAnd(let a, let b), .folOr(let a, let b):
            let schema: BaseStatement = if case .folAnd = t[phi] { .monoAnd } else { .monoOr }
            guard let (la, lb) = binary(t[l]), let (ra, rb) = binary(t[r]) else {
                throw TransferError.notMonotone(phi)
            }
            let left = try implication(a, from: la, to: ra, forward: forward, in: s, &t)
            let right = try implication(b, from: lb, to: rb, forward: forward, in: s, &t)
            return try base.applied(schema, [la, ra, lb, rb], [left, right], in: &t)

        case .folImplies(let a, let b):
            guard case .folImplies(let la, let lb) = t[l], case .folImplies(let ra, let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            let left = try implication(a, from: ra, to: la, forward: !forward, in: s, &t)
            let right = try implication(b, from: lb, to: rb, forward: forward, in: s, &t)
            return try base.applied(.monoImp, [la, ra, lb, rb], [left, right], in: &t)

        case .folIff:
            let equivalent = try equivalence(phi, forward ? l : r, forward ? r : l, in: s, &t)
            return try directed(equivalent, from: l, forward: forward, in: s, &t)

        case .ifolEx(.i, let body):
            guard case .ifolEx(.i, let lb) = t[l], case .ifolEx(.i, let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            return try quantified(.monoExists, .i, body, lb, rb, forward, s, &t)

        case .ifolAll(.i, let body):
            guard case .ifolAll(.i, let lb) = t[l], case .ifolAll(.i, let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            return try quantified(.monoForall, .i, body, lb, rb, forward, s, &t)

        case .folExists(let body):
            guard case .folExists(let lb) = t[l], case .folExists(let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            return try quantified(.monoExistsBare, nil, body, lb, rb, forward, s, &t)

        case .folForall(let body):
            guard case .folForall(let lb) = t[l], case .folForall(let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            return try quantified(.monoForallBare, nil, body, lb, rb, forward, s, &t)

        case .isaPropAll(let body):
            guard case .folForall(let lb) = t[l], case .folForall(let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            let guarded = try t.intern(.folImplies(try truth(try t.intern(.folBound(0)), in: &t), body))
            return try quantified(.monoForallBare, nil, guarded, lb, rb, forward, s, &t)

        case .ifolAll(let T, let body):
            guard isObject(T), case .ifolAll(T, let lb) = t[l], case .ifolAll(T, let rb) = t[r] else {
                throw TransferError.notMonotone(phi)
            }
            var inner = s
            _ = inner.assume(l)
            _ = inner.fix(T)
            let p = try implication(body, from: lb, to: rb, forward: forward, in: inner, &t)
            let x = try t.intern(.isaBound(0, T))
            var at = try t.intern(.folForallElim(try t.intern(.hyp(0, try shift(l, by: 1, in: &t))), x))
            if let g = try guarded(x, T, in: &t) {
                at = try t.intern(.folImpliesElim(at, try t.intern(.isaGuard(x, g))))
            }
            return try t.intern(.folImpliesIntro(
                l,
                body: try t.intern(.isaAllIntro(T, body: try t.intern(.folImpliesElim(p, at)))),
            ))

        case .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
             .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropIntro, .isaPropBound, .isaHidden, .folBottom,
             .folImpliesIntro, .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro,
             .isaExElim, .folBound, .folPred, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
             .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
             .folLetterAbs:
            throw TransferError.notMonotone(phi)
        }
    }

    func equivalence(_ phi: NodeID, _ value: NodeID, _ term: NodeID, in s: Scope, _ t: inout Table) throws -> NodeID {
        try Replacement(base: base, hole: equivalentAtom).proof(phi, value, term, in: s, &t)
    }

    private func equivalentAtom(
        _ phi: NodeID,
        _ value: NodeID,
        _ term: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID? {
        guard let there = try atom(phi, from: value, to: term, forward: true, in: s, &t) else { return nil }
        guard let back = try atom(phi, from: term, to: value, forward: false, in: s, &t) else {
            throw TransferError.notAnAtom(phi)
        }
        return try t.intern(.folIffIntro(there, back))
    }

    private func atom(
        _ phi: NodeID,
        from l: NodeID,
        to _: NodeID,
        forward: Bool,
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID? {
        guard Reify().names(Pattern(t[phi], in: t)) else { return nil }
        var slots = [(term: Int, unit: Unit)]()
        var occurrences = [[Int]: Int]()
        for (k, term) in terms.enumerated() {
            for u in units(phi, s.depth - 1 - term.value, [], in: t) {
                switch u.kind {
                case .term: occurrences[u.path] = k
                case .slot: slots.append((k, u))
                case .applied: throw TransferError.notAnAtom(phi)
                }
            }
        }
        if occurrences.isEmpty, slots.isEmpty { return nil }
        var source = phi
        var equivalent = [NodeID]()
        for (k, u) in slots {
            let x = s.depth - 1 - terms[k].value
            let argument = try argument(at: u.path, in: source, t)
            let at = try instantiate(try abstractIndex(argument, x, in: &t), with: try lifted(k, s, &t), in: &t)
            let next = try replacing(source, at: u.path[...], with: at, in: &t)
            equivalent.append(try slotConverted(source, next, u.path, base: base, in: s, &t, hole: equivalentAtom))
            source = next
        }
        var target = source
        for (path, k) in occurrences {
            target = try replacing(target, at: path[...], with: try lifted(k, s, &t), in: &t)
        }
        var steps = [NodeID]()
        if !occurrences.isEmpty {
            steps.append(
                forward
                    ? try close(source, target, occurrences, in: s, &t)
                    : try open(source, target, occurrences, in: s, &t)
            )
        }
        return try chained(equivalent, steps, from: l, forward: forward, in: s, &t)
    }

    private func close(
        _ source: NodeID,
        _ target: NodeID,
        _ occurrences: [[Int]: Int],
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        var f = Frame(s)
        let from = try named(atom: t[source], in: &t)
        let h = f.assume(from)
        var ys = Naming()
        _ = try ys.atom(t[source], in: &t)
        let o = try f.open(chain: .hypothesis(h), ys.chain.binders, in: &t)
        var ts = Naming(occurrences: Set(occurrences.keys))
        _ = try ts.atom(t[target], in: &t)
        var owner = [Int: (term: Int, piece: Int)]()
        for (path, site) in ts.sites {
            guard let k = occurrences[path], site.binders.count == terms[k].pieces.count else {
                throw TransferError.notAnAtom(target)
            }
            for (j, b) in site.binders.enumerated() { owner[b] = (k, j) }
        }
        var witnesses = [NodeID]()
        var facts = [NodeID]()
        var next = 0
        for b in ts.chain.binders.indices {
            if let (k, j) = owner[b] {
                witnesses.append(try f.variable(terms[k].pieces[j], in: &t))
                facts.append(try f.proof(terms[k].constraints[j], in: &t))
            } else {
                guard next < o.witnesses.count else { throw TransferError.notAnAtom(target) }
                witnesses.append(try f.variable(o.witnesses[next], in: &t))
                facts.append(try f.proof(o.constraints[next], in: &t))
                next += 1
            }
        }
        let core = try f.proof(o.core, in: &t)
        let proof = try reclosed(target, witnesses, facts, core, from: s.depth, in: f.scope, &t) { p, _, _, _ in
            throw TransferError.notItsConstraint(p)
        }
        return try f.close(proof, in: &t)
    }

    private func open(
        _ source: NodeID,
        _ target: NodeID,
        _ occurrences: [[Int]: Int],
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        var f = Frame(s)
        let from = try named(atom: t[target], in: &t)
        let h = f.assume(from)
        var ts = Naming(occurrences: Set(occurrences.keys))
        _ = try ts.atom(t[target], in: &t)
        let o = try f.open(chain: .hypothesis(h), ts.chain.binders, in: &t)
        var inSite = Set<Int>()
        var occurring = [(value: Int, term: Int, pieces: [Int], facts: [Fact])]()
        for (path, site) in ts.sites {
            guard let k = occurrences[path], case .bound(let v) = site.value else {
                throw TransferError.notAnAtom(target)
            }
            inSite.formUnion(site.binders)
            occurring.append((
                o.witnesses[v],
                k,
                site.binders.map { o.witnesses[$0] },
                site.binders.map { o.constraints[$0] },
            ))
        }
        let rest = ts.chain.binders.indices.filter { !inSite.contains($0) }
        let witnesses = try rest.map { try f.variable(o.witnesses[$0], in: &t) }
        let facts = try rest.map { try f.proof(o.constraints[$0], in: &t) }
        let core = try f.proof(o.core, in: &t)
        let equal = { (a: NodeID, b: NodeID, inner: Scope, t: inout Table) throws -> NodeID? in
            for m in occurring {
                guard
                    a == (try inner.variable(m.value, in: &t)),
                    b == (try inner.variable(terms[m.term].value, in: &t))
                else { continue }
                return try uniqueness(m.term, m.pieces, m.facts, in: inner, &t)
            }
            return nil
        }
        let proof = try reclosed(
            source,
            witnesses,
            facts,
            core,
            from: s.depth,
            in: f.scope,
            &t,
        ) { p, wanted, inner, t in
            try moved(p, wanted, equal, in: inner, &t)
        }
        return try f.close(proof, in: &t)
    }

    private func uniqueness(
        _ k: Int,
        _ pieces: [Int],
        _ facts: [Fact],
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let term = terms[k]
        let site = OpenedTerm(
            term: term.term,
            depth: term.depth,
            pieces: pieces,
            binders: term.binders,
            constraints: facts,
            value: term.value,
        )
        return try uniquenessApplied(site, term, base: base, in: s, &t)
    }

    private func moved(
        _ p: NodeID,
        _ wanted: NodeID,
        _ equal: @escaping (NodeID, NodeID, Scope, inout Table) throws -> NodeID?,
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        guard let have = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        let walk = try Replacement(base: base) { phi, l, r, inner, t in
            guard case .folPred = t[phi] else { return nil }
            return try congruent(l, r, base, { a, b, t in
                guard let e = try equal(a, b, inner, &t) else { throw TransferError.notItsConstraint(phi) }
                return e
            }, &t)
        }.proof(have, have, wanted, in: s, &t)
        return try t.intern(.folIffElimL(walk, p))
    }

    private func lifted(_ k: Int, _ s: Scope, _ t: inout Table) throws -> NodeID {
        try s.lift(terms[k].term, from: terms[k].depth, in: &t)
    }

    private func chained(
        _ equivalent: [NodeID],
        _ steps: [NodeID],
        from l: NodeID,
        forward: Bool,
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        if equivalent.isEmpty, steps.count == 1 { return steps[0] }
        var f = Frame(s)
        let cuts = try equivalent.map { try f.have($0, in: &t) }
        let implied = try steps.map { try f.have($0, in: &t) }
        let h = f.assume(l)
        var current = try f.hypothesis(h, in: &t)
        if forward {
            for c in cuts { current = try t.intern(.folIffElimL(try f.hypothesis(c, in: &t), current)) }
            for c in implied { current = try t.intern(.folImpliesElim(try f.hypothesis(c, in: &t), current)) }
        } else {
            for c in implied { current = try t.intern(.folImpliesElim(try f.hypothesis(c, in: &t), current)) }
            for c in cuts.reversed() { current = try t.intern(.folIffElimR(try f.hypothesis(c, in: &t), current)) }
        }
        return try f.close(current, in: &t)
    }

    private func directed(
        _ equivalent: NodeID,
        from l: NodeID,
        forward: Bool,
        in s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        var f = Frame(s)
        let c = try f.have(equivalent, in: &t)
        let h = f.assume(l)
        let both = try f.hypothesis(c, in: &t)
        let at = try f.hypothesis(h, in: &t)
        return try f.close(try t.intern(forward ? .folIffElimL(both, at) : .folIffElimR(both, at)), in: &t)
    }

    private func quantified(
        _ schema: BaseStatement,
        _ T: IRType?,
        _ body: NodeID,
        _ lb: NodeID,
        _ rb: NodeID,
        _ forward: Bool,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        var inner = s
        _ = inner.fix(T)
        let p = try implication(body, from: lb, to: rb, forward: forward, in: inner, &t)
        let every = try t.intern(T == .i ? .isaAllIntro(.i, body: p) : .folForallIntro(body: p))
        return try base.applied(
            schema,
            [try t.intern(.folLetterAbs(body: lb)), try t.intern(.folLetterAbs(body: rb))],
            [every],
            in: &t,
        )
    }
}

private func binary(_ n: Node) -> (NodeID, NodeID)? {
    switch n {
    case .folAnd(let a, let b), .folOr(let a, let b): (a, b)
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
         .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
         .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim,
         .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL,
         .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro, .folForallElim,
         .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll,
         .folLetter, .folLetterAbs:
        nil
    }
}
