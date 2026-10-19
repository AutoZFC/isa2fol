import IR

@frozen
public enum InstanceError: Error, Equatable, Sendable {
    case notAnInstance(NodeID)
    case notAnEquivalence(NodeID)
}

struct TermInstance {
    let base: Base

    func proof(_ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard
            case .isaAllElim(let original, let a) = t[id],
            case .ifolAll(.i, let phi)? = t.conclusion(of: original).map({ t[$0] }),
            let instance = t.conclusion(of: id)
        else { throw InstanceError.notAnInstance(id) }
        let wanted = try walked(instance, base: base, in: &t)
        return try atValue(p, a, phi, in: &t) { assumed, value, template, transfer, s, t in
            let atValue = try t.intern(.isaAllElim(assumed, value))
            guard let named = t.conclusion(of: atValue) else { throw InstanceError.notAnInstance(id) }
            let target = try s.lift(wanted, in: &t)
            let implied = try transfer.implication(template, from: named, to: target, forward: true, in: s, &t)
            return try t.intern(.folImpliesElim(implied, atValue))
        }
    }

    func witnessed(_ p: NodeID, body: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case .isaExIntro(_, let a, let phi) = t[id] else { throw InstanceError.notAnInstance(id) }
        return try atValue(p, a, phi, in: &t) { assumed, value, template, transfer, s, t in
            let some = try s.lift(try t.intern(.ifolEx(.i, body: body)), in: &t)
            guard case .ifolEx(.i, let lifted) = t[some], let premise = t.conclusion(of: assumed) else {
                throw InstanceError.notAnInstance(id)
            }
            let atValue = try instantiate(lifted, with: value, in: &t)
            let implied = try transfer.implication(template, from: premise, to: atValue, forward: false, in: s, &t)
            return try t.intern(.isaExIntro(try t.intern(.folImpliesElim(implied, assumed)), value, body: lifted))
        }
    }

    /// ⚠ THE PREMISE IS CUT, NEVER MOVED UNDER THE TERM'S OPENED NAMING: built outside it, its hypotheses would shift.
    private func atValue(
        _ p: NodeID,
        _ a: NodeID,
        _ phi: NodeID,
        in t: inout Table,
        _ finish: (NodeID, NodeID, NodeID, Transfer, Scope, inout Table) throws -> NodeID,
    ) throws -> NodeID {
        var f = Frame()
        let cut = try f.have(p, in: &t)
        let opened = try openedExistence(a, base: base, in: &f, &t)
        let value = try f.variable(opened.value, in: &t)
        let lifted = try f.scope.lift(try t.intern(.ifolAll(.i, body: phi)), in: &t)
        guard case .ifolAll(.i, let body) = t[lifted] else { throw InstanceError.notAnInstance(a) }
        let template = try instantiate(body, with: value, in: &t)
        let transfer = Transfer(base: base, terms: [opened])
        let finished = try finish(try f.hypothesis(cut, in: &t), value, template, transfer, f.scope, &t)
        return try f.close(finished, in: &t)
    }
}

struct Unit {
    enum Kind {
        case term
        case slot
        case applied
    }

    let path: [Int]
    let kind: Kind

}

func units(_ n: NodeID, _ x: Int, _ path: [Int], in t: Table) -> [Unit] {
    switch t[n] {
    case .isaBound(let k, _):
        return k == x ? [Unit(path: path, kind: .term)] : []

    case .isaConst(_, _, let args):
        return args.indices.flatMap { arguments(args[$0], x, path + [$0], in: t) }

    case .isaVarApp(let head, let args):
        let inner = args.indices.flatMap { arguments(args[$0], x, path + [$0], in: t) }
        guard case .isaBound(x, _) = t[head] else { return inner }
        return inner + [Unit(path: path, kind: .applied)]

    case .isaAbs:
        return freeVariables(n, in: t).contains { $0.index == x } ? [Unit(path: path, kind: .slot)] : []

    case .ifolAll, .ifolEx, .isaFree, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive, .isaSymmetric,
         .isaTransitive,
         .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro,
         .isaHidden,
         .isaPropBound, .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim,
         .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists,
         .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim,
         .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
         .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return []
    }
}

private func arguments(_ n: NodeID, _ x: Int, _ path: [Int], in t: Table) -> [Unit] {
    guard t.type(of: n) == .o else { return units(n, x, path, in: t) }
    return freeVariables(n, in: t).contains { $0.index == x } ? [Unit(path: path, kind: .slot)] : []
}

func argument(at path: [Int], in n: NodeID, _ t: Table) throws -> NodeID {
    var x = n
    for k in path {
        switch t[x] {
        case .isaConst(_, _, let args), .isaVarApp(_, let args): x = args[k]
        default: throw ReifyError.notATerm(x)
        }
    }
    return x
}

func replacing(_ n: NodeID, at path: ArraySlice<Int>, with x: NodeID, in t: inout Table) throws -> NodeID {
    guard let k = path.first else { return x }
    switch t[n] {
    case .isaConst(let c, let T, let args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaConst(c, T, args: replaced))

    case .isaVarApp(let f, let args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaVarApp(head: f, args: replaced))

    default:
        throw ReifyError.notATerm(n)
    }
}

typealias Hole = (NodeID, NodeID, NodeID, Scope, inout Table) throws -> NodeID?

func converted(
    _ phi: NodeID,
    _ x: Int,
    _ a: NodeID,
    base: Base,
    in t: inout Table,
    _ step: (NodeID, NodeID, Unit, inout Table) throws -> NodeID,
) throws -> NodeID? {
    var source = phi
    var joined: NodeID?
    for u in units(phi, x, [], in: t) {
        let replacement = try instantiate(
            try abstractIndex(try argument(at: u.path, in: source, t), x, in: &t),
            with: a,
            in: &t,
        )
        let target = try replacing(source, at: u.path[...], with: replacement, in: &t)
        let p = try step(source, target, u, &t)
        joined = try joined.map { try chained($0, p, base, &t) } ?? p
        source = target
    }
    return joined
}

func chained(_ p: NodeID, _ q: NodeID, _ base: Base, _ t: inout Table) throws -> NodeID {
    guard
        case .folIff(let a, let b)? = t.conclusion(of: p).map({ t[$0] }),
        case .folIff(_, let c)? = t.conclusion(of: q).map({ t[$0] })
    else { throw InstanceError.notAnEquivalence(p) }
    return try base.applied(.iffTrans, [a, b, c], [p, q], in: &t)
}

struct Sides {
    init(_ source: NodeID, _ target: NodeID, _ path: [Int], _ t: inout Table) throws {
        var ys = Naming(designated: path)
        var ts = Naming(designated: path)
        let sourceCore = try ys.atom(t[source], in: &t)
        let targetCore = try ts.atom(t[target], in: &t)
        (fy, ft) = (try ys.chain.formula(sourceCore, in: &t), try ts.chain.formula(targetCore, in: &t))
        (Y, T, sourceSite, targetSite) = (ys.chain.binders, ts.chain.binders, ys.site, ts.site)
    }

    let Y: [Binder]
    let T: [Binder]
    let sourceSite: (binders: Range<Int>, value: Ref)?
    let targetSite: (binders: Range<Int>, value: Ref)?
    let fy: NodeID
    let ft: NodeID

    func proof(
        in s: Scope,
        _ t: inout Table,
        there: (Scope, Fact, inout Table) throws -> NodeID,
        back: (Scope, Fact, inout Table) throws -> NodeID,
    ) throws -> NodeID {
        var forward = s
        var backward = s
        let fromY = forward.assume(fy)
        let fromT = backward.assume(ft)
        let p = try there(forward, .hypothesis(fromY), &t)
        let q = try back(backward, .hypothesis(fromT), &t)
        return try t.intern(.folIffIntro(
            try t.intern(.folImpliesIntro(fy, body: p)),
            try t.intern(.folImpliesIntro(ft, body: q)),
        ))
    }
}

func slotConverted(
    _ source: NodeID,
    _ target: NodeID,
    _ path: [Int],
    base: Base,
    in s: Scope,
    _ t: inout Table,
    hole: @escaping Hole,
    template: NodeID? = nil,
) throws -> NodeID {
    let sides = try Sides(source, target, path, &t)
    guard let site = sides.targetSite else { throw InstanceError.notAnInstance(target) }
    let lambda = try argument(at: path, in: template ?? source, t)
    let K = site.binders.lowerBound
    let depth = s.depth
    let definition = { (l: NodeID, r: NodeID, k: Int, s: Scope, t: inout Table) throws -> NodeID in
        let phi = try reading(try s.lift(lambda, from: depth, in: &t), at: try s.variable(k, in: &t), in: &t)
        return try Replacement(base: base, hole: hole).proof(phi, l, r, in: s, &t)
    }
    let reopened = { (
        atom: NodeID,
        o: Opened,
        s: Scope,
        t: inout Table,
        convert: (NodeID, NodeID, Scope, inout Table) throws -> NodeID,
    ) throws -> NodeID in
        try reclosed(
            atom,
            try o.witnesses.map { try s.variable($0, in: &t) },
            try o.constraints.map { try s.proof($0, in: &t) },
            try s.proof(o.core, in: &t),
            from: depth,
            in: s,
            &t,
            convert,
        )
    }
    return try sides.proof(in: s, &t, there: { s, from, t in
        try opening(from, sides.Y, in: s, &t) { s, o, t in
            try reopened(target, o, s, &t) { p, wanted, s, t in
                try t.intern(.folIffElimL(try definition(try conclusion(p, t), wanted, o.witnesses[K], s, &t), p))
            }
        }
    }, back: { s, from, t in
        try opening(from, sides.T, in: s, &t) { s, o, t in
            try reopened(source, o, s, &t) { p, wanted, s, t in
                try t.intern(.folIffElimR(try definition(wanted, try conclusion(p, t), o.witnesses[K], s, &t), p))
            }
        }
    })
}

private func reading(_ argument: NodeID, at k: NodeID, in t: inout Table) throws -> NodeID {
    guard t.type(of: argument) == .o else { return try classDefinition(argument, K: k, raw: true, in: &t) }
    return try t.intern(.folAnd(try truth(k, in: &t), try t.intern(.folIff(try holds(k, in: &t), argument))))
}

func reclosed(
    _ atom: NodeID,
    _ variables: [NodeID],
    _ facts: [NodeID],
    _ core: NodeID,
    from depth: Int,
    in s: Scope,
    _ t: inout Table,
    _ convert: (NodeID, NodeID, Scope, inout Table) throws -> NodeID,
) throws -> NodeID {
    var naming = Naming(Chain(opened: variables, shift: s.depth - depth))
    let wanted = try naming.atom(t[atom], in: &t)
    var proofs = [NodeID]()
    for (p, w) in zip(facts + [core], try naming.chain.stated() + [wanted]) {
        proofs.append(t.conclusion(of: p) == w ? p : try convert(p, w, s, &t))
    }
    let formula = try shift(try named(atom: t[atom], in: &t), by: s.depth - depth, in: &t)
    return try closing(formula, variables, Array(proofs.dropLast()), proofs[proofs.count - 1], in: &t)
}

func leibniz(
    _ p: NodeID,
    _ wanted: NodeID,
    _ equal: @escaping (Scope, inout Table) throws -> NodeID,
    _ base: Base,
    in s: Scope,
    _ t: inout Table,
) throws -> NodeID {
    let have = try conclusion(p, t)
    let walk = try Replacement(base: base) { phi, l, r, s, t in
        guard case .folPred = t[phi] else { return nil }
        let e = try equal(s, &t)
        return try congruent(l, r, base, { _, _, _ in e }, &t)
    }.proof(have, have, wanted, in: s, &t)
    return try t.intern(.folIffElimL(walk, p))
}

private func conclusion(_ p: NodeID, _ t: Table) throws -> NodeID {
    guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
    return c
}
