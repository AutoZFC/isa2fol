import IR

@frozen public enum InstanceError: Error, Equatable, Sendable {
    case notAnInstance(NodeID)
    case notAnEquivalence(NodeID)
}

struct TermInstance {
    let base: Base

    func proof(_ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case let .isaAllElim(original, a) = t[id], case let .ifolAll(.i, phi)? = t.conclusion(of: original).map({ t[$0] }),
              let instance = t.conclusion(of: id), let rewritten = t.conclusion(of: p) else { throw InstanceError.notAnInstance(id) }
        let wanted = try walked(instance, base: base, in: &t)
        let c = try closed(a, in: &t)
        let (exR, uniqR) = (try existence(of: a, in: &t), try uniqueness(of: a, in: &t))
        let ex = try t.intern(.use(.lemma(Lemma(exR)), [], try statement(exR, in: &t)))
        let uniq = try t.intern(.use(.lemma(Lemma(uniqR)), [], try statement(uniqR, in: &t)))
        var s = Scope()
        let exists = try instantiated(ex, at: try c.variables.map { try walked(try s.lift($0, in: &t), base: base, in: &t) }, c.types,
                                      guards: false, guardOf: isaGuard, in: &t)
        guard case let .ifolEx(.i, valued)? = t.conclusion(of: exists).map({ t[$0] }) else { throw InstanceError.notAnInstance(id) }
        let y = s.fix(.i), h = s.assume(valued)
        let premise = try s.lift(rewritten, in: &t)
        let assumed = s.assume(premise)
        let atY = try t.intern(.isaAllElim(try s.hypothesis(assumed, in: &t), try s.variable(y, in: &t)))
        guard let atYNamed = t.conclusion(of: atY) else { throw InstanceError.notAnInstance(id) }
        var naming = Naming(designated: [1])
        let equated = try equation(try s.variable(y, in: &t), try s.lift(a, in: &t), in: &t)
        _ = try naming.atom(t[equated], in: &t)
        guard case let .bound(value)? = naming.site?.value else { throw InstanceError.notAnInstance(id) }
        let conversion = Conversion(base: base, term: a, closed: c, uniq: uniq, witness: y, named: h,
                                    binders: naming.chain.binders, value: value)
        let walk = try Replacement(base: base, hole: conversion.atom).proof(phi, atYNamed, try s.lift(wanted, in: &t), in: s, &t)
        let body = try t.intern(.folImpliesIntro(premise, body: try t.intern(.folIffElimL(walk, atY))))
        return try t.intern(.folImpliesElim(try t.intern(.isaExElim(.i, exists, body: body)), p))
    }
}

struct Unit {
    let path: [Int]
    let kind: Kind

    enum Kind {
        case term, lambda, applied
    }
}

func units(_ n: NodeID, _ x: Int, _ path: [Int], in t: Table) -> [Unit] {
    switch t[n] {
    case let .isaBound(k, _):
        return k == x ? [Unit(path: path, kind: .term)] : []
    case let .isaConst(_, _, args):
        return args.indices.flatMap { units(args[$0], x, path + [$0], in: t) }
    case let .isaVarApp(head, args):
        let inner = args.indices.flatMap { units(args[$0], x, path + [$0], in: t) }
        guard case .isaBound(x, _) = t[head] else { return inner }
        return inner + [Unit(path: path, kind: .applied)]
    case .isaAbs:
        return freeVariables(n, in: t).contains { $0.index == x } ? [Unit(path: path, kind: .lambda)] : []
    case .ifolAll, .ifolEx, .isaFree, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive,
         .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim,
         .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists,
         .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim,
         .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
         .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return []
    }
}

func argument(at path: [Int], in n: NodeID, _ t: Table) throws -> NodeID {
    var x = n
    for k in path {
        switch t[x] {
        case let .isaConst(_, _, args), let .isaVarApp(_, args): x = args[k]
        default: throw ReifyError.notATerm(x)
        }
    }
    return x
}

func replacing(_ n: NodeID, at path: ArraySlice<Int>, with x: NodeID, in t: inout Table) throws -> NodeID {
    guard let k = path.first else { return x }
    switch t[n] {
    case let .isaConst(c, T, args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaConst(c, T, args: replaced))
    case let .isaVarApp(f, args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaVarApp(head: f, args: replaced))
    default:
        throw ReifyError.notATerm(n)
    }
}

private struct Conversion {
    let base: Base
    let term: NodeID
    let closed: Closed
    let uniq: NodeID
    let witness: Int
    let named: Int
    let binders: [Binder]
    let value: Int

    func atom(_ phi: NodeID, _ l: NodeID, _ r: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID? {
        guard Reify().names(Pattern(t[phi], in: t)) else { return nil }
        return try converted(phi, s.depth - 1 - witness, try s.lift(term, in: &t), base: base, in: &t) { source, target, u, t in
            switch u.kind {
            case .lambda: return try slotConverted(source, target, u.path, base: base, in: s, &t, hole: self.atom)
            case .term: return try self.step(source, target, u.path, in: s, &t)
            case .applied: throw InstanceError.notAnInstance(source)
            }
        }
    }

    private func step(_ source: NodeID, _ target: NodeID, _ path: [Int], in s: Scope, _ t: inout Table) throws -> NodeID {
        let sides = try Sides(source, target, path, &t)
        guard let site = sides.targetSite, case let .bound(occurrence) = site.value else { throw InstanceError.notAnInstance(target) }
        let (lower, upper, depth) = (site.binders.lowerBound, site.binders.upperBound, s.depth)
        return try sides.proof(in: s, &t, there: { s, from, t in
            try opening(from, sides.Y, in: s, &t) { s, oy, t in
                try opening(.hypothesis(self.named), self.binders, in: s, &t) { s, oh, t in
                    let witnesses = oy.witnesses[..<lower] + oh.witnesses + oy.witnesses[lower...]
                    let facts = oy.constraints[..<lower] + oh.constraints + oy.constraints[lower...]
                    return try reclosed(target, sides.T, try witnesses.map { try s.variable($0, in: &t) }, try facts.map { try s.proof($0, in: &t) },
                                        try s.proof(oy.core, in: &t), from: depth, in: s, &t) { p, wanted, s, t in
                        try leibniz(p, wanted, { s, t in try s.proof(oh.core, in: &t) }, self.base, in: s, &t)
                    }
                }
            }
        }, back: { s, from, t in
            try opening(from, sides.T, in: s, &t) { s, ot, t in
                try opening(.hypothesis(self.named), self.binders, in: s, &t) { s, oh, t in
                    let witnesses = ot.witnesses[..<lower] + ot.witnesses[upper...]
                    let facts = ot.constraints[..<lower] + ot.constraints[upper...]
                    let equal = { (s: Scope, t: inout Table) in
                        try self.returning(oh, Array(ot.witnesses[lower..<upper]), Array(ot.constraints[lower..<upper]),
                                           ot.witnesses[occurrence], in: s, &t)
                    }
                    return try reclosed(source, sides.Y, try witnesses.map { try s.variable($0, in: &t) }, try facts.map { try s.proof($0, in: &t) },
                                        try s.proof(ot.core, in: &t), from: depth, in: s, &t) { p, wanted, s, t in
                        try leibniz(p, wanted, equal, self.base, in: s, &t)
                    }
                }
            }
        })
    }

    private func returning(_ oh: Opened, _ witnesses: [Int], _ facts: [Fact], _ value2: Int, in s: Scope,
                           _ t: inout Table) throws -> NodeID {
        var p = try instantiated(uniq, at: try closed.variables.map { try walked(try s.lift($0, in: &t), base: base, in: &t) },
                                 closed.types, guards: true, guardOf: isaGuard, in: &t)
        let named = oh.witnesses.indices.map { (oh.witnesses[$0], oh.constraints[$0], binders[$0]) }
        let occurrence = witnesses.indices.map { (witnesses[$0], facts[$0], binders[$0]) }
        for (w, f, b) in named + occurrence {
            let v = try s.variable(w, in: &t)
            p = try t.intern(b == .set ? .isaAllElim(p, v) : .folForallElim(p, v))
            p = try t.intern(.folImpliesElim(p, try s.proof(f, in: &t)))
        }
        let (y, r, r2) = (try s.variable(witness, in: &t), try s.variable(oh.witnesses[value], in: &t), try s.variable(value2, in: &t))
        let yr2 = try base.claimed(.eqTrans, [y, r, r2], [try s.proof(oh.core, in: &t), p], in: &t)
        return try base.claimed(.eqSymm, [y, r2], [yr2], in: &t)
    }
}

typealias Hole = (NodeID, NodeID, NodeID, Scope, inout Table) throws -> NodeID?

func converted(_ phi: NodeID, _ x: Int, _ a: NodeID, base: Base, in t: inout Table,
               _ step: (NodeID, NodeID, Unit, inout Table) throws -> NodeID) throws -> NodeID? {
    var source = phi, joined: NodeID?
    for u in units(phi, x, [], in: t) {
        let replacement = try instantiate(try abstractIndex(try argument(at: u.path, in: source, t), x, in: &t), with: a, in: &t)
        let target = try replacing(source, at: u.path[...], with: replacement, in: &t)
        let p = try step(source, target, u, &t)
        joined = try joined.map { try chained($0, p, base, &t) } ?? p
        source = target
    }
    return joined
}

private func chained(_ p: NodeID, _ q: NodeID, _ base: Base, _ t: inout Table) throws -> NodeID {
    guard case let .folIff(a, b)? = t.conclusion(of: p).map({ t[$0] }), case let .folIff(_, c)? = t.conclusion(of: q).map({ t[$0] })
    else { throw InstanceError.notAnEquivalence(p) }
    return try base.applied(.iffTrans, [a, b, c], [p, q], in: &t)
}

struct Sides {
    let Y: [Binder]
    let T: [Binder]
    let sourceSite: (binders: Range<Int>, value: Ref)?
    let targetSite: (binders: Range<Int>, value: Ref)?
    let fy: NodeID
    let ft: NodeID

    init(_ source: NodeID, _ target: NodeID, _ path: [Int], _ t: inout Table) throws {
        var ys = Naming(designated: path), ts = Naming(designated: path)
        let (sourceCore, targetCore) = (try ys.atom(t[source], in: &t), try ts.atom(t[target], in: &t))
        (fy, ft) = (try ys.chain.formula(sourceCore, in: &t), try ts.chain.formula(targetCore, in: &t))
        (Y, T, sourceSite, targetSite) = (ys.chain.binders, ts.chain.binders, ys.site, ts.site)
    }

    func proof(in s: Scope, _ t: inout Table, there: (Scope, Fact, inout Table) throws -> NodeID,
               back: (Scope, Fact, inout Table) throws -> NodeID) throws -> NodeID {
        var forward = s, backward = s
        let fromY = forward.assume(fy), fromT = backward.assume(ft)
        let p = try there(forward, .hypothesis(fromY), &t), q = try back(backward, .hypothesis(fromT), &t)
        return try t.intern(.folIffIntro(try t.intern(.folImpliesIntro(fy, body: p)), try t.intern(.folImpliesIntro(ft, body: q))))
    }
}

func slotConverted(_ source: NodeID, _ target: NodeID, _ path: [Int], base: Base, in s: Scope, _ t: inout Table,
                   hole: @escaping Hole) throws -> NodeID {
    let sides = try Sides(source, target, path, &t)
    guard let site = sides.targetSite else { throw InstanceError.notAnInstance(target) }
    let lambda = try argument(at: path, in: source, t), K = site.binders.lowerBound, depth = s.depth
    let definition = { (l: NodeID, r: NodeID, k: Int, s: Scope, t: inout Table) throws -> NodeID in
        let phi = try classDefinition(try s.lift(lambda, from: depth, in: &t), K: try s.variable(k, in: &t), raw: true, in: &t)
        return try Replacement(base: base, hole: hole).proof(phi, l, r, in: s, &t)
    }
    let reopened = { (atom: NodeID, binders: [Binder], o: Opened, s: Scope, t: inout Table,
                      convert: (NodeID, NodeID, Scope, inout Table) throws -> NodeID) throws -> NodeID in
        try reclosed(atom, binders, try o.witnesses.map { try s.variable($0, in: &t) }, try o.constraints.map { try s.proof($0, in: &t) },
                     try s.proof(o.core, in: &t), from: depth, in: s, &t, convert)
    }
    return try sides.proof(in: s, &t, there: { s, from, t in
        try opening(from, sides.Y, in: s, &t) { s, o, t in
            try reopened(target, sides.T, o, s, &t) { p, wanted, s, t in
                try t.intern(.folIffElimL(try definition(try conclusion(p, t), wanted, o.witnesses[K], s, &t), p))
            }
        }
    }, back: { s, from, t in
        try opening(from, sides.T, in: s, &t) { s, o, t in
            try reopened(source, sides.Y, o, s, &t) { p, wanted, s, t in
                try t.intern(.folIffElimR(try definition(wanted, try conclusion(p, t), o.witnesses[K], s, &t), p))
            }
        }
    })
}

func reclosed(_ atom: NodeID, _ binders: [Binder], _ variables: [NodeID], _ facts: [NodeID], _ core: NodeID,
              from depth: Int, in s: Scope, _ t: inout Table,
              _ convert: (NodeID, NodeID, Scope, inout Table) throws -> NodeID) throws -> NodeID {
    var naming = Naming(Chain(opened: variables, shift: s.depth - depth))
    let wanted = try naming.atom(t[atom], in: &t)
    var proofs: [NodeID] = []
    for (p, w) in zip(facts + [core], try naming.chain.stated() + [wanted]) {
        proofs.append(t.conclusion(of: p) == w ? p : try convert(p, w, s, &t))
    }
    return try closing(binders, variables, Array(proofs.dropLast()), proofs[proofs.count - 1], in: &t)
}

func leibniz(_ p: NodeID, _ wanted: NodeID, _ equal: @escaping (Scope, inout Table) throws -> NodeID, _ base: Base, in s: Scope,
             _ t: inout Table) throws -> NodeID {
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
