import IR

@frozen public enum LambdaError: Error, Equatable, Sendable {
    case notAnInstance(NodeID)
    case notALambda(NodeID)
    case noBeta(NodeID)
    case notMine(String)
    case misproved(String)
}

private func shape(_ lambda: NodeID, in t: Table) throws -> (arity: Int, value: IRType) {
    var n = 0, inner = lambda
    while case let .isaAbs(T, body) = t[inner] {
        guard T == .i else { throw LambdaError.notALambda(lambda) }
        (n, inner) = (n + 1, body)
    }
    guard n > 0, let U = t.type(of: inner), U == .o || U == .i else { throw LambdaError.notALambda(lambda) }
    return (n, U)
}

func atArguments(_ lambda: NodeID, _ K: NodeID, base: Base, in t: inout Table) throws -> NodeID {
    let (n, value) = try shape(lambda, in: t)
    if value == .o {
        let ts = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
        let body = try walked(try beta(try shift(lambda, by: n, in: &t), ts, in: &t), base: base, in: &t)
        let atom = try named(atom: .isaVarApp(head: try shift(K, by: n, in: &t), args: ts), in: &t)
        var root = try t.intern(.folIff(atom, body))
        for _ in 0..<n { root = try t.intern(.ifolAll(.i, body: root)) }
        return root
    }
    let ts = try (0..<n).map { try t.intern(.isaBound(n + 1 - $0, .i)) }
    let (tau, r) = (try t.intern(.isaBound(1, .i)), try t.intern(.isaBound(0, .i)))
    let value2 = try walked(try equation(r, try beta(try shift(lambda, by: n + 2, in: &t), ts, in: &t), in: &t), base: base, in: &t)
    let applied = try t.intern(.folPred(.base("apply"), args: [tau, r, try shift(K, by: n + 2, in: &t)]))
    var root = try t.intern(.ifolAll(.i, body: try t.intern(.folIff(applied, value2))))
    let tupled = try tuple(try (0..<n).map { try t.intern(.isaBound(n - $0, .i)) }, try t.intern(.isaBound(0, .i)), in: &t)
    root = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(tupled, root))))
    for _ in 0..<n { root = try t.intern(.ifolAll(.i, body: root)) }
    guard let T = t.type(of: lambda), let function = try guarded(K, T, in: &t) else { throw LambdaError.notALambda(lambda) }
    return try t.intern(.folAnd(function, root))
}

struct LambdaInstance {
    let base: Base

    func proof(_ p: NodeID, was id: NodeID, in t: inout Table) throws -> NodeID {
        guard case let .isaAllElim(original, lambda) = t[id], let stated = t.conclusion(of: original),
              case let .ifolAll(T, psi) = t[stated], let instance = t.conclusion(of: id), let rewritten = t.conclusion(of: p),
              case let .ifolAll(_, psiNamed) = t[rewritten] else { throw LambdaError.notAnInstance(id) }
        let wanted = try walked(instance, base: base, in: &t)
        let reduction = try equivalence(T, psi, psiNamed, wanted, lambda, in: &t)
        let (f, c) = try lambdaFact(lambda, .arguments, in: &t)
        var s = Scope()
        let opened = try instantiated(try cited(f, try statement(f, base: base, in: &t), &t),
                                      at: try c.variables.map { try walked(try s.lift($0, in: &t), base: base, in: &t) }, c.types,
                                      guards: true, guardOf: isaGuard, in: &t)
        guard case let .folExists(body)? = t.conclusion(of: opened).map({ t[$0] }) else { throw LambdaError.notAnInstance(id) }
        let k = s.fix(nil), a = s.assume(body)
        let premise = try s.lift(rewritten, in: &t)
        let h = s.assume(premise)
        let K = try s.variable(k, in: &t), beta = try s.hypothesis(a, in: &t)
        var reduced = try t.intern(.folForallElim(try s.lift(reduction, in: &t), K))
        var premised = try t.intern(.folForallElim(try s.hypothesis(h, in: &t), K))
        if guardPredicate(T) != nil {
            let function = try t.intern(.folAndElimL(beta))
            reduced = try t.intern(.folImpliesElim(reduced, function))
            premised = try t.intern(.folImpliesElim(premised, function))
        }
        let concluded = try t.intern(.folIffElimL(try t.intern(.folImpliesElim(reduced, beta)), premised))
        let assumed = try t.intern(.folImpliesIntro(premise, body: concluded))
        return try t.intern(.folImpliesElim(try t.intern(.folExistsElim(opened, body: assumed)), p))
    }

    private func equivalence(_ T: IRType, _ psi: NodeID, _ psiNamed: NodeID, _ wanted: NodeID, _ lambda: NodeID,
                             in t: inout Table) throws -> NodeID {
        var s = Scope()
        let variable = s.fix(T)
        let lam = try s.lift(lambda, in: &t)
        let beta = try atArguments(lam, try s.variable(variable, in: &t), base: base, in: &t)
        let assumed = s.assume(beta)
        let hole = Beta(base: base, variable: variable, lambda: lam, depth: s.depth, assumption: assumed)
        let walk = try Replacement(base: base, hole: hole.atom).proof(psi, psiNamed, try s.lift(wanted, in: &t), in: s, &t)
        return try t.intern(.isaAllIntro(T, body: try t.intern(.folImpliesIntro(beta, body: walk))))
    }
}

private struct Beta {
    let base: Base
    let variable: Int
    let lambda: NodeID
    let depth: Int
    let assumption: Int

    func atom(_ phi: NodeID, _ l: NodeID, _ r: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID? {
        guard Reify().names(Pattern(t[phi], in: t)) else { return nil }
        let lam = try s.lift(lambda, from: depth, in: &t)
        let (_, value) = try shape(lam, in: t)
        return try converted(phi, s.depth - 1 - variable, lam, base: base, in: &t) { source, target, u, t in
            switch u.kind {
            case .lambda: return try slotConverted(source, target, u.path, base: base, in: s, &t, hole: self.atom)
            case .applied: return value == .o ? try predicate(source, s, &t) : try function(source, u.path, lam, s, &t)
            case .term: throw LambdaError.noBeta(source)
            }
        }
    }

    private func predicate(_ source: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID {
        guard case let .isaVarApp(_, args) = t[source] else { throw LambdaError.noBeta(source) }
        var q = try isaBeta(s, &t)
        for a in args { q = try t.intern(.isaAllElim(q, a)) }
        return try walked(q, base: base, in: &t)
    }

    private func isaBeta(_ s: Scope, _ t: inout Table) throws -> NodeID {
        let assumed = try s.hypothesis(assumption, in: &t)
        guard case let .hyp(index, _) = t[assumed] else { throw LambdaError.noBeta(lambda) }
        let lam = try s.lift(lambda, from: depth, in: &t), P = try s.variable(variable, in: &t)
        let (n, _) = try shape(lam, in: t)
        let xs = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
        let applied = try t.intern(.isaVarApp(head: try shift(P, by: n, in: &t), args: xs))
        var root = try t.intern(.folIff(applied, try beta(try shift(lam, by: n, in: &t), xs, in: &t)))
        for _ in 0..<n { root = try t.intern(.ifolAll(.i, body: root)) }
        return try t.intern(.hyp(index, root))
    }

    private func function(_ source: NodeID, _ path: [Int], _ lam: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID {
        guard case let .isaVarApp(F, args) = t[try argument(at: path, in: source, t)] else { throw LambdaError.noBeta(source) }
        let n = args.count
        var f = Frame(s)
        let xs = try (0..<n).map { _ in f.fix(.i) }.map { try f.variable($0, in: &t) }
        let shifted = try shift(source, by: n, in: &t)
        let sx = try replacing(shifted, at: path[...], with: try t.intern(.isaVarApp(head: try shift(F, by: n, in: &t), args: xs)), in: &t)
        let tx = try replacing(shifted, at: path[...], with: try beta(try shift(lam, by: n, in: &t), xs, in: &t), in: &t)
        let atVariables = try f.close(try applied(sx, tx, path, xs, f.scope, &t), in: &t)
        var q = try t.intern(.folIff(sx, tx))
        for _ in 0..<n { q = try t.intern(.ifolAll(.i, body: q)) }
        var g = Frame(s)
        _ = try g.have(atVariables, in: &t)
        var instance = try t.intern(.hyp(0, q))
        for a in args { instance = try t.intern(.isaAllElim(instance, a)) }
        return try g.close(try walked(instance, base: base, in: &t), in: &t)
    }

    private func applied(_ sx: NodeID, _ tx: NodeID, _ path: [Int], _ xs: [NodeID], _ s: Scope, _ t: inout Table) throws -> NodeID {
        let sides = try Sides(sx, tx, path, &t)
        guard let ys = sides.sourceSite, let ts = sides.targetSite, ys.binders.count == 2 else { throw LambdaError.noBeta(sx) }
        let (lower, upper, depth) = (ys.binders.lowerBound, ys.binders.upperBound, s.depth)
        let (lowerT, upperT) = (ts.binders.lowerBound, ts.binders.upperBound)
        let site = Array(sides.T[ts.binders])
        let body = try argument(at: path, in: tx, t)
        let beta = { (tau: NodeID, r: NodeID, tupled: NodeID, s: Scope, t: inout Table) throws -> NodeID in
            let every = try t.intern(.folAndElimR(try s.hypothesis(self.assumption, in: &t)))
            let at = try xs.map { try s.lift($0, from: depth, in: &t) } + [tau]
            return try eliminated(try eliminated(every, at: at, premises: [tupled], in: &t), at: [r], in: &t)
        }
        return try sides.proof(in: s, &t, there: { s, from, t in
            try opening(from, sides.Y, in: s, &t) { s, oy, t in
                let (tau, r) = (try s.variable(oy.witnesses[lower], in: &t), try s.variable(oy.witnesses[lower + 1], in: &t))
                let valued = try t.intern(.folIffElimL(try beta(tau, r, try s.proof(oy.constraints[lower], in: &t), s, &t),
                                                       try s.proof(oy.constraints[lower + 1], in: &t)))
                guard let named = t.conclusion(of: valued) else { throw TableError.expectedStep(valued) }
                var inner = s
                let h = inner.assume(named)
                let converted = try opening(.hypothesis(h), site, in: inner, &t) { s, oh, t in
                    let witnesses = oy.witnesses[..<lower] + oh.witnesses + oy.witnesses[upper...]
                    let facts = oy.constraints[..<lower] + oh.constraints + oy.constraints[upper...]
                    return try reclosed(tx, sides.T, try witnesses.map { try s.variable($0, in: &t) }, try facts.map { try s.proof($0, in: &t) },
                                        try s.proof(oy.core, in: &t), from: depth, in: s, &t) { p, wanted, s, t in
                        try leibniz(p, wanted, { s, t in try s.proof(oh.core, in: &t) }, self.base, in: s, &t)
                    }
                }
                return try t.intern(.folImpliesElim(try t.intern(.folImpliesIntro(named, body: converted)), valued))
            }
        }, back: { s, from, t in
            try opening(from, sides.T, in: s, &t) { s, ot, t in
                let v: NodeID
                switch ts.value {
                case let .bound(k): v = try s.variable(ot.witnesses[k], in: &t)
                case let .outer(x): v = try s.lift(x, from: depth, in: &t)
                }
                let pair = TupleFact(arity: xs.count, fact: .existence)
                let exists = try eliminated(try cited(pair, try statement(pair, in: &t), &t), at: try xs.map { try s.lift($0, from: depth, in: &t) }, in: &t)
                guard case let .ifolEx(.i, tupled)? = t.conclusion(of: exists).map({ t[$0] }) else { throw LambdaError.noBeta(sx) }
                var inner = s
                let tw = inner.fix(.i), ht = inner.assume(tupled)
                let (tau, vIn) = (try inner.variable(tw, in: &t), try inner.lift(v, from: s.depth, in: &t))
                var zf = Frame(inner)
                let zl = zf.fix(.i)
                let z = try zf.variable(zl, in: &t)
                let hz = zf.assume(try t.intern(.folPred(.base("eq"), args: [z, try zf.scope.lift(vIn, from: inner.depth, in: &t)])))
                let atZ = try reclosed(try equation(z, try zf.scope.lift(body, from: depth, in: &t), in: &t), site,
                                       try ot.witnesses[lowerT..<upperT].map { try zf.variable($0, in: &t) },
                                       try ot.constraints[lowerT..<upperT].map { try zf.proof($0, in: &t) },
                                       try zf.hypothesis(hz, in: &t), from: zf.scope.depth, in: zf.scope, &t) { p, _, _, _ in
                    throw LambdaError.noBeta(p)
                }
                let valued = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(try zf.close(atZ, in: &t), vIn)),
                                                          try eliminated(try base.cite(.eqRefl, in: &t), at: [vIn], in: &t)))
                let atTau = try inner.hypothesis(ht, in: &t)
                let apply = try t.intern(.folIffElimR(try beta(tau, vIn, atTau, inner, &t), valued))
                let variables = try ot.witnesses[..<lowerT].map { try inner.variable($0, in: &t) } + [tau, vIn]
                    + ot.witnesses[upperT...].map { try inner.variable($0, in: &t) }
                let facts = try ot.constraints[..<lowerT].map { try inner.proof($0, in: &t) } + [atTau, apply]
                    + ot.constraints[upperT...].map { try inner.proof($0, in: &t) }
                let closed = try reclosed(sx, sides.Y, variables, facts, try inner.proof(ot.core, in: &t), from: depth, in: inner, &t) { p, _, _, _ in
                    throw LambdaError.noBeta(p)
                }
                return try t.intern(.isaExElim(.i, exists, body: closed))
            }
        })
    }
}

struct LambdaProofs {
    let base: Base

    func arguments(_ f: LambdaFact, in t: inout Table) throws -> NodeID {
        var fr = Frame()
        var guards: [Int: Int] = [:]
        for (j, T) in f.types.enumerated() {
            let v = fr.fix(T)
            if T != .i, let g = try guarded(try fr.variable(v, in: &t), T, in: &t) { guards[j] = fr.assume(g) }
        }
        let vs = try f.types.indices.map { try fr.variable($0, in: &t) }
        let classF = LambdaFact(lambda: f.lambda, types: f.types, fact: .classExists, name: "CLASS_" + fingerprint(f.lambda, t))
        let atV = try instantiated(try cited(classF, try statement(classF, base: base, in: &t), &t), at: vs, f.types, guards: false,
                                   guardOf: isaGuard, in: &t)
        let (k, h) = try fr.open(atV, in: &t)
        let (n, value) = try shape(f.lambda, in: t)
        guard value == .i else {
            return try fr.close(try t.intern(.folExistsIntro(try predicate(f, n, k, h, fr, &t), try fr.variable(k, in: &t))), in: &t)
        }
        let functionF = LambdaFact(lambda: f.lambda, types: f.types, fact: .function, name: "FUNC_" + fingerprint(f.lambda, t))
        let atK = try f.types.indices.map { try fr.variable($0, in: &t) }
        let guardOf = { (x: NodeID, _: IRType, t: inout Table) throws -> NodeID in
            guard let j = atK.firstIndex(of: x), let g = guards[j] else { throw LambdaError.notMine(f.name) }
            return try fr.hypothesis(g, in: &t)
        }
        let atVF = try instantiated(try cited(functionF, try statement(functionF, base: base, in: &t), &t), at: atK, f.types, guards: true,
                                    guardOf: guardOf, in: &t)
        let K = try fr.variable(k, in: &t)
        let function = try eliminated(atVF, at: [K], premises: [try fr.hypothesis(h, in: &t)], in: &t)
        let both = try t.intern(.folAndIntro(function, try self.function(f, n, k, h, fr, &t)))
        return try fr.close(try t.intern(.folExistsIntro(both, K)), in: &t)
    }

    private func predicate(_ f: LambdaFact, _ n: Int, _ k: Int, _ h: Int, _ fr: Frame, _ t: inout Table) throws -> NodeID {
        var sub = Frame(fr.scope)
        let ts = (0..<n).map { _ in sub.fix(.i) }
        let body = { (f2: Frame, t: inout Table) throws -> NodeID in
            try walked(try beta(try f2.scope.lift(f.lambda, from: f.types.count, in: &t), try ts.map { try f2.variable($0, in: &t) }, in: &t),
                       base: self.base, in: &t)
        }
        var each = Frame(sub.scope)
        let tw = each.fix(.i)
        let tupled = each.assume(try tuple(try ts.map { try each.variable($0, in: &t) }, try each.variable(tw, in: &t), in: &t))
        let d = try each.have(try eliminated(try each.hypothesis(h, in: &t), at: [try each.variable(tw, in: &t)], in: &t), in: &t)
        let c = try sub.have(try each.close(try atTuple(d, tupled, ts, tw, body, each, &t), in: &t), in: &t)
        var fw = Frame(sub.scope)
        let atom = try named(atom: .isaVarApp(head: try fw.variable(k, in: &t), args: try ts.map { try fw.variable($0, in: &t) }), in: &t)
        let ha = fw.assume(atom)
        let (tau, th) = try fw.open(try fw.hypothesis(ha, in: &t), in: &t)
        let atTau = try eliminated(try fw.hypothesis(c, in: &t), at: [try fw.variable(tau, in: &t)],
                                   premises: [try fw.proof(.left(.hypothesis(th)), in: &t)], in: &t)
        let forward = try fw.close(try t.intern(.folIffElimL(atTau, try fw.proof(.right(.hypothesis(th)), in: &t))), in: &t)
        var bw = Frame(sub.scope)
        let hb = bw.assume(try body(bw, &t))
        let pair = TupleFact(arity: n, fact: .existence)
        let (tau2, th2) = try bw.open(try eliminated(try cited(pair, try statement(pair, in: &t), &t), at: try ts.map { try bw.variable($0, in: &t) }, in: &t), in: &t)
        let atTau2 = try eliminated(try bw.hypothesis(c, in: &t), at: [try bw.variable(tau2, in: &t)],
                                    premises: [try bw.hypothesis(th2, in: &t)], in: &t)
        let member = try t.intern(.folIffElimR(atTau2, try bw.hypothesis(hb, in: &t)))
        let closed = try t.intern(.isaExIntro(try t.intern(.folAndIntro(try bw.hypothesis(th2, in: &t), member)), try bw.variable(tau2, in: &t)))
        let backward = try bw.close(closed, in: &t)
        return try sub.close(try t.intern(.folIffIntro(forward, backward)), in: &t)
    }

    private func function(_ f: LambdaFact, _ n: Int, _ k: Int, _ h: Int, _ fr: Frame, _ t: inout Table) throws -> NodeID {
        var sub = Frame(fr.scope)
        let ts = (0..<n).map { _ in sub.fix(.i) }
        let tw = sub.fix(.i)
        let tupled = sub.assume(try tuple(try ts.map { try sub.variable($0, in: &t) }, try sub.variable(tw, in: &t), in: &t))
        let valued = { (r: Int, f2: Frame, t: inout Table) throws -> NodeID in
            let b = try beta(try f2.scope.lift(f.lambda, from: f.types.count, in: &t), try ts.map { try f2.variable($0, in: &t) }, in: &t)
            return try walked(try equation(try f2.variable(r, in: &t), b, in: &t), base: self.base, in: &t)
        }
        var each = Frame(sub.scope)
        let r = each.fix(.i)
        let d = try each.have(try eliminated(try each.hypothesis(h, in: &t), at: [try each.variable(tw, in: &t), try each.variable(r, in: &t)], in: &t), in: &t)
        let member = try sub.have(try each.close(try atTuple(d, tupled, ts, tw, { f2, t in try valued(r, f2, &t) }, each, &t), in: &t), in: &t)
        let lam = try sub.scope.lift(f.lambda, from: f.types.count, in: &t)
        let b = try beta(lam, try ts.map { try sub.variable($0, in: &t) }, in: &t)
        let c = try closed(b, in: &t), ex = try existence(of: b, in: &t)
        let (y, hy) = try sub.open(try instantiated(try cited(ex, try statement(ex, in: &t), &t), at: c.variables, c.types, guards: false,
                                                    guardOf: isaGuard, in: &t), in: &t)
        let Y = try sub.variable(y, in: &t)
        let atY = try t.intern(.folIffElimR(try eliminated(try sub.hypothesis(member, in: &t), at: [Y], in: &t), try sub.hypothesis(hy, in: &t)))
        let some = try t.intern(.isaExIntro(atY, Y))
        var last = Frame(sub.scope)
        let r2 = last.fix(.i)
        let R = try last.variable(r2, in: &t), tau = try last.variable(tw, in: &t)
        let pmem = try eliminated(try eliminated(try base.cite(.applyPmem, in: &t), at: [try last.variable(k, in: &t), tau],
                                                 premises: [try last.scope.lift(some, from: sub.scope.depth, in: &t)], in: &t), at: [R], in: &t)
        let atR = try eliminated(try last.hypothesis(member, in: &t), at: [R], in: &t)
        guard case let .folIff(a, m)? = t.conclusion(of: pmem).map({ t[$0] }), case let .folIff(_, c2)? = t.conclusion(of: atR).map({ t[$0] })
        else { throw LambdaError.notMine(f.name) }
        let chained = try base.applied(.iffTrans, [a, m, c2], [pmem, atR], in: &t)
        return try sub.close(try last.close(chained, in: &t), in: &t)
    }

    private func atTuple(_ d: Int, _ tupled: Int, _ ts: [Int], _ tw: Int, _ body: (Frame, inout Table) throws -> NodeID,
                         _ f: Frame, _ t: inout Table) throws -> NodeID {
        let definition = try f.hypothesis(d, in: &t)
        guard case let .folIff(member, _)? = t.conclusion(of: definition).map({ t[$0] }) else {
            throw LambdaError.notMine("a class's definition")
        }
        let n = ts.count
        var fw = Frame(f.scope)
        let hm = fw.assume(member)
        let (xs, conj) = try fw.open(try t.intern(.folIffElimL(try fw.hypothesis(d, in: &t), try fw.hypothesis(hm, in: &t))), count: n, in: &t)
        let inj = TupleFact(arity: n, fact: .injectivity)
        let equal = try eliminated(try cited(inj, try statement(inj, in: &t), &t), at: try (xs + ts + [tw]).map { try fw.variable($0, in: &t) },
                                   premises: [try fw.proof(.left(conj), in: &t), try fw.hypothesis(tupled, in: &t)], in: &t)
        let e = try fw.have(equal, in: &t)
        let moved = try transported(try fw.proof(.right(conj), in: &t), to: try body(fw, &t), xs, ts, equalities: e, fw, &t)
        let forward = try fw.close(moved, in: &t)
        var bw = Frame(f.scope)
        let hb = bw.assume(try body(bw, &t))
        var witness = try t.intern(.folAndIntro(try bw.hypothesis(tupled, in: &t), try bw.hypothesis(hb, in: &t)))
        for x in ts.reversed() { witness = try t.intern(.isaExIntro(witness, try bw.variable(x, in: &t))) }
        let backward = try bw.close(try t.intern(.folIffElimR(try bw.hypothesis(d, in: &t), witness)), in: &t)
        return try t.intern(.folIffIntro(forward, backward))
    }

    private func transported(_ p: NodeID, to wanted: NodeID, _ xs: [Int], _ ts: [Int], equalities e: Int, _ f: Frame,
                             _ t: inout Table) throws -> NodeID {
        guard let have = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        if have == wanted { return p }
        let n = xs.count
        let walk = try Replacement(base: base) { phi, l, r, s, t in
            guard case .folPred = t[phi] else { return nil }
            return try congruent(l, r, self.base, { a, b, t in
                for j in 0..<n {
                    guard a == (try s.variable(xs[j], in: &t)), b == (try s.variable(ts[j], in: &t)) else { continue }
                    var fact = Fact.hypothesis(e)
                    for _ in 0..<j { fact = .right(fact) }
                    return try s.proof(j < n - 1 ? .left(fact) : fact, in: &t)
                }
                throw LambdaError.noBeta(phi)
            }, &t)
        }.proof(have, have, wanted, in: f.scope, &t)
        return try t.intern(.folIffElimL(walk, p))
    }
}

public struct LambdaProver: Prover {
    public let name = "lambda"
    let base: Base

    public init(base: Base) { self.base = base }

    public func owns(_ l: Lemma) -> Owned? {
        guard let f = l.request as? LambdaFact, f.fact == .arguments else { return nil }
        return .rule
    }

    public func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        guard let f = l.request as? LambdaFact, f.fact == .arguments else { throw LambdaError.notMine(l.name) }
        let proof = try LambdaProofs(base: base).arguments(f, in: &t)
        guard t.conclusion(of: proof) == statement else { throw LambdaError.misproved(l.name) }
        return proof
    }

    public func defines(_ c: Defined) -> Owned? { nil }

    public func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        throw LambdaError.notMine(c.definitionName)
    }
}
