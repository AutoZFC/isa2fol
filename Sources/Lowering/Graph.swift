import IR

@frozen public enum GraphError: Error, Equatable, Sendable {
    case noDefinition(String)
    case notMine(String)
    case unexpected(String)
}

private enum Member {
    case term((Scope, [NodeID], inout Table) throws -> NodeID)
    case relation(ex: BaseStatement, uniq: BaseStatement, cong: BaseStatement)
    case primReplace(Int)
}

struct GraphProofs {
    let base: Base
    let definitions: [Definition]

    func prove(_ f: ConstantFact, in t: inout Table) throws -> NodeID {
        switch f.fact {
        case .existence: return try setExistence(f.constant, &t)
        case .uniqueness: return try setUniqueness(f.constant, &t)
        case .classExists, .lift: throw GraphError.notMine(f.name)
        case .agreement: return try agreement(f, &t)
        case .totality: return try totality(f, &t)
        case .function: return try function(f, &t)
        }
    }

    func prove(_ f: LambdaFact, in t: inout Table) throws -> NodeID {
        switch f.fact {
        case .classExists, .arguments: throw GraphError.notMine(f.name)
        case .function: return try lambdaFunction(f, &t)
        }
    }

    private func definitionCited(_ c: Constant, _ t: inout Table) throws -> NodeID {
        switch c {
        case .primitive(.zf(.pow)): return try base.cite(.zfPowDef, in: &t)
        case .primitive(.zf(.union)): return try base.cite(.zfUnionDef, in: &t)
        case .primitive(.zf(.primReplace)): return try base.cite(.zfPrimReplaceDef, in: &t)
        case let .defined(d): return try t.intern(.use(.definition(d), [], try atDefinition(d, definitions, in: &t)))
        case .primitive(.zf(.mem)), .primitive(.zf(.zero)), .primitive(.zf(.inf)), .primitive(.pure), .primitive(.ifol), .declared:
            throw GraphError.noDefinition(c.name)
        }
    }

    private func definition(_ d: Defined) throws -> Definition {
        guard let found = definitions.first(where: { $0.defines == .constant(d) }) else { throw GraphError.noDefinition(d.name) }
        return found
    }

    private func member(_ c: Constant, _ T: IRType, classes ps: [Int]) throws -> Member {
        switch c {
        case .primitive(.zf(.pow)): return .relation(ex: .powEX, uniq: .powUNIQ, cong: .powCONG)
        case .primitive(.zf(.union)): return .relation(ex: .unionEX, uniq: .unionUNIQ, cong: .unionCONG)
        case .primitive(.zf(.primReplace)): return .primReplace(ps[0])
        case let .defined(d):
            let definiens = try definition(d).definiens
            return .term { s, xs, t in
                var sets = xs[...], classes = ps[...]
                let args = try T.domains.map { D -> NodeID in D == .i ? sets.removeFirst() : try s.variable(classes.removeFirst(), in: &t) }
                return try beta(definiens, args, in: &t)
            }
        case .primitive(.zf(.mem)), .primitive(.zf(.zero)), .primitive(.zf(.inf)), .primitive(.pure), .primitive(.ifol), .declared:
            throw GraphError.noDefinition(c.name)
        }
    }

    private func graph(_ c: Constant, _ C: Int, _ ps: [Int], _ hc: Int) -> (Scope, inout Table) throws -> NodeID {
        { s, t in
            let def = try eliminated(try definitionCited(c, &t), at: try ([C] + ps).map { try s.variable($0, in: &t) }, in: &t)
            return try t.intern(.folIffElimL(def, try s.hypothesis(hc, in: &t)))
        }
    }

    private func named(_ c: Constant, _ C: Int, _ ps: [Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        try t.intern(.folPred(.constant(c), args: try ([C] + ps).map { try f.variable($0, in: &t) }))
    }

    private func totality(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { $0 != .i }, m = f.type.domains.count - classes.count
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }
        let C = fr.fix(nil)
        let hc = fr.assume(try named(f.constant, C, ps, fr, &t))
        let xs = (0..<m).map { _ in fr.fix(.i) }
        let tau = fr.fix(.i)
        let ht = fr.assume(try tuple(try xs.map { try fr.variable($0, in: &t) }, try fr.variable(tau, in: &t), in: &t))
        let kind = try member(f.constant, f.type, classes: ps)
        let valued = { (y: NodeID, value: NodeID, g: Frame, t: inout Table) throws -> NodeID in
            let gr = try eliminated(try self.graph(f.constant, C, ps, hc)(g.scope, &t), at: [try g.variable(tau, in: &t), y], in: &t)
            var inside = try t.intern(.folAndIntro(try g.hypothesis(ht, in: &t), value))
            for x in xs.reversed() { inside = try t.intern(.isaExIntro(inside, try g.variable(x, in: &t))) }
            return try t.intern(.folIffElimR(gr, inside))
        }
        let variableBody: NodeID? = try {
            guard case let .term(body) = kind else { return nil }
            let b = try body(fr.scope, try xs.map { try fr.variable($0, in: &t) }, &t)
            if case .isaBound = t[b] { return b }
            return nil
        }()
        if let x = variableBody {
            var z = Frame(fr.scope)
            let zl = z.fix(.i)
            let hz = z.assume(try t.intern(.folPred(.base("eq"), args: [try z.variable(zl, in: &t), try z.scope.lift(x, from: fr.scope.depth, in: &t)])))
            let everyZ = try z.close(try valued(try z.variable(zl, in: &t), try z.hypothesis(hz, in: &t), z, &t), in: &t)
            let reflexive = try eliminated(try base.cite(.eqRefl, in: &t), at: [x], in: &t)
            let atX = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(everyZ, x)), reflexive))
            return try fr.close(try t.intern(.isaExIntro(atX, x)), in: &t)
        }
        let (y, value) = try existence(kind, xs, &fr, &t)
        return try fr.close(try t.intern(.isaExIntro(try valued(y, value, fr, &t), y)), in: &t)
    }

    private func existence(_ kind: Member, _ xs: [Int], _ fr: inout Frame, _ t: inout Table) throws -> (NodeID, NodeID) {
        switch kind {
        case let .term(body):
            let b = try body(fr.scope, try xs.map { try fr.variable($0, in: &t) }, &t)
            let r = try Lowering.existence(of: b, in: &t), c = try closed(b, in: &t)
            let ex = try instantiated(try cited(r, try statement(r, in: &t), &t), at: c.variables, c.types, guards: false,
                                      guardOf: isaGuard, in: &t)
            let (w, h) = try fr.open(ex, in: &t)
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))
        case let .relation(ex, _, _):
            let (w, h) = try fr.open(try eliminated(try base.cite(ex, in: &t), at: [try fr.variable(xs[0], in: &t)], in: &t), in: &t)
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))
        case let .primReplace(P):
            let at = [try fr.variable(P, in: &t), try fr.variable(xs[0], in: &t)]
            let (w, h) = try fr.open(try eliminated(try base.cite(.zfPrimReplaceValue, in: &t), at: at, in: &t), in: &t)
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))
        }
    }

    private func function(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { $0 != .i }, m = f.type.domains.count - classes.count
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }
        var guards: [Int: Int] = [:]
        for (j, D) in classes.enumerated() where isFunctionClass(D) {
            if let g = try guarded(try fr.variable(ps[j], in: &t), D, in: &t) { guards[ps[j]] = fr.assume(g) }
        }
        let C = fr.fix(nil)
        let hc = fr.assume(try named(f.constant, C, ps, fr, &t))
        let kind = try member(f.constant, f.type, classes: ps)
        return try fr.close(try singleValued(graph(f.constant, C, ps, hc), C, kind, arity: m, guards, fr, &t), in: &t)
    }

    private func lambdaFunction(_ f: LambdaFact, _ t: inout Table) throws -> NodeID {
        var fr = Frame()
        var guards: [Int: Int] = [:]
        for T in f.types {
            let v = fr.fix(T)
            if T != .i, let g = try guarded(try fr.variable(v, in: &t), T, in: &t) { guards[v] = fr.assume(g) }
        }
        let outer = fr.scope.depth
        let K = fr.fix(nil)
        let lambda = try fr.scope.lift(f.lambda, from: outer, in: &t), at = fr.scope.depth
        let hK = fr.assume(try classDefinition(lambda, K: try fr.variable(K, in: &t), in: &t))
        var m = 0, inner = lambda
        while case let .isaAbs(_, body) = t[inner] { (m, inner) = (m + 1, body) }
        let kind = Member.term { s, xs, t in try beta(try s.lift(lambda, from: at, in: &t), xs, in: &t) }
        return try fr.close(try singleValued({ s, t in try s.hypothesis(hK, in: &t) }, K, kind, arity: m, guards, fr, &t), in: &t)
    }

    private func singleValued(_ graph: @escaping (Scope, inout Table) throws -> NodeID, _ K: Int, _ kind: Member, arity m: Int,
                              _ guards: [Int: Int], _ outer: Frame, _ t: inout Table) throws -> NodeID {
        var sub = Frame(outer.scope)
        let (tt, r, s) = (sub.fix(.i), sub.fix(.i), sub.fix(.i))
        let value = { (v: Int, f: Frame, t: inout Table) throws -> NodeID in
            try t.intern(.folPred(.base("pmem"), args: [try f.variable(tt, in: &t), try f.variable(v, in: &t), try f.variable(K, in: &t)]))
        }
        let hr = sub.assume(try value(r, sub, &t)), hs = sub.assume(try value(s, sub, &t))
        let open = { (v: Int, h: Int, f: inout Frame, t: inout Table) throws -> (witnesses: [Int], body: Fact) in
            let at = try eliminated(try graph(f.scope, &t), at: [try f.variable(tt, in: &t), try f.variable(v, in: &t)], in: &t)
            let e = try t.intern(.folIffElimL(at, try f.hypothesis(h, in: &t)))
            if m == 0 { return ([], .hypothesis(try f.have(e, in: &t))) }
            return try f.open(e, count: m, in: &t)
        }
        let (xs, conj) = try open(r, hr, &sub, &t)
        let (xs2, conj2) = try open(s, hs, &sub, &t)
        var moved = Fact.right(conj2)
        if m > 0 {
            let f = TupleFact(arity: m, fact: .injectivity)
            let inj = try eliminated(try cited(f, try statement(f, in: &t), &t),
                                     at: try (xs + xs2 + [tt]).map { try sub.variable($0, in: &t) },
                                     premises: [try sub.proof(.left(conj), in: &t), try sub.proof(.left(conj2), in: &t)], in: &t)
            let equal = try sub.have(inj, in: &t)
            let projection = { (j: Int) -> Fact in
                var fact = Fact.hypothesis(equal)
                for _ in 0..<j { fact = .right(fact) }
                return j < m - 1 ? .left(fact) : fact
            }
            moved = .hypothesis(try sub.have(try transport(kind, from: xs2, to: xs, projection, value: s, at: tt, moved, graph, sub, &t), in: &t))
        }
        let eq = try unique(kind, xs, r, s, .right(conj), moved, guards, &sub, &t)
        let rhs = try sub.close(eq, in: &t)
        let def = try eliminated(try base.cite(.functionDef, in: &t), at: [try outer.variable(K, in: &t)], in: &t)
        return try t.intern(.folIffElimR(def, rhs))
    }

    private func transport(_ kind: Member, from xs2: [Int], to xs: [Int], _ projection: @escaping (Int) -> Fact, value s: Int, at tt: Int,
                           _ given: Fact, _ graph: (Scope, inout Table) throws -> NodeID, _ f: Frame,
                           _ t: inout Table) throws -> NodeID {
        let source = try f.proof(given, in: &t)
        switch kind {
        case let .relation(_, _, cong):
            let eq = try symmetric(try f.proof(projection(0), in: &t), &t)
            return try eliminated(try base.cite(cong, in: &t), at: [try f.variable(xs2[0], in: &t), try f.variable(xs[0], in: &t),
                                                                    try f.variable(s, in: &t)], premises: [eq, source], in: &t)
        case .term, .primReplace:
            guard let from = t.conclusion(of: source) else { throw TableError.expectedStep(source) }
            var rhs = try graphBody(try eliminated(try graph(f.scope, &t), at: [try f.variable(tt, in: &t), try f.variable(s, in: &t)], in: &t), &t)
            for x in xs {
                guard case let .ifolEx(.i, body) = t[rhs] else { throw GraphError.unexpected("a graph definition's entries") }
                rhs = try instantiate(body, with: try f.variable(x, in: &t), in: &t)
            }
            guard case let .folAnd(_, to) = t[rhs] else { throw GraphError.unexpected("a graph definition's member") }
            let walk = try Replacement(base: base) { phi, l, r, s, t in
                guard case .folPred = t[phi], l != r else { return nil }
                return try congruent(l, r, self.base, { a, b, t in
                    for j in xs.indices where try s.variable(xs2[j], in: &t) == a && s.variable(xs[j], in: &t) == b {
                        return try self.symmetric(try s.proof(projection(j), in: &t), &t)
                    }
                    throw GraphError.unexpected("an atom moved at no entry")
                }, &t)
            }.proof(from, from, to, in: f.scope, &t)
            return try t.intern(.folIffElimL(walk, source))
        }
    }

    private func unique(_ kind: Member, _ xs: [Int], _ r: Int, _ s: Int, _ mr: Fact, _ ms: Fact, _ guards: [Int: Int],
                        _ f: inout Frame, _ t: inout Table) throws -> NodeID {
        switch kind {
        case let .term(body):
            let b = try body(f.scope, try xs.map { try f.variable($0, in: &t) }, &t), depth = f.scope.depth
            if case .isaBound = t[b] {
                return try eliminated(try base.cite(.eqTrans, in: &t), at: [try f.variable(r, in: &t), b, try f.variable(s, in: &t)],
                                      premises: [try f.proof(mr, in: &t), try symmetric(try f.proof(ms, in: &t), &t)], in: &t)
            }
            var naming = Naming()
            _ = try naming.name(b, [], &t)
            let binders = naming.chain.binders
            let o1 = try f.open(chain: mr, binders, in: &t), o2 = try f.open(chain: ms, binders, in: &t)
            let (rv, sv) = (try f.variable(r, in: &t), try f.variable(s, in: &t))
            let request = try uniqueness(of: b, in: &t), c = try closed(try f.scope.lift(b, from: depth, in: &t), in: &t)
            var p = try instantiated(try cited(request, try statement(request, in: &t), &t), at: c.variables, c.types, guards: true,
                                     guardOf: { x, _, t in try self.guardOf(x, guards, f, &t) }, in: &t)
            for o in [o1, o2] {
                for k in binders.indices {
                    p = try eliminated(p, at: [try f.variable(o.witnesses[k], in: &t)], premises: [try f.proof(o.constraints[k], in: &t)], in: &t)
                }
            }
            let (core, core2) = (try f.proof(o1.core, in: &t), try f.proof(o2.core, in: &t))
            guard case let .folPred(_, cores)? = t.conclusion(of: core).map({ t[$0] }), cores.count == 2,
                  case let .folPred(_, cores2)? = t.conclusion(of: core2).map({ t[$0] }), cores2.count == 2
            else { throw GraphError.unexpected("a member's core") }
            let toValue = try eliminated(try base.cite(.eqTrans, in: &t), at: [rv, cores[1], cores2[1]],
                                         premises: [try f.proof(o1.core, in: &t), p], in: &t)
            return try eliminated(try base.cite(.eqTrans, in: &t), at: [rv, cores2[1], sv],
                                  premises: [toValue, try symmetric(try f.proof(o2.core, in: &t), &t)], in: &t)
        case let .relation(_, uniq, _):
            return try eliminated(try base.cite(uniq, in: &t), at: [try f.variable(xs[0], in: &t), try f.variable(r, in: &t), try f.variable(s, in: &t)],
                                  premises: [try f.proof(mr, in: &t), try f.proof(ms, in: &t)], in: &t)
        case .primReplace:
            return try replacedUnique(try f.variable(r, in: &t), try f.variable(s, in: &t), mr, ms, f, &t)
        }
    }

    private func replacedUnique(_ r: NodeID, _ s: NodeID, _ mr: Fact, _ ms: Fact, _ f: Frame, _ t: inout Table) throws -> NodeID {
        let goal = try t.intern(.folPred(.base("eq"), args: [r, s]))
        let (pr, ps) = (try f.proof(mr, in: &t), try f.proof(ms, in: &t))
        guard case let .folOr(rl, rr)? = t.conclusion(of: pr).map({ t[$0] }),
              case let .folOr(sl, sr)? = t.conclusion(of: ps).map({ t[$0] }) else {
            throw GraphError.unexpected("PrimReplace's two branches")
        }
        let branch = { (a: NodeID, body: (Frame, Int, inout Table) throws -> NodeID, f: Frame, t: inout Table) throws -> NodeID in
            var g = Frame(f.scope)
            let h = g.assume(a)
            return try g.close(try body(g, h, &t), in: &t)
        }
        let absurd = { (no: Fact, yes: Fact, g: Frame, t: inout Table) throws -> NodeID in
            let bottom = try t.intern(.folNotElim(try g.proof(no, in: &t), try g.proof(yes, in: &t)))
            return try t.intern(.folBottomElim(bottom, try g.scope.lift(goal, from: f.scope.depth, in: &t)))
        }
        let whenMatrix = try branch(rl, { g, h1, t in
            let both = try branch(sl, { g2, h2, t in try self.extensional(r, s, .right(.hypothesis(h1)), .right(.hypothesis(h2)), g2, from: f, &t) }, g, &t)
            let mixed = try branch(sr, { g2, h2, t in try absurd(.left(.hypothesis(h2)), .left(.hypothesis(h1)), g2, &t) }, g, &t)
            return try t.intern(.folOrElim(try g.proof(ms, in: &t), both, mixed))
        }, f, &t)
        let whenEmpty = try branch(rr, { g, h1, t in
            let mixed = try branch(sl, { g2, h2, t in try absurd(.left(.hypothesis(h1)), .left(.hypothesis(h2)), g2, &t) }, g, &t)
            let both = try branch(sr, { g2, h2, t in
                try eliminated(try self.base.cite(.zeroUNIQ, in: &t), at: [try g2.scope.lift(r, from: f.scope.depth, in: &t),
                                                                          try g2.scope.lift(s, from: f.scope.depth, in: &t)],
                               premises: [try g2.proof(.right(.hypothesis(h1)), in: &t), try g2.proof(.right(.hypothesis(h2)), in: &t)], in: &t)
            }, g, &t)
            return try t.intern(.folOrElim(try g.proof(ms, in: &t), mixed, both))
        }, f, &t)
        return try t.intern(.folOrElim(try f.proof(mr, in: &t), whenMatrix, whenEmpty))
    }

    private func extensional(_ r: NodeID, _ s: NodeID, _ mr: Fact, _ ms: Fact, _ g: Frame, from f: Frame,
                             _ t: inout Table) throws -> NodeID {
        var each = Frame(g.scope)
        let vl = each.fix(.i), v = try each.variable(vl, in: &t)
        let agree = try iffThrough(try eliminated(try each.proof(mr, in: &t), at: [v], in: &t),
                                   try eliminated(try each.proof(ms, in: &t), at: [v], in: &t), base, &t)
        let everywhere = try each.close(agree, in: &t)
        let (rg, sg) = (try g.scope.lift(r, from: f.scope.depth, in: &t), try g.scope.lift(s, from: f.scope.depth, in: &t))
        return try t.intern(.folIffElimR(try eliminated(try base.cite(.extensionality, in: &t), at: [rg, sg], in: &t), everywhere))
    }

    private func agreement(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { $0 != .i }
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }, ps2 = classes.map { fr.fix($0) }
        let (C, C2) = (fr.fix(nil), fr.fix(nil))
        var agrees: [Int] = []
        for j in classes.indices {
            agrees.append(fr.assume(try Lowering.agreement(try fr.variable(ps[j], in: &t), try fr.variable(ps2[j], in: &t),
                                                           function: isFunctionClass(classes[j]), in: &t)))
        }
        let hc = fr.assume(try named(f.constant, C, ps, fr, &t)), hc2 = fr.assume(try named(f.constant, C2, ps2, fr, &t))
        var sub = Frame(fr.scope)
        let arity = isFunctionClass(f.type) ? 2 : 1
        let at = try (0..<arity).map { _ in sub.fix(.i) }.map { try sub.variable($0, in: &t) }
        let e = try eliminated(try graph(f.constant, C, ps, hc)(sub.scope, &t), at: at, in: &t)
        let e2 = try eliminated(try graph(f.constant, C2, ps2, hc2)(sub.scope, &t), at: at, in: &t)
        guard case let .folIff(_, phi)? = t.conclusion(of: e).map({ t[$0] }), case let .folIff(_, phi2)? = t.conclusion(of: e2).map({ t[$0] })
        else { throw GraphError.unexpected("a graph definition") }
        let walk = try Replacement(base: base) { _, l, r, s, t in
            guard l != r, case let .folPred(p, ls) = t[l], case let .folPred(p2, rs) = t[r], p == p2, ls.count == rs.count else { return nil }
            for j in classes.indices {
                let (P, P2) = (try s.variable(ps[j], in: &t), try s.variable(ps2[j], in: &t))
                guard let k = ls.indices.last, ls[k] == P, rs[k] == P2, ls.dropLast() == rs.dropLast() else { continue }
                let given = try s.hypothesis(agrees[j], in: &t)
                if p == .base("elem") || p == .base("pmem") { return try eliminated(given, at: Array(ls.dropLast()), in: &t) }
                if p == .base("apply") {
                    let lifted = try eliminated(try self.base.cite(.applyClassCong, in: &t), at: [P, P2], premises: [given], in: &t)
                    return try eliminated(lifted, at: Array(ls.dropLast()), in: &t)
                }
            }
            throw GraphError.unexpected("an atom differing at no class parameter")
        }.proof(phi, phi, phi2, in: sub.scope, &t)
        let toPhi2 = try base.applied(.iffTrans, [try premiseLeft(e, &t), phi, phi2], [e, walk], in: &t)
        return try fr.close(try sub.close(try iffThrough(toPhi2, e2, base, &t), in: &t), in: &t)
    }

    private func setExistence(_ c: Constant, _ t: inout Table) throws -> NodeID {
        guard case let .defined(d) = c else { throw GraphError.notMine(c.name) }
        let b = try definition(d).definiens
        var fr = Frame()
        let r = try Lowering.existence(of: b, in: &t)
        let (w, h) = try fr.open(try cited(r, try statement(r, in: &t), &t), in: &t)
        let y = try fr.variable(w, in: &t)
        let def = try eliminated(try definitionCited(c, &t), at: [y], in: &t)
        return try fr.close(try t.intern(.isaExIntro(try t.intern(.folIffElimR(def, try fr.hypothesis(h, in: &t))), y)), in: &t)
    }

    private func setUniqueness(_ c: Constant, _ t: inout Table) throws -> NodeID {
        guard case let .defined(d) = c else { throw GraphError.notMine(c.name) }
        let b = try definition(d).definiens
        var fr = Frame()
        let (v, w) = (fr.fix(.i), fr.fix(.i))
        let named = { (x: Int, f: Frame, t: inout Table) throws -> NodeID in
            try t.intern(.folPred(.constant(c), args: [try f.variable(x, in: &t)]))
        }
        let hv = fr.assume(try named(v, fr, &t)), hw = fr.assume(try named(w, fr, &t))
        let unfolded = { (x: Int, h: Int, f: inout Frame, t: inout Table) throws -> Fact in
            let def = try eliminated(try self.definitionCited(c, &t), at: [try f.variable(x, in: &t)], in: &t)
            return .hypothesis(try f.have(try t.intern(.folIffElimL(def, try f.hypothesis(h, in: &t))), in: &t))
        }
        let (mv, mw) = (try unfolded(v, hv, &fr, &t), try unfolded(w, hw, &fr, &t))
        let kind = Member.term { _, _, _ in b }
        let equal = try unique(kind, [], v, w, mv, mw, [:], &fr, &t)
        return try fr.close(equal, in: &t)
    }

    private func guardOf(_ x: NodeID, _ guards: [Int: Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        for (level, g) in guards where try f.variable(level, in: &t) == x { return try f.hypothesis(g, in: &t) }
        throw GraphError.unexpected("a function variable with no guard")
    }

    private func symmetric(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case let .folPred(.base("eq"), xs)? = t.conclusion(of: p).map({ t[$0] }) else { throw TableError.principalConnective(p) }
        return try eliminated(try base.cite(.eqSymm, in: &t), at: xs, premises: [p], in: &t)
    }

    private func premiseLeft(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case let .folIff(a, _)? = t.conclusion(of: p).map({ t[$0] }) else { throw TableError.principalConnective(p) }
        return a
    }

    private func graphBody(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case let .folIff(_, b)? = t.conclusion(of: p).map({ t[$0] }) else { throw TableError.principalConnective(p) }
        return b
    }
}
