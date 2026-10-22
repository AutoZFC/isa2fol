import IR

@frozen
public enum GraphError: Error, Equatable, Sendable {
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

    func definitionCited(_ c: Constant, _ t: inout Table) throws -> NodeID {
        switch c {
        case .primitive(.zf(.pow)): return try base.cite(.zfPowDef, in: &t)
        case .primitive(.zf(.union)): return try base.cite(.zfUnionDef, in: &t)
        case .primitive(.zf(.primReplace)): return try base.cite(.zfPrimReplaceDef, in: &t)
        case .defined(let d): return try t.intern(.use(.definition(d), [], try atDefinition(d, definitions, in: &t)))
        case .primitive(.zf(.mem)), .primitive(.zf(.zero)), .primitive(.zf(.inf)), .primitive(.pure), .primitive(.ifol):
            throw GraphError.noDefinition(c.name)
        }
    }

    func definition(_ d: Defined) throws -> Definition {
        guard let found = definitions.first(where: { $0.defines == .constant(d) })
        else { throw GraphError.noDefinition(d.name) }
        return found
    }

    func graph(_ c: Constant, _ C: Int, _ ps: [Int], _ hc: Int) -> (Scope, inout Table) throws -> NodeID {
        { s, t in
            let def = try eliminated(
                try definitionCited(c, &t),
                at: try ([C] + ps).map { try s.variable($0, in: &t) },
                in: &t,
            )
            return try t.intern(.folIffElimL(def, try s.hypothesis(hc, in: &t)))
        }
    }

    private func member(_ c: Constant, _ T: IRType, classes ps: [Int]) throws -> Member {
        switch c {
        case .primitive(.zf(.pow)): return .relation(ex: .powEX, uniq: .powUNIQ, cong: .powCONG)

        case .primitive(.zf(.union)): return .relation(ex: .unionEX, uniq: .unionUNIQ, cong: .unionCONG)

        case .primitive(.zf(.primReplace)): return .primReplace(ps[0])

        case .defined(let d):
            let definiens = try definition(d).definiens
            return .term { s, xs, t in
                var sets = xs[...]
                var classes = ps[...]
                let args = try T.domains.map { D -> NodeID in
                    isEntry(D) ? try atEntry(D, sets.removeFirst(), in: &t) : try s.variable(
                        classes.removeFirst(),
                        in: &t,
                    )
                }
                return try beta(definiens, args, in: &t)
            }

        case .primitive(.zf(.mem)), .primitive(.zf(.zero)), .primitive(.zf(.inf)), .primitive(.pure), .primitive(.ifol):
            throw GraphError.noDefinition(c.name)
        }
    }

    private func named(_ c: Constant, _ C: Int, _ ps: [Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        try t.intern(.folPred(.constant(c), args: try ([C] + ps).map { try f.variable($0, in: &t) }))
    }

    private func totality(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { !isEntry($0) }
        let m = f.type.domains.count - classes.count
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }
        var guards = [Int: Int]()
        for (j, D) in classes.enumerated() where isFunctionClass(D) {
            if let g = try guarded(try fr.variable(ps[j], in: &t), D, in: &t) { guards[ps[j]] = fr.assume(g) }
        }
        let C = fr.fix(nil)
        let hc = fr.assume(try named(f.constant, C, ps, fr, &t))
        let xs = (0..<m).map { _ in fr.fix(.i) }
        let tau = fr.fix(.i)
        let ht = fr.assume(try tuple(try xs.map { try fr.variable($0, in: &t) }, try fr.variable(tau, in: &t), in: &t))
        let kind = try member(f.constant, f.type, classes: ps)
        let valued = { (y: NodeID, value: NodeID, g: Frame, t: inout Table) throws -> NodeID in
            let gr = try eliminated(
                try graph(f.constant, C, ps, hc)(g.scope, &t),
                at: [try g.variable(tau, in: &t), y],
                in: &t,
            )
            let inside = try introduced(
                try sides(gr, t).right,
                at: try xs.map { try g.variable($0, in: &t) },
                from: try t.intern(.folAndIntro(try g.hypothesis(ht, in: &t), value)),
                in: &t,
            )
            return try t.intern(.folIffElimR(gr, inside))
        }
        let some = { (g: Frame, t: inout Table) throws -> NodeID in
            try someLeft(
                of: try eliminated(
                    try graph(f.constant, C, ps, hc)(g.scope, &t),
                    at: [try g.variable(tau, in: &t)],
                    in: &t,
                ),
                in: &t,
            )
        }
        let variableBody: NodeID? = try {
            guard case .term(let body) = kind else { return nil }
            let b = try body(fr.scope, try xs.map { try fr.variable($0, in: &t) }, &t)
            if case .isaBound = t[b] { return b }
            return nil
        }()
        if let x = variableBody {
            var z = Frame(fr.scope)
            let zl = z.fix(.i)
            let hz = z.assume(try t.intern(.folPred(
                .base("eq"),
                args: [try z.variable(zl, in: &t), try z.scope.lift(x, from: fr.scope.depth, in: &t)],
            )))
            let everyZ = try z.close(
                try valued(try z.variable(zl, in: &t), try z.hypothesis(hz, in: &t), z, &t),
                in: &t,
            )
            let reflexive = try eliminated(try base.cite(.eqRefl, in: &t), at: [x], in: &t)
            let atX = try t.intern(.folImpliesElim(try t.intern(.isaAllElim(everyZ, x)), reflexive))
            return try fr.close(try introduced(try some(fr, &t), at: [x], from: atX, in: &t), in: &t)
        }
        let (y, value) = try existence(kind, xs, guards, &fr, &t)
        return try fr.close(
            try introduced(try some(fr, &t), at: [y], from: try valued(y, value, fr, &t), in: &t),
            in: &t,
        )
    }

    private func existence(
        _ kind: Member,
        _ xs: [Int],
        _ guards: [Int: Int],
        _ fr: inout Frame,
        _ t: inout Table,
    ) throws -> (NodeID, NodeID) {
        switch kind {
        case .term(let body):
            let b = try body(fr.scope, try xs.map { try fr.variable($0, in: &t) }, &t)
            let r = try Lowering.existence(of: b, in: &t)
            let c = try closed(b, in: &t)
            let guardOf = guardsOf(guards, fr)
            let ex = try instantiated(
                try cited(r, try statement(r, in: &t), &t),
                at: c.variables,
                c.types,
                guards: true,
                guardOf: { x, _, t in try guardOf(x, &t) },
                in: &t,
            )
            let (w, h) = try fr.open(ex, in: &t)
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))

        case .relation(let ex, _, _):
            let (w, h) = try fr.open(
                try eliminated(try base.cite(ex, in: &t), at: [try fr.variable(xs[0], in: &t)], in: &t),
                in: &t,
            )
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))

        case .primReplace(let P):
            let at = [try fr.variable(P, in: &t), try fr.variable(xs[0], in: &t)]
            let (w, h) = try fr.open(try eliminated(try base.cite(.zfPrimReplaceValue, in: &t), at: at, in: &t), in: &t)
            return (try fr.variable(w, in: &t), try fr.hypothesis(h, in: &t))
        }
    }

    private func function(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { !isEntry($0) }
        let m = f.type.domains.count - classes.count
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }
        var guards = [Int: Int]()
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
        var guards = [Int: Int]()
        for T in f.types {
            let v = fr.fix(T)
            if T != .i, let g = try guarded(try fr.variable(v, in: &t), T, in: &t) { guards[v] = fr.assume(g) }
        }
        let outer = fr.scope.depth
        let K = fr.fix(nil)
        let lambda = try fr.scope.lift(f.lambda, from: outer, in: &t)
        let at = fr.scope.depth
        let hK = fr.assume(try classDefinition(lambda, K: try fr.variable(K, in: &t), in: &t))
        var m = 0
        var inner = lambda
        while case .isaAbs(_, let body) = t[inner] { (m, inner) = (m + 1, body) }
        let kind = Member.term { s, xs, t in try beta(try s.lift(lambda, from: at, in: &t), xs, in: &t) }
        return try fr.close(
            try singleValued({ s, t in try s.hypothesis(hK, in: &t) }, K, kind, arity: m, guards, fr, &t),
            in: &t,
        )
    }

    private func singleValued(
        _ graph: @escaping (Scope, inout Table) throws -> NodeID,
        _ K: Int,
        _ kind: Member,
        arity m: Int,
        _ guards: [Int: Int],
        _ outer: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var sub = Frame(outer.scope)
        let tt = sub.fix(.i)
        let r = sub.fix(.i)
        let s = sub.fix(.i)
        let value = { (v: Int, f: Frame, t: inout Table) throws -> NodeID in
            try t.intern(.folPred(
                .base("pmem"),
                args: [try f.variable(tt, in: &t), try f.variable(v, in: &t), try f.variable(K, in: &t)],
            ))
        }
        let hr = sub.assume(try value(r, sub, &t))
        let hs = sub.assume(try value(s, sub, &t))
        let open = { (v: Int, h: Int, f: inout Frame, t: inout Table) throws -> (witnesses: [Int], body: Fact) in
            let at = try eliminated(
                try graph(f.scope, &t),
                at: [try f.variable(tt, in: &t), try f.variable(v, in: &t)],
                in: &t,
            )
            let e = try t.intern(.folIffElimL(at, try f.hypothesis(h, in: &t)))
            if m == 0 { return ([], .hypothesis(try f.have(e, in: &t))) }
            return try f.open(e, count: m, in: &t)
        }
        let (xs, conj) = try open(r, hr, &sub, &t)
        let (xs2, conj2) = try open(s, hs, &sub, &t)
        var moved = Fact.right(conj2)
        if m > 0 {
            let f = TupleFact(arity: m, fact: .injectivity)
            let inj = try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try (xs + xs2 + [tt]).map { try sub.variable($0, in: &t) },
                premises: [try sub.proof(.left(conj), in: &t), try sub.proof(.left(conj2), in: &t)],
                in: &t,
            )
            let equal = try sub.have(inj, in: &t)
            let projection = { (j: Int) -> Fact in
                var fact = Fact.hypothesis(equal)
                for _ in 0..<j { fact = .right(fact) }
                return j < m - 1 ? .left(fact) : fact
            }
            moved = .hypothesis(try sub.have(
                try transport(kind, from: xs2, to: xs, projection, value: s, at: tt, moved, graph, sub, &t),
                in: &t,
            ))
        }
        let eq = try unique(kind, xs, r, s, .right(conj), moved, guards, &sub, &t)
        let rhs = try sub.close(eq, in: &t)
        let def = try eliminated(try base.cite(.functionDef, in: &t), at: [try outer.variable(K, in: &t)], in: &t)
        return try t.intern(.folIffElimR(def, rhs))
    }

    private func transport(
        _ kind: Member,
        from xs2: [Int],
        to xs: [Int],
        _ projection: @escaping (Int) -> Fact,
        value s: Int,
        at tt: Int,
        _ given: Fact,
        _ graph: (Scope, inout Table) throws -> NodeID,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let source = try f.proof(given, in: &t)
        switch kind {
        case .relation(_, _, let cong):
            let eq = try symmetric(try f.proof(projection(0), in: &t), &t)
            return try eliminated(
                try base.cite(cong, in: &t),
                at: [
                    try f.variable(xs2[0], in: &t),
                    try f.variable(xs[0], in: &t),
                    try f.variable(s, in: &t),
                ],
                premises: [eq, source],
                in: &t,
            )

        case .term, .primReplace:
            var rhs = try graphBody(
                try eliminated(
                    try graph(f.scope, &t),
                    at: [try f.variable(tt, in: &t), try f.variable(s, in: &t)],
                    in: &t,
                ),
                &t,
            )
            for x in xs {
                guard case .ifolEx(.i, let body) = t[rhs]
                else { throw GraphError.unexpected("a graph definition's entries") }
                rhs = try instantiate(body, with: try f.variable(x, in: &t), in: &t)
            }
            guard case .folAnd(_, let to) = t[rhs] else { throw GraphError.unexpected("a graph definition's member") }
            guard let from = t.conclusion(of: source) else { throw TableError.expectedStep(source) }
            return try Carry { p, target, s, t in
                guard let have = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
                let moved = try congruent(have, target, base, { a, b, t in
                    for j in xs.indices {
                        let x2 = try s.variable(xs2[j], in: &t)
                        let x = try s.variable(xs[j], in: &t)
                        if x2 == a, x == b { return try symmetric(try s.proof(projection(j), in: &t), &t) }
                        if x == a, x2 == b { return try s.proof(projection(j), in: &t) }
                    }
                    throw GraphError.unexpected("an atom moved at no entry")
                }, &t)
                return try t.intern(.folIffElimL(moved, p))
            }.proof(source, from: from, to: to, in: f.scope, &t)
        }
    }

    private func unique(
        _ kind: Member,
        _ xs: [Int],
        _ r: Int,
        _ s: Int,
        _ mr: Fact,
        _ ms: Fact,
        _ guards: [Int: Int],
        _ f: inout Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        switch kind {
        case .term(let body):
            let b = try body(f.scope, try xs.map { try f.variable($0, in: &t) }, &t)
            let depth = f.scope.depth
            if case .isaBound = t[b] {
                return try eliminated(
                    try base.cite(.eqTrans, in: &t),
                    at: [try f.variable(r, in: &t), b, try f.variable(s, in: &t)],
                    premises: [try f.proof(mr, in: &t), try symmetric(try f.proof(ms, in: &t), &t)],
                    in: &t,
                )
            }
            var naming = Naming()
            let top = try naming.name(b, &t)
            let constraints = try naming.chain.stated()
            var witnesses = [Int]()
            var hypotheses = [Int]()
            let terms = TermProofs(base: base)
            for (j, piece) in naming.pieces.enumerated() {
                let at = Refs(outer: depth, witnesses: witnesses, frame: f)
                let guardOf = guardsOf(guards, f)
                let (w, h) = try f.open(try terms.witness(piece, at, hypotheses, naming.pieces, guardOf, &t), in: &t)
                let assumed = try f.hypothesis(h, in: &t)
                guard t.conclusion(of: assumed) == constraints[j]
                else { throw GraphError.unexpected("a piece's constraint") }
                witnesses.append(w)
                hypotheses.append(h)
            }
            let value = try Refs(outer: depth, witnesses: witnesses, frame: f).node(top, &t)
            let opened = f
            let atPieces = { (m: Fact, t: inout Table) throws -> NodeID in
                var p = try opened.proof(m, in: &t)
                for (w, h) in zip(witnesses, hypotheses) {
                    p = try eliminated(
                        p,
                        at: [try opened.variable(w, in: &t)],
                        premises: [try opened.hypothesis(h, in: &t)],
                        in: &t,
                    )
                }
                return p
            }
            return try eliminated(
                try base.cite(.eqTrans, in: &t),
                at: [try f.variable(r, in: &t), value, try f.variable(s, in: &t)],
                premises: [try atPieces(mr, &t), try symmetric(try atPieces(ms, &t), &t)],
                in: &t,
            )

        case .relation(_, let uniq, _):
            return try eliminated(
                try base.cite(uniq, in: &t),
                at: [try f.variable(xs[0], in: &t), try f.variable(r, in: &t), try f.variable(s, in: &t)],
                premises: [try f.proof(mr, in: &t), try f.proof(ms, in: &t)],
                in: &t,
            )

        case .primReplace:
            return try replacedUnique(try f.variable(r, in: &t), try f.variable(s, in: &t), mr, ms, f, &t)
        }
    }

    private func replacedUnique(
        _ r: NodeID,
        _ s: NodeID,
        _ mr: Fact,
        _ ms: Fact,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let goal = try t.intern(.folPred(.base("eq"), args: [r, s]))
        let pr = try f.proof(mr, in: &t)
        let ps = try f.proof(ms, in: &t)
        guard
            case .folOr(let rl, let rr)? = t.conclusion(of: pr).map({ t[$0] }),
            case .folOr(let sl, let sr)? = t.conclusion(of: ps).map({ t[$0] })
        else {
            throw GraphError.unexpected("PrimReplace's two branches")
        }
        let branch = { (
            a: NodeID,
            body: (Frame, Int, inout Table) throws -> NodeID,
            f: Frame,
            t: inout Table,
        ) throws -> NodeID in
            var g = Frame(f.scope)
            let h = g.assume(a)
            return try g.close(try body(g, h, &t), in: &t)
        }
        let absurd = { (no: Fact, yes: Fact, g: Frame, t: inout Table) throws -> NodeID in
            let bottom = try t.intern(.folNotElim(try g.proof(no, in: &t), try g.proof(yes, in: &t)))
            return try t.intern(.folBottomElim(bottom, try g.scope.lift(goal, from: f.scope.depth, in: &t)))
        }
        let whenMatrix = try branch(rl, { g, h1, t in
            let both = try branch(
                sl,
                { g2, h2, t in
                    try extensional(r, s, .right(.hypothesis(h1)), .right(.hypothesis(h2)), g2, from: f, &t) },
                g,
                &t,
            )
            let mixed = try branch(
                sr,
                { g2, h2, t in try absurd(.left(.hypothesis(h2)), .left(.hypothesis(h1)), g2, &t) },
                g,
                &t,
            )
            return try t.intern(.folOrElim(try g.proof(ms, in: &t), both, mixed))
        }, f, &t)
        let whenEmpty = try branch(rr, { g, h1, t in
            let mixed = try branch(
                sl,
                { g2, h2, t in try absurd(.left(.hypothesis(h1)), .left(.hypothesis(h2)), g2, &t) },
                g,
                &t,
            )
            let both = try branch(sr, { g2, h2, t in
                try eliminated(
                    try base.cite(.zeroUNIQ, in: &t),
                    at: [
                        try g2.scope.lift(r, from: f.scope.depth, in: &t),
                        try g2.scope.lift(
                            s,
                            from: f.scope.depth,
                            in: &t,
                        ),
                    ],
                    premises: [
                        try g2.proof(.right(.hypothesis(h1)), in: &t),
                        try g2.proof(.right(.hypothesis(h2)), in: &t),
                    ],
                    in: &t,
                )
            }, g, &t)
            return try t.intern(.folOrElim(try g.proof(ms, in: &t), mixed, both))
        }, f, &t)
        return try t.intern(.folOrElim(try f.proof(mr, in: &t), whenMatrix, whenEmpty))
    }

    private func extensional(
        _ r: NodeID,
        _ s: NodeID,
        _ mr: Fact,
        _ ms: Fact,
        _ g: Frame,
        from f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var each = Frame(g.scope)
        let vl = each.fix(.i)
        let v = try each.variable(vl, in: &t)
        let agree = try iffThrough(
            try eliminated(try each.proof(mr, in: &t), at: [v], in: &t),
            try eliminated(try each.proof(ms, in: &t), at: [v], in: &t),
            base,
            &t,
        )
        let everywhere = try each.close(agree, in: &t)
        let rg = try g.scope.lift(r, from: f.scope.depth, in: &t)
        let sg = try g.scope.lift(s, from: f.scope.depth, in: &t)
        return try t.intern(.folIffElimR(
            try eliminated(try base.cite(.extensionality, in: &t), at: [rg, sg], in: &t),
            everywhere,
        ))
    }

    private func agreement(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { !isEntry($0) }
        var fr = Frame()
        let ps = classes.map { fr.fix($0) }
        let ps2 = classes.map { fr.fix($0) }
        let C = fr.fix(nil)
        let C2 = fr.fix(nil)
        var agrees = [Int]()
        for j in classes.indices {
            agrees.append(fr.assume(try Lowering.agreement(
                try fr.variable(ps[j], in: &t),
                try fr.variable(ps2[j], in: &t),
                function: isFunctionClass(classes[j]),
                in: &t,
            )))
        }
        let hc = fr.assume(try named(f.constant, C, ps, fr, &t))
        let hc2 = fr.assume(try named(f.constant, C2, ps2, fr, &t))
        var sub = Frame(fr.scope)
        let arity = isFunctionClass(f.type) ? 2 : 1
        let at = try (0..<arity).map { _ in sub.fix(.i) }.map { try sub.variable($0, in: &t) }
        let e = try eliminated(try graph(f.constant, C, ps, hc)(sub.scope, &t), at: at, in: &t)
        let e2 = try eliminated(try graph(f.constant, C2, ps2, hc2)(sub.scope, &t), at: at, in: &t)
        guard
            case .folIff(_, let phi)? = t.conclusion(of: e).map({ t[$0] }),
            case .folIff(_, let phi2)? = t.conclusion(of: e2).map({ t[$0] })
        else { throw GraphError.unexpected("a graph definition") }
        let agreeing = Carry { p, target, s, t in
            guard
                let have = t.conclusion(of: p), case .folPred(let q, let ls) = t[have],
                case .folPred(let q2, let rs) = t[target], q == q2, ls.count == rs.count, let k = ls.indices.last,
                ls.dropLast() == rs.dropLast()
            else { throw GraphError.unexpected("an atom differing at no class parameter") }
            for j in classes.indices {
                let P = try s.variable(ps[j], in: &t)
                let P2 = try s.variable(ps2[j], in: &t)
                let forward = ls[k] == P && rs[k] == P2
                guard forward || ls[k] == P2 && rs[k] == P else { continue }
                var given = try s.hypothesis(agrees[j], in: &t)
                if q == .base("apply") {
                    given = try eliminated(
                        try base.cite(.applyClassCong, in: &t),
                        at: [P, P2],
                        premises: [given],
                        in: &t,
                    )
                } else if q != .base("elem"), q != .base("pmem") {
                    continue
                }
                let iff = try eliminated(given, at: Array(ls.dropLast()), in: &t)
                return try t.intern(forward ? .folIffElimL(iff, p) : .folIffElimR(iff, p))
            }
            throw GraphError.unexpected("an atom differing at no class parameter")
        }
        let leftC = try premiseLeft(e, &t)
        let leftC2 = try premiseLeft(e2, &t)
        let way = { (from: NodeID, out: NodeID, back: NodeID, source: NodeID, target: NodeID, t: inout Table) throws
            -> NodeID in
            var g = Frame(sub.scope)
            let h = g.assume(from)
            let inner = try t.intern(.folIffElimL(
                try lifted(out, from: sub.scope, to: g.scope, in: &t),
                try g.hypothesis(h, in: &t),
            ))
            let carried = try agreeing.proof(inner, from: source, to: target, in: g.scope, &t)
            return try g.close(
                try t.intern(.folIffElimR(try lifted(back, from: sub.scope, to: g.scope, in: &t), carried)),
                in: &t,
            )
        }
        let there = try way(leftC, e, e2, phi, phi2, &t)
        let back = try way(leftC2, e2, e, phi2, phi, &t)
        return try fr.close(try sub.close(try t.intern(.folIffIntro(there, back)), in: &t), in: &t)
    }

    private func setExistence(_ c: Constant, _ t: inout Table) throws -> NodeID {
        guard case .defined(let d) = c else { throw GraphError.notMine(c.name) }
        let b = try definition(d).definiens
        var fr = Frame()
        let r = try Lowering.existence(of: b, in: &t)
        let (w, h) = try fr.open(try cited(r, try statement(r, in: &t), &t), in: &t)
        let y = try fr.variable(w, in: &t)
        let def = try eliminated(try definitionCited(c, &t), at: [y], in: &t)
        return try fr.close(
            try introduced(
                try statement(ConstantFact(constant: c, type: .i, fact: .existence), in: &t),
                at: [y],
                from: try t.intern(.folIffElimR(def, try fr.hypothesis(h, in: &t))),
                in: &t,
            ),
            in: &t,
        )
    }

    private func setUniqueness(_ c: Constant, _ t: inout Table) throws -> NodeID {
        guard case .defined(let d) = c else { throw GraphError.notMine(c.name) }
        let b = try definition(d).definiens
        var fr = Frame()
        let v = fr.fix(.i)
        let w = fr.fix(.i)
        let named = { (x: Int, f: Frame, t: inout Table) throws -> NodeID in
            try t.intern(.folPred(.constant(c), args: [try f.variable(x, in: &t)]))
        }
        let hv = fr.assume(try named(v, fr, &t))
        let hw = fr.assume(try named(w, fr, &t))
        let unfolded = { (x: Int, h: Int, f: inout Frame, t: inout Table) throws -> Fact in
            let def = try eliminated(try definitionCited(c, &t), at: [try f.variable(x, in: &t)], in: &t)
            return .hypothesis(try f.have(try t.intern(.folIffElimL(def, try f.hypothesis(h, in: &t))), in: &t))
        }
        let mv = try unfolded(v, hv, &fr, &t)
        let mw = try unfolded(w, hw, &fr, &t)
        let kind = Member.term { _, _, _ in b }
        let equal = try unique(kind, [], v, w, mv, mw, [:], &fr, &t)
        return try fr.close(equal, in: &t)
    }

    private func guardOf(_ x: NodeID, _ guards: [Int: Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        for (level, g) in guards where try f.variable(level, in: &t) == x { return try f.hypothesis(g, in: &t) }
        throw GraphError.unexpected("a function variable with no guard")
    }

    private func symmetric(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case .folPred(.base("eq"), let xs)? = t.conclusion(of: p).map({ t[$0] })
        else { throw TableError.principalConnective(p) }
        return try eliminated(try base.cite(.eqSymm, in: &t), at: xs, premises: [p], in: &t)
    }

    private func premiseLeft(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case .folIff(let a, _)? = t.conclusion(of: p).map({ t[$0] })
        else { throw TableError.principalConnective(p) }
        return a
    }

    private func graphBody(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case .folIff(_, let b)? = t.conclusion(of: p).map({ t[$0] })
        else { throw TableError.principalConnective(p) }
        return b
    }
}

/// From `p`, proving `from`, a proof of `to`: two formulas alike but at their atoms, each atom carried by `atom` — one
/// walk in one direction, each connective by its own introduction and elimination, no subformula restated.
struct Carry {
    let atom: (NodeID, NodeID, Scope, inout Table) throws -> NodeID

    func proof(_ p: NodeID, from a: NodeID, to b: NodeID, in s: Scope, _ t: inout Table) throws -> NodeID {
        if a == b { return p }
        let up = { (q: NodeID, g: Frame, t: inout Table) throws -> NodeID in
            try lifted(q, from: s, to: g.scope, in: &t)
        }
        switch (t[a], t[b]) {
        case (.folAnd(let a1, let a2), .folAnd(let b1, let b2)):
            return try t.intern(.folAndIntro(
                try proof(try t.intern(.folAndElimL(p)), from: a1, to: b1, in: s, &t),
                try proof(try t.intern(.folAndElimR(p)), from: a2, to: b2, in: s, &t),
            ))

        case (.folOr(let a1, let a2), .folOr(let b1, let b2)):
            var g1 = Frame(s)
            let h1 = g1.assume(a1)
            let left = try g1.close(try t.intern(.folOrIntroL(
                try proof(try g1.hypothesis(h1, in: &t), from: a1, to: b1, in: g1.scope, &t),
                b2,
            )), in: &t)
            var g2 = Frame(s)
            let h2 = g2.assume(a2)
            let right = try g2.close(try t.intern(.folOrIntroR(
                b1,
                try proof(try g2.hypothesis(h2, in: &t), from: a2, to: b2, in: g2.scope, &t),
            )), in: &t)
            return try t.intern(.folOrElim(p, left, right))

        case (.folImplies(let a1, let a2), .folImplies(let b1, let b2)):
            var g = Frame(s)
            let h = g.assume(b1)
            let back = try proof(try g.hypothesis(h, in: &t), from: b1, to: a1, in: g.scope, &t)
            let applied = try t.intern(.folImpliesElim(try up(p, g, &t), back))
            return try g.close(try proof(applied, from: a2, to: b2, in: g.scope, &t), in: &t)

        case (.folNot(let a1), .folNot(let b1)):
            var g = Frame(s)
            let h = g.assume(b1)
            let back = try proof(try g.hypothesis(h, in: &t), from: b1, to: a1, in: g.scope, &t)
            return try t.intern(.folNotIntro(b1, body: try t.intern(.folNotElim(try up(p, g, &t), back))))

        case (.folIff(let a1, let a2), .folIff(let b1, let b2)):
            let one = { (x: NodeID, y: NodeID, x2: NodeID, y2: NodeID, left: Bool, t: inout Table) throws -> NodeID in
                var g = Frame(s)
                let h = g.assume(x2)
                let back = try proof(try g.hypothesis(h, in: &t), from: x2, to: x, in: g.scope, &t)
                let lifted = try up(p, g, &t)
                let q = try t.intern(left ? .folIffElimL(lifted, back) : .folIffElimR(lifted, back))
                return try g.close(try proof(q, from: y, to: y2, in: g.scope, &t), in: &t)
            }
            return try t.intern(.folIffIntro(
                try one(a1, a2, b1, b2, true, &t),
                try one(a2, a1, b2, b1, false, &t),
            ))

        case (.ifolAll(.i, let a1), .ifolAll(.i, let b1)):
            var g = Frame(s)
            let x = g.fix(.i)
            let at = try t.intern(.isaAllElim(try up(p, g, &t), try g.variable(x, in: &t)))
            return try g.close(try proof(at, from: a1, to: b1, in: g.scope, &t), in: &t)

        case (.folForall(let a1), .folForall(let b1)):
            var g = Frame(s)
            let x = g.fix(nil)
            let at = try t.intern(.folForallElim(try up(p, g, &t), try g.variable(x, in: &t)))
            return try g.close(try proof(at, from: a1, to: b1, in: g.scope, &t), in: &t)

        case (.ifolEx(.i, let a1), .ifolEx(.i, _)):
            var g = Frame(s)
            let (w, h) = try g.open(p, in: &t)
            let q = try proof(
                try g.hypothesis(h, in: &t),
                from: try body(a, s, g, &t),
                to: try body(b, s, g, &t),
                in: g.scope,
                &t,
            )
            let shape = try body(b, s, g, &t, under: true)
            return try g.close(try t.intern(.isaExIntro(q, try g.variable(w, in: &t), body: shape)), in: &t)

        case (.folExists(let a1), .folExists(_)):
            var g = Frame(s)
            let (w, h) = try g.open(p, in: &t)
            let q = try proof(
                try g.hypothesis(h, in: &t),
                from: try body(a, s, g, &t),
                to: try body(b, s, g, &t),
                in: g.scope,
                &t,
            )
            return try g.close(try t.intern(.folExistsIntro(q, try g.variable(w, in: &t))), in: &t)

        case (.folPred, .folPred):
            return try atom(p, b, s, &t)

        default:
            throw GraphError.unexpected("two formulas apart beyond their atoms")
        }
    }

    /// The body of `b`, an existential at `s`, at `g`'s scope: its own variable `g`'s last, or kept bound (`under`).
    private func body(_ b: NodeID, _ s: Scope, _ g: Frame, _ t: inout Table, under: Bool = false) throws -> NodeID {
        let lifted = try lifted(b, from: s, to: g.scope, in: &t)
        let inner: NodeID
        switch t[lifted] {
        case .ifolEx(.i, let x), .folExists(let x): inner = x
        default: throw GraphError.unexpected("an existential")
        }
        if under { return inner }
        return try instantiate(inner, with: try g.variable(g.scope.depth - 1, in: &t), in: &t)
    }
}

/// The guard hypotheses `guards` of a frame's variables, keyed by level, as `f` holds them.
private func guardsOf(_ guards: [Int: Int], _ f: Frame) -> (NodeID, inout Table) throws -> NodeID {
    { x, t in
        for (level, h) in guards where try f.variable(level, in: &t) == x { return try f.hypothesis(h, in: &t) }
        throw GraphError.unexpected("the guard of \(x)")
    }
}
