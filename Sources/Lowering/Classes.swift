import IR

@frozen
public enum ClassError: Error, Equatable, Sendable {
    case notMine(String)
    case misproved(String)
    case noDefinition(String)
    case unexpected(String)
}

public struct ClassProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "class"

    public func owns(_ l: Lemma) -> Owned? {
        switch l.request {
        case let f as ConstantFact:
            guard f.fact == .classExists || f.fact == .lift else { return nil }
            switch f.constant {
            case .defined, .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)): return .rule
            case .primitive(.zf(.zero)), .primitive(.zf(.inf)): return f.fact == .classExists ? .rule : nil
            case .primitive, .declared: return .unbuilt
            }

        case let f as LambdaFact:
            guard f.fact == .classExists else { return nil }
            return f.types.contains(.o) ? .unbuilt : .rule

        case is RekeyFact:
            return .rule

        default:
            return nil
        }
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        in t: inout Table,
    ) throws -> NodeID {
        let proofs = ClassProofs(base: base, definitions: definitions)
        let proof: NodeID
        switch l.request {
        case let f as ConstantFact where f.fact == .lift: proof = try proofs.lift(f, &t)

        case let f as ConstantFact: proof = f.type == .i ? try proofs.singleton(f.constant, &t) : try proofs.constant(
                f,
                &t,
            )

        case let f as LambdaFact: proof = try proofs.lambda(f, &t)

        case let f as RekeyFact: proof = try proofs.rekey(f.width, &t)

        default: throw ClassError.notMine(l.name)
        }
        guard t.conclusion(of: proof) == statement else { throw ClassError.misproved(l.name) }
        return proof
    }

    public func defines(_: Defined) -> Owned? {
        nil
    }

    public func define(_ c: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        throw ClassError.notMine(c.name)
    }

    let base: Base

}

struct ClassProofs {
    let base: Base
    let definitions: [Definition]

    func lambda(_ f: LambdaFact, _ t: inout Table) throws -> NodeID {
        var top = Frame()
        var roles = [Role]()
        var values = [Int]()
        for T in f.types {
            let v = top.fix(T)
            roles.append(T == .i ? .entry(values.count) : .fixed(v))
            if T == .i { values.append(v) }
        }
        let depth = top.scope.depth
        let raw = try classBody(f.lambda, raw: true, in: &t)
        let named = try classBody(f.lambda, raw: false, in: &t)
        var g = try Comprehension(base: base, top: top, in: &t)
        let c = try g.context(values, &t)
        let exists = try g.section(
            raw: raw.body,
            named: named.body,
            outside: named.outside,
            roles: roles,
            depth: depth,
            context: c,
            &t,
        )
        return try g.top.close(exists, in: &t)
    }

    func constant(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        var top = Frame()
        let classes = f.type.domains.filter { $0 != .i }
        let ps = classes.map { top.fix($0) }
        let depth = top.scope.depth
        let src = try source(f.constant, f.type, &t)
        var g = try Comprehension(base: base, top: top, in: &t)
        let exists = try g.section(
            raw: src.raw,
            named: src.named,
            outside: src.outside,
            roles: ps.map { .fixed($0) },
            depth: depth,
            context: g.empty,
            &t,
        )
        let (K, hK) = try g.top.open(exists, in: &t)
        let k = try g.top.variable(K, in: &t)
        let at = try eliminated(src.definition, at: [k] + (try ps.map { try g.top.variable($0, in: &t) }), in: &t)
        let defines = try t.intern(.folIffElimR(at, try g.top.hypothesis(hK, in: &t)))
        return try g.top.close(try t.intern(.folExistsIntro(defines, k)), in: &t)
    }

    func lift(_ f: ConstantFact, _ t: inout Table) throws -> NodeID {
        let classes = f.type.domains.filter { $0 != .i }
        let outside = isFunctionClass(f.type) ? 2 : 1
        let k = 3 + outside
        let src = try source(f.constant, f.type, &t)
        var top = Frame()
        let p = top.fix(.i)
        let p1 = top.fix(.i)
        let hn = top.assume(try pred("nsucc", [p, p1], at: top.scope, &t))
        let As = classes.map { _ in top.fix(nil) }
        var g = try Comprehension(base: base, top: top, in: &t)
        _ = try g.numeral(k, &t)
        let sections = classes.indices.map { g.classParameter(
            As[$0],
            function: isFunctionClass(classes[$0]),
            record: 2,
            index: 0,
            next: 1,
        ) }
        let W = try g.build(src.raw, sections.map { .section($0) } + (0..<outside).map { .entry(3 + $0) }, k, &t)
        let rekey = RekeyFact(width: outside)
        let at = try eliminated(
            try cited(rekey, try statement(rekey, in: &t), &t),
            at: [try g.top.variable(p, in: &t), try g.top.variable(p1, in: &t)],
            premises: [try g.top.hypothesis(hn, in: &t)],
            in: &t,
        )
        let (U, hU) = try g.top.open(try eliminated(at, at: [try g.top.variable(W.cls, in: &t)], in: &t), in: &t)
        let reading = g.reading
        var M = Frame(g.top.scope)
        let a = M.fix(.i)
        let ht = M.assume(try pred("tuple", [a, p], at: M.scope, &t))
        let Ks = classes.map { M.fix($0) }
        var env = Env()
        for j in classes.indices {
            let section = try approximation(
                Ks[j],
                As[j],
                record: a,
                p,
                p1,
                function: isFunctionClass(classes[j]),
                in: M.scope,
                &t,
            )
            env.sections[sections[j]] = M.assume(section)
        }
        let C = M.fix(nil)
        let hc = M.assume(try t.intern(.folPred(
            .constant(f.constant),
            args: try ([C] + Ks).map { try M.variable($0, in: &t) },
        )))
        var E = Frame(M.scope)
        let values = (0..<outside).map { _ in E.fix(.i) }
        let rho = try reading.record([p, p1, a] + values, in: &E, &t)
        let def = try eliminated(src.definition, at: try ([C] + Ks).map { try E.variable($0, in: &t) }, in: &t)
        let graph = try eliminated(
            try t.intern(.folIffElimL(def, try E.hypothesis(hc, in: &t))),
            at: try values.map { try E.variable($0, in: &t) },
            in: &t,
        )
        let exact = try reading.read(try sides(graph, t).right, W, E, rho, env, &t)
        let keyed = try records(rho, W.cls, reading, E, &t)
        let moved = try rekeyed(hU, a, ht, values, U, p, p1, E, &t)
        let back = try base.applied(.iffSymm, [try sides(exact, t).left, try sides(exact, t).right], [exact], in: &t)
        let proof = try chained(try chained(try chained(graph, back, &t), keyed, &t), moved, &t)
        let body = try M.close(try E.close(proof, in: &t), in: &t)
        return try g.top.close(try t.intern(.folExistsIntro(body, try g.top.variable(U, in: &t))), in: &t)
    }

    func rekey(_ m: Int, _ t: inout Table) throws -> NodeID {
        var top = Frame()
        let p = top.fix(.i)
        let p1 = top.fix(.i)
        let hn = top.assume(try pred("nsucc", [p, p1], at: top.scope, &t))
        let W = top.fix(nil)
        let (T, hT) = try top.open(
            try eliminated(try base.cite(.tuplesClass, in: &t), at: [try top.variable(p, in: &t)], in: &t),
            in: &t,
        )
        let depth = top.scope.depth
        var s = top.scope
        let x = s.fix(.i)
        var q = s
        let a = q.fix(.i)
        let vs = (0..<m).map { _ in q.fix(.i) }
        let mid = m == 2 ? [q.fix(.i)] : []
        let rho = q.fix(.i)
        let binders = 2 + m + mid.count
        var conj = try t.intern(.folAnd(
            try tuple(try ([p, p1, a] + vs).map { try q.variable($0, in: &t) }, try q.variable(rho, in: &t), in: &t),
            try pred("elem", [rho, W], at: q, &t),
        ))
        if m == 2 {
            conj = try t.intern(.folAnd(try pred("snoc", [mid[0], p1, vs[1], x], at: q, &t), conj))
            conj = try t.intern(.folAnd(try pred("snoc", [a, p, vs[0], mid[0]], at: q, &t), conj))
        } else {
            conj = try t.intern(.folAnd(try pred("snoc", [a, p, vs[0], x], at: q, &t), conj))
        }
        var Q = try t.intern(.folAnd(try pred("elem", [a, T], at: q, &t), conj))
        for _ in 0..<binders { Q = try t.intern(.ifolEx(.i, body: Q)) }
        var g = try Comprehension(base: base, top: top, in: &t)
        let c = try g.context([p, p1], &t)
        let ex = try g.section(
            raw: Q,
            named: Q,
            outside: 1,
            roles: [.entry(0), .entry(1), .fixed(W), .fixed(T)],
            depth: depth,
            context: c,
            &t,
        )
        let (U, hU) = try g.top.open(ex, in: &t)
        var M = Frame(g.top.scope)
        let a0 = M.fix(.i)
        let ht = M.assume(try pred("tuple", [a0, p], at: M.scope, &t))
        let values = (0..<m).map { _ in M.fix(.i) }
        let records = (0..<m).map { _ in M.fix(.i) }
        var snocs = [Int]()
        for j in 0..<m { snocs.append(M.assume(try pred(
            "snoc",
            [j == 0 ? a0 : records[j - 1], j == 0 ? p : p1, values[j], records[j]],
            at: M.scope,
            &t,
        ))) }
        let last = records[m - 1]
        let atLast = { (f: Frame, t: inout Table) throws -> NodeID in
            try t.intern(.isaAllElim(try f.hypothesis(hU, in: &t), try f.variable(last, in: &t)))
        }
        var back = Frame(M.scope)
        var inside = back.scope
        let r0 = inside.fix(.i)
        let entries = try ([p, p1, a0] + values).map { try inside.variable($0, in: &t) }
        let y = try t.intern(.ifolEx(
            .i,
            body: try t.intern(.folAnd(
                try tuple(entries, try inside.variable(r0, in: &t), in: &t),
                try pred("elem", [r0, W], at: inside, &t),
            )),
        ))
        let hy = back.assume(y)
        let (rw, hr) = try back.open(try back.hypothesis(hy, in: &t), in: &t)
        let inT = try t.intern(.folIffElimR(
            try t.intern(.isaAllElim(try back.hypothesis(hT, in: &t), try back.variable(a0, in: &t))),
            try back.hypothesis(ht, in: &t),
        ))
        var both = try back.hypothesis(hr, in: &t)
        for s in snocs.reversed() { both = try t.intern(.folAndIntro(try back.hypothesis(s, in: &t), both)) }
        let atBack = try atLast(back, &t)
        let witnessed = try introduced(
            try sides(atBack, t).right,
            at: try ([a0] + values + (m == 2 ? [records[0]] : []) + [rw]).map { try back.variable($0, in: &t) },
            from: try t.intern(.folAndIntro(inT, both)),
            in: &t,
        )
        let backward = try back.close(try t.intern(.folIffElimR(atBack, witnessed)), in: &t)
        var there = Frame(M.scope)
        let hm = there.assume(try pred("elem", [last, U], at: there.scope, &t))
        let (ws, body) = try there.open(
            try t.intern(.folIffElimL(try atLast(there, &t), try there.hypothesis(hm, in: &t))),
            count: binders,
            in: &t,
        )
        let part = { (j: Int, last: Bool) -> Fact in
            var fact = body
            for _ in 0..<j { fact = .right(fact) }
            return last ? fact : .left(fact)
        }
        let a2 = ws[0]
        let v2 = Array(ws[1...m])
        let rho2 = ws[binders - 1]
        let inA2 = try eliminated(try there.hypothesis(hT, in: &t), at: [try there.variable(a2, in: &t)], in: &t)
        let a2Tuple = try there.have(try t.intern(.folIffElimL(inA2, try there.proof(part(0, false), in: &t))), in: &t)
        let inj = { (
            s: Int,
            s2: Int,
            n: Int,
            v: Int,
            w: Int,
            b: Int,
            ts: Int,
            ts2: Int,
            sn: NodeID,
            sn2: NodeID,
            f: Frame,
            t: inout Table,
        ) throws -> NodeID in
            try eliminated(
                try base.cite(.snocInj, in: &t),
                at: try [s, s2, n, v, w, b].map { try f.variable($0, in: &t) },
                premises: [try f.hypothesis(ts, in: &t), try f.hypothesis(ts2, in: &t), sn, sn2],
                in: &t,
            )
        }
        let symmetric = { (p: NodeID, t: inout Table) throws -> NodeID in
            guard case .folPred(_, let xs)? = t.conclusion(of: p).map({ t[$0] })
            else { throw TableError.principalConnective(p) }
            return try eliminated(try base.cite(.eqSymm, in: &t), at: xs, premises: [p], in: &t)
        }
        var equal = [(from: Int, to: Int, proof: Int)]()
        if m == 1 {
            let pair = try inj(
                a0,
                a2,
                p,
                values[0],
                v2[0],
                last,
                ht,
                a2Tuple,
                try there.hypothesis(snocs[0], in: &t),
                try there.proof(part(1, false), in: &t),
                there,
                &t,
            )
            let hPair = try there.have(pair, in: &t)
            equal.append((
                a2,
                a0,
                try there.have(
                    try symmetric(try t.intern(.folAndElimL(try there.hypothesis(hPair, in: &t))), &t),
                    in: &t,
                ),
            ))
            equal.append((
                v2[0],
                values[0],
                try there.have(
                    try symmetric(try t.intern(.folAndElimR(try there.hypothesis(hPair, in: &t))), &t),
                    in: &t,
                ),
            ))
        } else {
            let b2 = ws[m + 1]
            let snoced = { (s: Int, b: Int, v: Int, ts: Int, sn: NodeID, f: Frame, t: inout Table) throws -> NodeID in
                try eliminated(
                    try base.cite(.tupleSnoc, in: &t),
                    at: try [s, b, p, v, p1].map { try f.variable($0, in: &t) },
                    premises: [try f.hypothesis(ts, in: &t), try f.hypothesis(hn, in: &t), sn],
                    in: &t,
                )
            }
            let b1Tuple = try there.have(
                try snoced(a0, records[0], values[0], ht, try there.hypothesis(snocs[0], in: &t), there, &t),
                in: &t,
            )
            let b2Tuple = try there.have(
                try snoced(a2, b2, v2[0], a2Tuple, try there.proof(part(1, false), in: &t), there, &t),
                in: &t,
            )
            let outer = try inj(
                records[0],
                b2,
                p1,
                values[1],
                v2[1],
                last,
                b1Tuple,
                b2Tuple,
                try there.hypothesis(snocs[1], in: &t),
                try there.proof(part(2, false), in: &t),
                there,
                &t,
            )
            let hOuter = try there.have(outer, in: &t)
            let toB1 = try symmetric(try t.intern(.folAndElimL(try there.hypothesis(hOuter, in: &t))), &t)
            let moved = try eliminated(
                try base.cite(.snocResCong, in: &t),
                at: try [a2, p, v2[0], b2, records[0]].map { try there.variable($0, in: &t) },
                premises: [try there.proof(part(1, false), in: &t), toB1],
                in: &t,
            )
            let inner = try inj(
                a0,
                a2,
                p,
                values[0],
                v2[0],
                records[0],
                ht,
                a2Tuple,
                try there.hypothesis(snocs[0], in: &t),
                moved,
                there,
                &t,
            )
            let hInner = try there.have(inner, in: &t)
            equal.append((
                a2,
                a0,
                try there.have(
                    try symmetric(try t.intern(.folAndElimL(try there.hypothesis(hInner, in: &t))), &t),
                    in: &t,
                ),
            ))
            equal.append((
                v2[0],
                values[0],
                try there.have(
                    try symmetric(try t.intern(.folAndElimR(try there.hypothesis(hInner, in: &t))), &t),
                    in: &t,
                ),
            ))
            equal.append((
                v2[1],
                values[1],
                try there.have(
                    try symmetric(try t.intern(.folAndElimR(try there.hypothesis(hOuter, in: &t))), &t),
                    in: &t,
                ),
            ))
        }
        let tupled = try there.proof(part(m + 1, false), in: &t)
        guard let from = t.conclusion(of: tupled) else { throw TableError.expectedStep(tupled) }
        let to = try tuple(
            try ([p, p1, a0] + values).map { try there.variable($0, in: &t) },
            try there.variable(rho2, in: &t),
            in: &t,
        )
        let walk = try Replacement(base: base) { phi, l, r, s, t in
            guard case .folPred = t[phi], l != r else { return nil }
            return try congruent(l, r, base, { x, y, t in
                for e in equal
                    where try s.variable(e.from, in: &t) == x && s
                    .variable(e.to, in: &t) == y
                { return try s.hypothesis(
                    e.proof,
                    in: &t,
                ) }
                throw ClassError.unexpected("an entry moved by no equation")
            }, &t)
        }.proof(from, from, to, in: there.scope, &t)
        let carried = try t.intern(.folIffElimL(walk, tupled))
        let member = try there.proof(part(m + 2, true), in: &t)
        let forward = try there.close(
            try introduced(
                try there.scope.lift(y, from: M.scope.depth, in: &t),
                at: [try there.variable(rho2, in: &t)],
                from: try t.intern(.folAndIntro(carried, member)),
                in: &t,
            ),
            in: &t,
        )
        let exact = try M.close(try t.intern(.folIffIntro(forward, backward)), in: &t)
        return try g.top.close(try t.intern(.folExistsIntro(exact, try g.top.variable(U, in: &t))), in: &t)
    }

    func singleton(_ c: Constant, _ t: inout Table) throws -> NodeID {
        let ex: NodeID
        let uniq: NodeID
        let definition: NodeID
        switch c {
        case .defined(let d):
            let e = ConstantFact(constant: c, type: .i, fact: .existence)
            let u = ConstantFact(constant: c, type: .i, fact: .uniqueness)
            (ex, uniq) = (try cited(e, try statement(e, in: &t), &t), try cited(u, try statement(u, in: &t), &t))
            definition = try t.intern(.use(.definition(d), [], try atDefinition(d, definitions, in: &t)))

        case .primitive(.zf(.zero)):
            (ex, uniq, definition) = (
                try base.cite(.zfZeroEX, in: &t),
                try base.cite(.zfZeroUNIQ, in: &t),
                try base.cite(.zfZeroDef, in: &t),
            )

        case .primitive(.zf(.inf)):
            (ex, uniq, definition) = (
                try base.cite(.zfInfEX, in: &t),
                try base.cite(.zfInfUNIQ, in: &t),
                try base.cite(.zfInfDef, in: &t),
            )

        case .primitive, .declared:
            throw ClassError.noDefinition(c.name)
        }
        var top = Frame()
        let (v0, h0) = try top.open(ex, in: &t)
        let value = try top.variable(v0, in: &t)
        let pair = try eliminated(
            try base.cite(.upairEx, in: &t),
            at: [value, value],
            premises: [try isaGuard(value, .i, &t), try isaGuard(value, .i, &t)],
            in: &t,
        )
        let (w, hw) = try top.open(pair, in: &t)
        let unfolded = try eliminated(
            try base.cite(.upairDef, in: &t),
            at: [
                try top.variable(v0, in: &t),
                try top.variable(v0, in: &t),
                try top.variable(w, in: &t),
            ],
            in: &t,
        )
        let members = try t.intern(.folAndElimR(try t.intern(.folAndElimR(try t.intern(.folIffElimL(
            unfolded,
            try top.hypothesis(hw, in: &t),
        ))))))
        let hm = try top.have(members, in: &t)
        var each = Frame(top.scope)
        let vl = each.fix(.i)
        let v = try each.variable(vl, in: &t)
        let v0e = try each.variable(v0, in: &t)
        let equal = try t.intern(.folPred(.base("eq"), args: [v, v0e]))
        let either = try t.intern(.isaAllElim(try each.hypothesis(hm, in: &t), v))
        let once = try base.applied(
            .iffSymm,
            [equal, try t.intern(.folOr(equal, equal))],
            [try base.instance(.orIdem, [equal], in: &t)],
            in: &t,
        )
        let member = try base.applied(
            .iffTrans,
            [try sides(either, t).left, try sides(either, t).right, equal],
            [either, once],
            in: &t,
        )
        let named = try t.intern(.folPred(.constant(c), args: [v]))
        var there = Frame(each.scope)
        let he = there.assume(equal)
        let atV0 = try eliminated(definition, at: [try there.variable(v0, in: &t)], in: &t)
        let atV = try eliminated(definition, at: [try there.variable(vl, in: &t)], in: &t)
        let from = try sides(atV0, t).right
        let to = try sides(atV, t).right
        let carried = try Replacement(base: base) { phi, l, r, s, t in
            try self.carried(phi, l, r, s, { s, a, b, t in
                try eliminated(
                    try base.cite(.eqSymm, in: &t),
                    at: [b, a],
                    premises: [try s.hypothesis(he, in: &t)],
                    in: &t,
                )
            }, &t)
        }.proof(from, from, to, in: there.scope, &t)
        let body0 = try t.intern(.folIffElimL(atV0, try there.hypothesis(h0, in: &t)))
        let forward = try there.close(
            try t.intern(.folIffElimR(atV, try t.intern(.folIffElimL(carried, body0)))),
            in: &t,
        )
        var back = Frame(each.scope)
        let hn = back.assume(named)
        let backward = try back.close(
            try eliminated(
                uniq,
                at: [try back.variable(vl, in: &t), try back.variable(v0, in: &t)],
                premises: [
                    try back.hypothesis(hn, in: &t),
                    try back.hypothesis(h0, in: &t),
                ],
                in: &t,
            ),
            in: &t,
        )
        let exact = try base.applied(
            .iffTrans,
            [try sides(member, t).left, equal, named],
            [member, try t.intern(.folIffIntro(forward, backward))],
            in: &t,
        )
        let every = try each.close(exact, in: &t)
        return try top.close(
            try introduced(
                try statement(ConstantFact(constant: c, type: .i, fact: .classExists), in: &t),
                at: [try top.variable(w, in: &t)],
                from: every,
                in: &t,
            ),
            in: &t,
        )
    }

    private func source(_ c: Constant, _ T: IRType, _ t: inout Table) throws
        -> (definition: NodeID, outside: Int, raw: NodeID, named: NodeID)
    {
        let classes = T.domains.filter { $0 != .i }
        let k = classes.count
        switch c {
        case .defined(let d):
            guard let found = definitions.first(where: { $0.defines == .constant(d) })
            else { throw ClassError.noDefinition(d.name) }
            let parameters = try classes.indices.map { try t.intern(.isaBound(k - 1 - $0, classes[$0])) }
            let lambda = try definedLambda(found, classes: parameters, in: &t)
            let raw = try classBody(lambda, raw: true, in: &t)
            let named = try classBody(lambda, raw: false, in: &t)
            return (
                try t.intern(.use(.definition(d), [], try atDefinition(d, definitions, in: &t))),
                named.outside,
                raw.body,
                named.body,
            )

        case .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)):
            let s: BaseStatement = c == .primitive(.zf(.pow))
                ? .zfPowDef
                : c == .primitive(.zf(.union)) ? .zfUnionDef : .zfPrimReplaceDef
            let definition = try base.cite(s, in: &t)
            guard var inner = t.conclusion(of: definition) else { throw TableError.expectedStep(definition) }
            for _ in 0...k {
                guard case .folForall(let body) = t[inner] else { throw ClassError.noDefinition(c.name) }
                inner = body
            }
            var outside = 0
            var matrix = try iff(inner, t).right
            while case .ifolAll(.i, let body) = t[matrix] { (outside, matrix) = (outside + 1, body) }
            let phi = try dropping(try iff(matrix, t).right, k + outside, in: &t)
            return (definition, outside, phi, phi)

        case .primitive, .declared:
            throw ClassError.noDefinition(c.name)
        }
    }

    private func records(_ rho: Record, _ W: Int, _ reading: Reading, _ f: Frame, _ t: inout Table) throws -> NodeID {
        var there = Frame(f.scope)
        let h = there.assume(try pred("elem", [rho.variable, W], at: f.scope, &t))
        let tupled = try reading.tupled(rho, in: there.scope, &t)
        var inside = there.scope
        let r0 = inside.fix(.i)
        let x = try t.intern(.ifolEx(.i, body: try t.intern(.folAnd(
            try tuple(try rho.entries.map { try inside.variable($0, in: &t) }, try inside.variable(r0, in: &t), in: &t),
            try pred("elem", [r0, W], at: inside, &t),
        ))))
        let some = try introduced(
            x,
            at: [try there.variable(rho.variable, in: &t)],
            from: try t.intern(.folAndIntro(tupled, try there.hypothesis(h, in: &t))),
            in: &t,
        )
        let forward = try there.close(some, in: &t)
        var back = Frame(f.scope)
        let hx = back.assume(x)
        let (other, ho) = try back.open(try back.hypothesis(hx, in: &t), in: &t)
        let entries = try rho.entries.map { try back.variable($0, in: &t) }
        let uniq = TupleFact(arity: entries.count, fact: .uniqueness)
        let reflexive = try entries.map { try eliminated(try base.cite(.eqRefl, in: &t), at: [$0], in: &t) }
        let atEntries = try eliminated(
            try cited(uniq, try statement(uniq, in: &t), &t),
            at: entries + entries,
            premises: reflexive,
            in: &t,
        )
        let same = try eliminated(
            atEntries,
            at: [try back.variable(other, in: &t), try back.variable(rho.variable, in: &t)],
            premises: [
                try t.intern(.folAndElimL(try back.hypothesis(ho, in: &t))),
                try reading.tupled(rho, in: back.scope, &t),
            ],
            in: &t,
        )
        let cong = try eliminated(
            try base.cite(.congElemL, in: &t),
            at: try [other, rho.variable, W].map { try back.variable($0, in: &t) },
            premises: [same],
            in: &t,
        )
        let backward = try back.close(
            try t.intern(.folIffElimL(cong, try t.intern(.folAndElimR(try back.hypothesis(ho, in: &t))))),
            in: &t,
        )
        return try t.intern(.folIffIntro(forward, backward))
    }

    private func rekeyed(
        _ hU: Int,
        _ a: Int,
        _ ht: Int,
        _ values: [Int],
        _: Int,
        _ p: Int,
        _ p1: Int,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let m = values.count
        func level(
            _ j: Int,
            _ prefix: Int,
            _ snocs: [Int],
            _ records: [Int],
            _ g: Frame,
            _ t: inout Table,
        ) throws -> NodeID {
            var h = Frame(g.scope)
            let b = h.fix(.i)
            let s = h.assume(try pred("snoc", [prefix, j == 0 ? p : p1, values[j], b], at: h.scope, &t))
            let inner: NodeID
            if j == m - 1 {
                var e = try t.intern(.isaAllElim(try h.hypothesis(hU, in: &t), try h.variable(a, in: &t)))
                e = try t.intern(.folImpliesElim(e, try h.hypothesis(ht, in: &t)))
                inner = try eliminated(
                    e,
                    at: try (values + records + [b]).map { try h.variable($0, in: &t) },
                    premises: try (snocs + [s]).map { try h.hypothesis($0, in: &t) },
                    in: &t,
                )
            } else {
                inner = try level(j + 1, b, snocs + [s], records + [b], h, &t)
            }
            let premise = try h.close(inner, in: &t)
            let psi = try unshift(try sides(inner, t).right, in: &t)
            let some = try base.instance(
                .snocSome,
                [try t.intern(.folLetterAbs(body: try sides(inner, t).left)), psi],
                in: &t,
            )
            return try eliminated(
                some,
                at: try [prefix, j == 0 ? p : p1, values[j]].map { try g.variable($0, in: &t) },
                premises: [premise],
                in: &t,
            )
        }
        let read = try level(0, a, [], [], f, &t)
        return try base.applied(.iffSymm, [try sides(read, t).left, try sides(read, t).right], [read], in: &t)
    }

    private func carried(
        _ phi: NodeID,
        _ l: NodeID,
        _ r: NodeID,
        _ s: Scope,
        _ equal: @escaping (Scope, NodeID, NodeID, inout Table) throws -> NodeID,
        _ t: inout Table,
    ) throws -> NodeID? {
        guard case .folPred(.base(let name), let ls) = t[phi], l != r else { return nil }
        guard let def = unfolding[name], case .folPred(_, let rs) = t[r] else {
            return try congruent(l, r, base, { a, b, t in try equal(s, a, b, &t) }, &t)
        }
        let dl = try eliminated(try base.cite(def, in: &t), at: ls, in: &t)
        let dr = try eliminated(try base.cite(def, in: &t), at: rs, in: &t)
        let walk = try Replacement(base: base) { phi, l, r, s, t in try carried(phi, l, r, s, equal, &t) }
            .proof(try sides(dl, t).right, try sides(dl, t).right, try sides(dr, t).right, in: s, &t)
        let back = try base.applied(.iffSymm, [r, try sides(dr, t).right], [dr], in: &t)
        return try chained(try chained(dl, walk, &t), back, &t)
    }

    private func chained(_ p: NodeID, _ q: NodeID, _ t: inout Table) throws -> NodeID {
        let (a, b) = try sides(p, t), c = try sides(q, t).right
        return try base.applied(.iffTrans, [a, b, c], [p, q], in: &t)
    }
}

private let unfolding: [String: BaseStatement] = ["zero": .zeroDef, "Inf": .infDef, "ind": .indDef]
