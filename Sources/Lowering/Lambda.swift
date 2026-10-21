import IR

@frozen
public enum LambdaError: Error, Equatable, Sendable {
    case notAnInstance(NodeID)
    case notALambda(NodeID)
    case noBeta(NodeID)
    case notMine(String)
    case misproved(String)
}

private func shape(_ lambda: NodeID, in t: Table) throws -> (arity: Int, value: IRType) {
    var n = 0
    var inner = lambda
    while case .isaAbs(let T, let body) = t[inner] {
        guard T == .i else { throw LambdaError.notALambda(lambda) }
        (n, inner) = (n + 1, body)
    }
    guard n > 0, let U = t.type(of: inner), U == .o || U == .i else { throw LambdaError.notALambda(lambda) }
    return (n, U)
}

func atArguments(_ lambda: NodeID, _ K: NodeID, base _: Base, in t: inout Table) throws -> NodeID {
    let (n, value) = try shape(lambda, in: t)
    if value == .o {
        let ts = try (0..<n).map { try t.intern(.isaBound(n - 1 - $0, .i)) }
        let body = try formula(try beta(try shift(lambda, by: n, in: &t), ts, in: &t), .statement, in: &t)
        let atom = try named(atom: .isaVarApp(head: try shift(K, by: n, in: &t), args: ts), in: &t)
        var root = try t.intern(.folIff(atom, body))
        for _ in 0..<n { root = try t.intern(.ifolAll(.i, body: root)) }
        return root
    }
    let ts = try (0..<n).map { try t.intern(.isaBound(n + 1 - $0, .i)) }
    let tau = try t.intern(.isaBound(1, .i))
    let r = try t.intern(.isaBound(0, .i))
    let value2 = try formula(
        try equation(r, try beta(try shift(lambda, by: n + 2, in: &t), ts, in: &t), in: &t),
        .statement,
        in: &t,
    )
    let applied = try t.intern(.folPred(.base("apply"), args: [tau, r, try shift(K, by: n + 2, in: &t)]))
    var root = try t.intern(.ifolAll(.i, body: try t.intern(.folIff(applied, value2))))
    let tupled = try tuple(
        try (0..<n).map { try t.intern(.isaBound(n - $0, .i)) },
        try t.intern(.isaBound(0, .i)),
        in: &t,
    )
    root = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(tupled, root))))
    for _ in 0..<n { root = try t.intern(.ifolAll(.i, body: root)) }
    guard
        let T = t.type(of: lambda),
        let function = try guarded(K, T, in: &t)
    else { throw LambdaError.notALambda(lambda) }
    return try t.intern(.folAnd(function, root))
}

struct LambdaProofs {
    let base: Base

    func arguments(_ f: LambdaFact, in t: inout Table) throws -> NodeID {
        var fr = Frame()
        var guards = [Int: Int]()
        for (j, T) in f.types.enumerated() {
            let v = fr.fix(T)
            if T != .i, let g = try guarded(try fr.variable(v, in: &t), T, in: &t) { guards[j] = fr.assume(g) }
        }
        let vs = try f.types.indices.map { try fr.variable($0, in: &t) }
        let classF = LambdaFact(
            lambda: f.lambda,
            types: f.types,
            fact: .classExists,
            name: "CLASS_" + fingerprint(f.lambda, t),
        )
        let atV = try instantiated(
            try cited(classF, try statement(classF, base: base, in: &t), &t),
            at: vs,
            f.types,
            guards: false,
            guardOf: isaGuard,
            in: &t,
        )
        let (k, h) = try fr.open(atV, in: &t)
        let atK = try f.types.indices.map { try fr.variable($0, in: &t) }
        let guardOf = { (x: NodeID, _: IRType, t: inout Table) throws -> NodeID in
            guard let j = atK.firstIndex(of: x), let g = guards[j] else { throw LambdaError.notMine(f.name) }
            return try fr.hypothesis(g, in: &t)
        }
        let at = try classAtArguments(f.lambda, from: f.types.count, k, h, fr, guardOf: guardOf, in: &t)
        return try fr.close(try t.intern(.folExistsIntro(at, try fr.variable(k, in: &t))), in: &t)
    }

    func classAtArguments(
        _ lambda: NodeID,
        from depth: Int,
        _ k: Int,
        _ h: Int,
        _ fr: Frame,
        guardOf: (NodeID, IRType, inout Table) throws -> NodeID,
        in t: inout Table,
    ) throws -> NodeID {
        let (n, value) = try shape(lambda, in: t)
        guard value == .i else { return try predicate(lambda, depth, n, k, h, fr, &t) }
        let (functionF, c) = try lambdaFact(try fr.scope.lift(lambda, from: depth, in: &t), .function, in: &t)
        let atVF = try instantiated(
            try cited(functionF, try statement(functionF, base: base, in: &t), &t),
            at: c.variables,
            c.types,
            guards: true,
            guardOf: guardOf,
            in: &t,
        )
        let K = try fr.variable(k, in: &t)
        let function = try eliminated(atVF, at: [K], premises: [try fr.hypothesis(h, in: &t)], in: &t)
        return try t.intern(.folAndIntro(function, try self.function(lambda, depth, n, k, h, fr, guardOf, &t)))
    }

    func atTuple(
        _ d: Int,
        _ tupled: Int,
        _ ts: [Int],
        _ tw: Int,
        _ body: (Frame, inout Table) throws -> NodeID,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let definition = try f.hypothesis(d, in: &t)
        guard case .folIff(let member, _)? = t.conclusion(of: definition).map({ t[$0] }) else {
            throw LambdaError.notMine("a class's definition")
        }
        let n = ts.count
        var fw = Frame(f.scope)
        let hm = fw.assume(member)
        let opened = try t.intern(.folIffElimL(try fw.hypothesis(d, in: &t), try fw.hypothesis(hm, in: &t)))
        guard n > 0 else {
            let forward = try fw.close(try t.intern(.folAndElimR(opened)), in: &t)
            return try t.intern(.folIffIntro(forward, try back(d, tupled, ts, body, f, &t)))
        }
        let (xs, conj) = try fw.open(opened, count: n, in: &t)
        let inj = TupleFact(arity: n, fact: .injectivity)
        let equal = try eliminated(
            try cited(inj, try statement(inj, in: &t), &t),
            at: try (xs + ts + [tw]).map { try fw.variable($0, in: &t) },
            premises: [try fw.proof(.left(conj), in: &t), try fw.hypothesis(tupled, in: &t)],
            in: &t,
        )
        let e = try fw.have(equal, in: &t)
        let moved = try transported(
            try fw.proof(.right(conj), in: &t),
            to: try body(fw, &t),
            xs,
            ts,
            equalities: e,
            fw,
            &t,
        )
        let forward = try fw.close(moved, in: &t)
        return try t.intern(.folIffIntro(forward, try back(d, tupled, ts, body, f, &t)))
    }

    private func predicate(
        _ lambda: NodeID,
        _ depth: Int,
        _ n: Int,
        _ k: Int,
        _ h: Int,
        _ fr: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var sub = Frame(fr.scope)
        let ts = (0..<n).map { _ in sub.fix(.i) }
        let body = { (f2: Frame, t: inout Table) throws -> NodeID in
            try formula(
                try beta(
                    try f2.scope.lift(lambda, from: depth, in: &t),
                    try ts.map { try f2.variable($0, in: &t) },
                    in: &t,
                ),
                .statement,
                in: &t,
            )
        }
        var each = Frame(sub.scope)
        let tw = each.fix(.i)
        let tupled = each.assume(try tuple(
            try ts.map { try each.variable($0, in: &t) },
            try each.variable(tw, in: &t),
            in: &t,
        ))
        let d = try each.have(
            try eliminated(try each.hypothesis(h, in: &t), at: [try each.variable(tw, in: &t)], in: &t),
            in: &t,
        )
        let c = try sub.have(try each.close(try atTuple(d, tupled, ts, tw, body, each, &t), in: &t), in: &t)
        var fw = Frame(sub.scope)
        let atom = try named(
            atom: .isaVarApp(head: try fw.variable(k, in: &t), args: try ts.map { try fw.variable($0, in: &t) }),
            in: &t,
        )
        let ha = fw.assume(atom)
        let pair = TupleFact(arity: n, fact: .existence)
        let (tau, th) = try fw.open(
            try eliminated(
                try cited(pair, try statement(pair, in: &t), &t),
                at: try ts.map { try fw.variable($0, in: &t) },
                in: &t,
            ),
            in: &t,
        )
        let tupleFact = [try fw.hypothesis(th, in: &t)]
        let held = try eliminated(
            try fw.hypothesis(ha, in: &t),
            at: [try fw.variable(tau, in: &t)],
            premises: tupleFact,
            in: &t,
        )
        let atTau = try eliminated(
            try fw.hypothesis(c, in: &t),
            at: [try fw.variable(tau, in: &t)],
            premises: tupleFact,
            in: &t,
        )
        let forward = try fw.close(try t.intern(.folIffElimL(atTau, held)), in: &t)
        var bw = Frame(sub.scope)
        let hb = bw.assume(try body(bw, &t))
        var every = Frame(bw.scope)
        let tau2 = every.fix(.i)
        let th2 = every.assume(try tuple(
            try ts.map { try every.variable($0, in: &t) },
            try every.variable(tau2, in: &t),
            in: &t,
        ))
        let atTau2 = try eliminated(
            try every.hypothesis(c, in: &t),
            at: [try every.variable(tau2, in: &t)],
            premises: [try every.hypothesis(th2, in: &t)],
            in: &t,
        )
        let member = try every.close(try t.intern(.folIffElimR(atTau2, try every.hypothesis(hb, in: &t))), in: &t)
        let backward = try bw.close(member, in: &t)
        return try sub.close(try t.intern(.folIffIntro(forward, backward)), in: &t)
    }

    private func function(
        _ lambda: NodeID,
        _ depth: Int,
        _ n: Int,
        _ k: Int,
        _ h: Int,
        _ fr: Frame,
        _ guardOf: (NodeID, IRType, inout Table) throws -> NodeID,
        _ t: inout Table,
    ) throws -> NodeID {
        var sub = Frame(fr.scope)
        let ts = (0..<n).map { _ in sub.fix(.i) }
        let tw = sub.fix(.i)
        let tupled = sub.assume(try tuple(
            try ts.map { try sub.variable($0, in: &t) },
            try sub.variable(tw, in: &t),
            in: &t,
        ))
        let valued = { (r: Int, f2: Frame, t: inout Table) throws -> NodeID in
            let b = try beta(
                try f2.scope.lift(lambda, from: depth, in: &t),
                try ts.map { try f2.variable($0, in: &t) },
                in: &t,
            )
            return try formula(try equation(try f2.variable(r, in: &t), b, in: &t), .statement, in: &t)
        }
        var each = Frame(sub.scope)
        let r = each.fix(.i)
        let d = try each.have(
            try eliminated(try each.hypothesis(h, in: &t), at: [
                try each.variable(tw, in: &t),
                try each.variable(r, in: &t),
            ], in: &t),
            in: &t,
        )
        let member = try sub.have(
            try each.close(try atTuple(d, tupled, ts, tw, { f2, t in try valued(r, f2, &t) }, each, &t), in: &t),
            in: &t,
        )
        let lam = try sub.scope.lift(lambda, from: depth, in: &t)
        let b = try beta(lam, try ts.map { try sub.variable($0, in: &t) }, in: &t)
        let c = try closed(b, in: &t)
        let ex = try existence(of: b, in: &t)
        let here = sub
        let (y, hy) = try sub.open(
            try instantiated(
                try cited(ex, try statement(ex, in: &t), &t),
                at: c.variables,
                c.types,
                guards: true,
                guardOf: { x, T, t in
                    guard case .isaBound(let j, _) = t[x], j >= here.scope.depth - fr.scope.depth else {
                        throw LambdaError.notALambda(x)
                    }
                    let outer = try fr.variable(here.scope.depth - 1 - j, in: &t)
                    return try lifted(try guardOf(outer, T, &t), from: fr.scope, to: here.scope, in: &t)
                },
                in: &t,
            ),
            in: &t,
        )
        let Y = try sub.variable(y, in: &t)
        let atY = try t.intern(.folIffElimR(
            try eliminated(try sub.hypothesis(member, in: &t), at: [Y], in: &t),
            try sub.hypothesis(hy, in: &t),
        ))
        let some = try introduced(
            try someLeft(of: try sub.hypothesis(member, in: &t), in: &t),
            at: [Y],
            from: atY,
            in: &t,
        )
        var last = Frame(sub.scope)
        let r2 = last.fix(.i)
        let R = try last.variable(r2, in: &t)
        let tau = try last.variable(tw, in: &t)
        let pmem = try eliminated(
            try eliminated(
                try base.cite(.applyPmem, in: &t),
                at: [try last.variable(k, in: &t), tau],
                premises: [try last.scope.lift(some, from: sub.scope.depth, in: &t)],
                in: &t,
            ),
            at: [R],
            in: &t,
        )
        let atR = try eliminated(try last.hypothesis(member, in: &t), at: [R], in: &t)
        guard
            case .folIff(let a, let m)? = t.conclusion(of: pmem).map({ t[$0] }),
            case .folIff(_, let c2)? = t.conclusion(of: atR).map({ t[$0] })
        else { throw LambdaError.notALambda(lambda) }
        let chained = try base.applied(.iffTrans, [a, m, c2], [pmem, atR], in: &t)
        return try sub.close(try last.close(chained, in: &t), in: &t)
    }

    private func back(
        _ d: Int,
        _ tupled: Int,
        _ ts: [Int],
        _ body: (Frame, inout Table) throws -> NodeID,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var bw = Frame(f.scope)
        let hb = bw.assume(try body(bw, &t))
        let defined = try bw.hypothesis(d, in: &t)
        let witness = try introduced(
            try sides(defined, t).right,
            at: try ts.map { try bw.variable($0, in: &t) },
            from: try t.intern(.folAndIntro(try bw.hypothesis(tupled, in: &t), try bw.hypothesis(hb, in: &t))),
            in: &t,
        )
        return try bw.close(try t.intern(.folIffElimR(defined, witness)), in: &t)
    }

    private func transported(
        _ p: NodeID,
        to wanted: NodeID,
        _ xs: [Int],
        _ ts: [Int],
        equalities e: Int,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        guard let have = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        if have == wanted { return p }
        let n = xs.count
        return try Carry { q, target, s, t in
            guard let from = t.conclusion(of: q) else { throw TableError.expectedStep(q) }
            let moved = try congruent(from, target, base, { a, b, t in
                for j in 0..<n {
                    let x = try s.variable(xs[j], in: &t)
                    let y = try s.variable(ts[j], in: &t)
                    guard x == a && y == b || y == a && x == b else { continue }
                    var fact = Fact.hypothesis(e)
                    for _ in 0..<j { fact = .right(fact) }
                    let proof = try s.proof(j < n - 1 ? .left(fact) : fact, in: &t)
                    return x == a ? proof : try base.claimed(.eqSymm, [x, y], [proof], in: &t)
                }
                throw LambdaError.noBeta(from)
            }, &t)
            return try t.intern(.folIffElimL(moved, q))
        }.proof(p, from: have, to: wanted, in: f.scope, &t)
    }
}

public struct LambdaProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "lambda"

    public func owns(_ l: Lemma) -> Owned? {
        guard let f = l.request as? LambdaFact, f.fact == .arguments else { return nil }
        return .rule
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _: [Definition],
        _: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved {
        guard let f = l.request as? LambdaFact, f.fact == .arguments else { throw LambdaError.notMine(l.name) }
        let proof = try LambdaProofs(base: base).arguments(f, in: &t)
        guard t.conclusion(of: proof) == statement else { throw LambdaError.misproved(l.name) }
        return .proof(proof)
    }

    public func defines(_: Defined) -> Owned? {
        nil
    }

    public func define(_ c: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        throw LambdaError.notMine(c.definitionName)
    }

    let base: Base

}
