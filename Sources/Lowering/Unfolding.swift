import IR

@frozen
public enum UnfoldingError: Error, Equatable, Sendable {
    case notADefinition(NodeID)
    case notAnUnfolding(String)
}

/// `c_UNFOLD` at its arguments in the statement's form: the instance a proof takes, met to the statement's naming, the
/// values it holds fixed where it stands by their existence.
func unfolding(
    _ c: Defined,
    stated: NodeID,
    statement: NodeID,
    at args: [NodeID],
    base: Base,
    in t: inout Table,
) throws -> NodeID {
    let (proof, matrix) = try definition(c, stated: stated, statement: statement, at: args, base: base, in: &t)
    let named = try met(proof, matrix, moving: .closed, toValues: false, in: &t)
    let inner = try fixing(
        try scoped(named, closed: false, below: Int.max, in: &t),
        in: named,
        by: .existence(base),
        in: &t,
    )
    return try fixing(try scoped(inner, closed: true, in: &t), in: inner, by: .existence(base), in: &t)
}

/// `c_UNFOLD` cited at a definition's terms as a proof cites it — its letters by `schema_inst`, a set term at its
/// value, a λ at its class — and the instance it concludes, in the proof's form.
func definition(
    _ c: Defined,
    stated: NodeID,
    statement: NodeID,
    at args: [NodeID],
    base: Base,
    in t: inout Table,
) throws -> (proof: NodeID, matrix: NodeID) {
    let k = min(letters(stated, t), args.count)
    var proof = try cited(Unfolding(constant: c, statement: statement), statement, &t)
    for a in args.prefix(k) { proof = try t.intern(.folSchemaInst(proof, try valued(a, in: &t))) }
    proof = try metBelowLetters(proof, stated, at: Array(args.prefix(k)), base: base, in: &t)
    var at = stated
    for a in args.prefix(k) {
        guard case .ifolAll(.o, let body) = t[at] else { throw UnfoldingError.notADefinition(a) }
        at = try instantiate(body, with: a, in: &t)
    }
    for a in args.dropFirst(k) {
        guard case .ifolAll(let T, let body) = t[at] else { throw UnfoldingError.notADefinition(a) }
        proof = T == .i
            ? try Instances(base: base).instance(proof, body, T, at: a, in: &t)
            : try instantiatedAtLambda(proof, body, T, at: a, base: base, in: &t)
        at = try instantiate(body, with: a, in: &t)
    }
    return (proof, at)
}

func pointwiseDefinition(_ c: Defined, _ d: Definition, in t: inout Table) throws -> NodeID {
    let domains = d.type.domains
    let n = domains.count
    let arguments = try domains.indices.map { k in try etaLong(try t.intern(.isaBound(n - 1 - k, domains[k])), in: &t) }
    let defined = try t.intern(.isaConst(.defined(c), d.type, args: arguments))
    var stated = try t.equation(result(d.type), defined, try beta(d.definiens, arguments, in: &t))
    for T in domains.reversed() { stated = try t.intern(.ifolAll(T, body: stated)) }
    return stated
}

func etaLong(_ x: NodeID, in t: inout Table) throws -> NodeID {
    guard let T = t.type(of: x) else { throw UnfoldingError.notADefinition(x) }
    let m = T.domains.count
    guard m > 0 else { return x }
    var lambda = try t.intern(.isaVarApp(
        head: try shift(x, by: m, in: &t),
        args: try (0..<m).map { try t.intern(.isaBound(m - 1 - $0, .i)) },
    ))
    for _ in 0..<m { lambda = try t.intern(.isaAbs(.i, body: lambda)) }
    return lambda
}

struct UnfoldingProofs {
    let base: Base
    let definitions: [Definition]

    func prove(_ r: Unfolding, in t: inout Table) throws -> NodeID {
        let graphs = GraphProofs(base: base, definitions: definitions)
        let d = try graphs.definition(r.constant)
        let domains = d.type.domains
        var s = Scope()
        var variables = [Int]()
        var matrix = r.statement
        for T in domains {
            if T == .o {
                guard case .folForall(let guarded) = t[matrix], case .folImplies(_, let body) = t[guarded] else {
                    throw UnfoldingError.notAnUnfolding(r.name)
                }
                let v = s.fix(nil)
                variables.append(v)
                _ = s.assume(try truth(try s.variable(v, in: &t), in: &t))
                matrix = body
                continue
            }
            guard case .ifolAll(_, let body) = t[matrix] else { throw UnfoldingError.notAnUnfolding(r.name) }
            variables.append(s.fix(T))
            matrix = body
        }
        let unfolder = Unfolder(
            base: base,
            graphs: graphs,
            constant: .defined(r.constant),
            definition: d,
            variables: variables,
            depth: s.depth,
            name: r.name,
        )
        var proof: NodeID =
            if result(d.type) == .o {
                try unfolder.predicate(matrix, Frame(s), &t)
            } else if domains.isEmpty {
                try unfolder.set(matrix, Frame(s), &t)
            } else {
                try unfolder.function(matrix, Frame(s), &t)
            }
        for T in domains.reversed() {
            guard T == .o else {
                proof = try t.intern(.isaAllIntro(T, body: proof))
                continue
            }
            let premise = try truth(try t.intern(.folBound(0)), in: &t)
            proof = try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(premise, body: proof))))
        }
        return proof
    }
}

private struct Unfolder {
    let base: Base
    let graphs: GraphProofs
    let constant: Constant
    let definition: Definition
    let variables: [Int]
    let depth: Int
    let name: String

    /// `∀v. c(v) → ⟦v = b⟧`: the value fixed and assumed, its `@def` there.
    func set(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        var f = f
        var rest = try f.scope.lift(matrix, from: depth, in: &t)
        var restScope = f.scope
        let (v, hv) = try peel(&rest, &restScope, &f, &t)
        let def = try eliminated(try graphs.definitionCited(constant, &t), at: [try f.variable(v, in: &t)], in: &t)
        return try f.close(try t.intern(.folIffElimL(def, try f.hypothesis(hv, in: &t))), in: &t)
    }

    /// The pointwise equation's naming: its pieces fixed and assumed, the value's graph at them read back.
    func function(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        var f = f
        var rest = try f.scope.lift(matrix, from: depth, in: &t)
        var restScope = f.scope
        var es = [Int]()
        var hes = [Int]()
        for _ in propositions {
            let (e, h) = try peel(&rest, &restScope, &f, &t)
            es.append(e)
            hes.append(h)
        }
        var ks = [Int]()
        var hks = [Int]()
        for _ in slots {
            let (k, h) = try peel(&rest, &restScope, &f, &t)
            ks.append(k)
            hks.append(h)
        }
        let (c, hc) = try peel(&rest, &restScope, &f, &t)
        let (tw, ht) = try peel(&rest, &restScope, &f, &t)
        let (r, hr) = try peel(&rest, &restScope, &f, &t)
        let at = atTuple(es)
        let member = try at.converted(c, ks, hc, tw, ht, value: r, &f, &t)
        let valued = try t.intern(.folIffElimL(member, try f.hypothesis(hr, in: &t)))
        var core = try readBack(ks, hks, es, value: r, f, &t).map { try t.intern(.folIffElimL($0, valued)) } ?? valued
        if let read = try truthsRead(es, hes, value: r, f, &t) { core = try t.intern(.folIffElimL(read, core)) }
        return try f.close(core, in: &t)
    }

    /// `c(x⃗) ↔ body`: forward the naming's pieces opened by their existence and the naming instantiated there; back
    /// the pieces fixed and assumed.
    func predicate(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        guard case .folIff(let left, let right) = t[matrix] else { throw UnfoldingError.notAnUnfolding(name) }
        var fw = f
        let ha = fw.assume(try fw.scope.lift(left, from: depth, in: &t))
        let (es, hes) = try truthSets(&fw, &t)
        let (ks, hks) = try slotClasses(&fw, &t)
        let at = atTuple(es)
        let (c, hc) = try fw.open(try at.classExists(ks, fw, &t), in: &t)
        let (tw, ht) = try fw.open(try at.tupleExists(fw, &t), in: &t)
        let member = try at.converted(c, ks, hc, tw, ht, value: nil, &fw, &t)
        var naming = try fw.hypothesis(ha, in: &t)
        for (w, h) in zip(es + ks + [c, tw], hes + hks + [hc, ht]) {
            naming = try eliminated(
                naming,
                at: [try fw.variable(w, in: &t)],
                premises: [try fw.hypothesis(h, in: &t)],
                in: &t,
            )
        }
        var reached = try t.intern(.folIffElimL(member, naming))
        if let read = try readBack(ks, hks, es, value: nil, fw, &t) {
            reached = try t.intern(.folIffElimL(read, reached))
        }
        if let read = try truthsRead(es, hes, value: nil, fw, &t) { reached = try t.intern(.folIffElimL(read, reached))
        }
        let forward = try fw.close(reached, in: &t)

        var bw = f
        let hb = bw.assume(try bw.scope.lift(right, from: depth, in: &t))
        var rest = try bw.scope.lift(left, from: depth, in: &t)
        var restScope = bw.scope
        var bes = [Int]()
        var bhes = [Int]()
        for _ in propositions {
            let (e, h) = try peel(&rest, &restScope, &bw, &t)
            bes.append(e)
            bhes.append(h)
        }
        var bks = [Int]()
        var bhks = [Int]()
        for _ in slots {
            let (k, h) = try peel(&rest, &restScope, &bw, &t)
            bks.append(k)
            bhks.append(h)
        }
        let (c2, hc2) = try peel(&rest, &restScope, &bw, &t)
        let (tw2, ht2) = try peel(&rest, &restScope, &bw, &t)
        let member2 = try atTuple(bes).converted(c2, bks, hc2, tw2, ht2, value: nil, &bw, &t)
        var body = try bw.hypothesis(hb, in: &t)
        if let read = try truthsRead(bes, bhes, value: nil, bw, &t) { body = try t.intern(.folIffElimR(read, body)) }
        if let read = try readBack(bks, bhks, bes, value: nil, bw, &t) { body = try t.intern(.folIffElimR(read, body)) }
        let backward = try bw.close(try t.intern(.folIffElimR(member2, body)), in: &t)
        return try t.intern(.folIffIntro(forward, backward))
    }

    private var domains: [IRType] {
        definition.type.domains
    }

    private var slots: [Int] {
        variables.indices.filter { !isEntry(domains[$0]) }
    }

    private var propositions: [Int] {
        variables.indices.filter { domains[$0] == .o }
    }

    private var sets: [Int] {
        variables.indices.filter { domains[$0] == .i }.map { variables[$0] }
    }

    /// The next binder of `rest`, a universal naming at `scope`, fixed in `f` and its constraint assumed.
    private func peel(
        _ rest: inout NodeID,
        _ scope: inout Scope,
        _ f: inout Frame,
        _ t: inout Table,
    ) throws -> (Int, Int) {
        let here = try lifted(rest, from: scope, to: f.scope, in: &t)
        let body: NodeID
        let set: Bool
        switch t[here] {
        case .ifolAll(.i, let b): (body, set) = (b, true)
        case .folForall(let b): (body, set) = (b, false)
        default: throw UnfoldingError.notAnUnfolding(name)
        }
        let w = f.fix(set ? .i : nil)
        guard case .folImplies(let c, let after) = t[body] else { throw UnfoldingError.notAnUnfolding(name) }
        let h = f.assume(c)
        rest = after
        scope = f.scope
        return (w, h)
    }

    private func atTuple(_ truthSets: [Int]) -> AtTuple {
        var queue = truthSets[...]
        let entries = variables.indices.filter { isEntry(domains[$0]) }.map { j in
            domains[j] == .o ? queue.removeFirst() : variables[j]
        }
        return AtTuple(base: base, graphs: graphs, constant: constant, type: definition.type, sets: entries, name: name)
    }

    private func proposition(_ j: Int, _ s: Scope, _ t: inout Table) throws -> NodeID {
        try t.intern(.isaPropBound(s.depth - 1 - variables[j]))
    }

    private func truthSets(_ f: inout Frame, _ t: inout Table) throws -> (sets: [Int], constraints: [Int]) {
        var sets = [Int]()
        var constraints = [Int]()
        for j in propositions {
            let read = try formula(try proposition(j, f.scope, &t), .statement, in: &t)
            let (e, h) = try f.open(try base.instance(.truthSetEX, [read], in: &t), in: &t)
            sets.append(e)
            constraints.append(h)
        }
        return (sets, constraints)
    }

    private func truthsRead(
        _ es: [Int],
        _ hes: [Int],
        value r: Int?,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID? {
        guard !es.isEmpty else { return nil }
        var atTruthSets = [Int: NodeID]()
        var atPropositions = [Int: NodeID]()
        for j in slots {
            atTruthSets[j] = try slot(j, f, &t)
            atPropositions[j] = atTruthSets[j]
        }
        var holes = [(set: NodeID, read: NodeID, constraint: Int)]()
        for (n, j) in propositions.enumerated() {
            atTruthSets[j] = try holds(try f.variable(es[n], in: &t), in: &t)
            atPropositions[j] = try proposition(j, f.scope, &t)
            holes.append((atTruthSets[j]!, try formula(atPropositions[j]!, .statement, in: &t), hes[n]))
        }
        let have = try formula(try instance(atTruthSets, value: r, f.scope, &t), .statement, in: &t)
        let wanted = try formula(try instance(atPropositions, value: r, f.scope, &t), .statement, in: &t)
        let d = f.scope.depth
        return try Replacement(base: base) { _, l, r, inner, t in
            for hole in holes {
                guard
                    l == (try inner.lift(hole.set, from: d, in: &t)),
                    r == (try inner.lift(hole.read, from: d, in: &t))
                else { continue }
                return try inner.proof(.right(.hypothesis(hole.constraint)), in: &t)
            }
            return nil
        }.proof(have, have, wanted, in: f.scope, &t)
    }

    private func slotClasses(_ f: inout Frame, _ t: inout Table) throws -> (classes: [Int], definitions: [Int]) {
        var classes = [Int]()
        var definitions = [Int]()
        for j in slots {
            let (fact, c) = try lambdaFact(try slot(j, f, &t), .classExists, in: &t)
            let some = try instantiated(
                try cited(fact, try statement(fact, base: base, in: &t), &t),
                at: c.variables,
                c.types,
                guards: false,
                guardOf: isaGuard,
                in: &t,
            )
            let (k, h) = try f.open(some, in: &t)
            classes.append(k)
            definitions.append(h)
        }
        return (classes, definitions)
    }

    private func slot(_ j: Int, _ f: Frame, _ t: inout Table) throws -> NodeID {
        let T = domains[j]
        let m = T.domains.count
        let variable = try shift(try f.variable(variables[j], in: &t), by: m, in: &t)
        var lambda = try t.intern(.isaVarApp(
            head: variable,
            args: try (0..<m).map { try t.intern(.isaBound(m - 1 - $0, .i)) },
        ))
        for _ in 0..<m { lambda = try t.intern(.isaAbs(.i, body: lambda)) }
        return lambda
    }

    /// The naming at the slots' classes against it at the slots, `BETA` read one slot after another, the later ones
    /// still at their classes.
    private func readBack(
        _ ks: [Int],
        _ hks: [Int],
        _ es: [Int],
        value r: Int?,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID? {
        guard !slots.isEmpty else { return nil }
        var guards = [NodeID: NodeID]()
        for (m, j) in slots.enumerated() where guardPredicate(domains[j]) != nil {
            let K = try f.variable(ks[m], in: &t)
            let function = try t.intern(.folForallElim(try functionFact(try slot(j, f, &t), base, &t), K))
            guards[K] = try t.intern(.folImpliesElim(function, try f.hypothesis(hks[m], in: &t)))
        }
        var steps = [NodeID]()
        for (n, j) in slots.enumerated() {
            var inner = f.scope
            let y = inner.fix(domains[j])
            var given = [Int: NodeID]()
            var classes = [Int: NodeID]()
            for (m, i) in slots.enumerated() {
                if m < n {
                    given[i] = try slot(i, Frame(inner), &t)
                } else if m == n {
                    given[i] = try inner.variable(y, in: &t)
                } else {
                    let k = inner.depth - 1 - ks[m]
                    given[i] = try t.intern(.isaBound(k, domains[i]))
                    classes[k] = try f.variable(ks[m], in: &t)
                }
            }
            for (m, i) in propositions.enumerated() {
                given[i] = try holds(try inner.variable(es[m], in: &t), in: &t)
            }
            let psi = try instance(given, value: r, inner, &t)
            guard looseIndices(psi, in: t).contains(0) else { continue }
            let read = { (forward: Bool, t: inout Table) throws -> NodeID in
                try betaCited(
                    psi,
                    domains[j],
                    at: try slot(j, f, &t),
                    cls: try f.variable(ks[n], in: &t),
                    definition: try f.hypothesis(hks[n], in: &t),
                    stated: true,
                    forward: forward,
                    classes: classes,
                    guardOf: { x, U, t in try guards[x] ?? isaGuard(x, U, &t) },
                    in: &t,
                )
            }
            steps.append(try t.intern(.folIffIntro(try read(true, &t), try read(false, &t))))
        }
        return steps.isEmpty ? nil : try chained(steps, &t)
    }

    private func instance(_ given: [Int: NodeID], value r: Int?, _ s: Scope, _ t: inout Table) throws -> NodeID {
        var sets = sets[...]
        let args = try domains.indices.map { j -> NodeID in
            if let x = given[j] { return x }
            return try s.variable(sets.removeFirst(), in: &t)
        }
        let body = try beta(definition.definiens, args, in: &t)
        guard let r else { return body }
        return try equation(try s.variable(r, in: &t), body, in: &t)
    }
}

struct AtTuple {
    let base: Base
    let graphs: GraphProofs
    let constant: Constant
    let type: IRType
    let sets: [Int]
    let name: String

    func classExists(_ ks: [Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        let fact = ConstantFact(constant: constant, type: type, fact: .classExists)
        return try eliminated(
            try cited(fact, try statement(fact, in: &t), &t),
            at: try ks.map { try f.variable($0, in: &t) },
            in: &t,
        )
    }

    func tupleExists(_ f: Frame, _ t: inout Table) throws -> NodeID {
        let fact = TupleFact(arity: sets.count, fact: .existence)
        return try eliminated(
            try cited(fact, try statement(fact, in: &t), &t),
            at: try sets.map { try f.variable($0, in: &t) },
            in: &t,
        )
    }

    func converted(
        _ c: Int,
        _ ks: [Int],
        _ hc: Int,
        _ tw: Int,
        _ ht: Int,
        value r: Int?,
        _ f: inout Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let def = try graphs.graph(constant, c, ks, hc)(f.scope, &t)
        let at = try eliminated(def, at: try ([tw] + (r.map { [$0] } ?? [])).map { try f.variable($0, in: &t) }, in: &t)
        guard let stated = t.conclusion(of: at) else { throw TableError.expectedStep(at) }
        var entries = try sides(at, t).right
        for x in sets {
            guard case .ifolEx(.i, let body) = t[entries] else { throw UnfoldingError.notAnUnfolding(name) }
            entries = try instantiate(body, with: try f.variable(x, in: &t), in: &t)
        }
        guard case .folAnd(_, let body) = t[entries], case .folIff = t[stated] else {
            throw UnfoldingError.notAnUnfolding(name)
        }
        let d = try f.have(at, in: &t)
        let level = f.scope.depth
        return try LambdaProofs(base: base).atTuple(
            d,
            ht,
            sets,
            tw,
            { g, t in try g.scope.lift(body, from: level, in: &t) },
            f,
            &t,
        )
    }
}

/// `A₀ ↔ Aₙ` from `A₀ ↔ A₁`, …, `Aₙ₋₁ ↔ Aₙ`.
func chained(_ iffs: [NodeID], _ t: inout Table) throws -> NodeID {
    guard iffs.count > 1 else { return iffs[0] }
    let sides = try iffs.map { p -> (NodeID, NodeID) in
        guard let c = t.conclusion(of: p), case .folIff(let a, let b) = t[c] else { throw TableError.expectedStep(p) }
        return (a, b)
    }
    let first = sides[0].0
    let last = sides[sides.count - 1].1
    let lifted = try iffs.map { try lifted($0, terms: 0, hyps: 1, in: &t) }
    var forward = try t.intern(.hyp(0, first))
    for p in lifted { forward = try t.intern(.folIffElimL(p, forward)) }
    var backward = try t.intern(.hyp(0, last))
    for p in lifted.reversed() { backward = try t.intern(.folIffElimR(p, backward)) }
    return try t.intern(.folIffIntro(
        try t.intern(.folImpliesIntro(first, body: forward)),
        try t.intern(.folImpliesIntro(last, body: backward)),
    ))
}
