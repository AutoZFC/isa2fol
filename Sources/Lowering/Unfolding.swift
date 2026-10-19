import IR

@frozen
public enum UnfoldingError: Error, Equatable, Sendable {
    case notADefinition(NodeID)
    case notAnUnfolding(String)
}

func unfolded(_ n: Node, was id: NodeID, base: Base, in t: inout Table) throws -> NodeID {
    guard case .isaDefinition(_, .constant(let c), _, let stated, let args) = t[id] else {
        throw UnfoldingError.notADefinition(id)
    }
    return try unfolding(c, stated: stated, statement: children(n)[0], at: args, base: base, in: &t)
}

func unfolding(
    _ c: Defined,
    stated: NodeID,
    statement: NodeID,
    at args: [NodeID],
    base: Base,
    in t: inout Table,
) throws -> NodeID {
    var proof = try cited(Unfolding(constant: c, statement: statement), statement, &t)
    var at = stated
    for a in args {
        guard case .ifolAll(let T, let body) = t[at] else { throw UnfoldingError.notADefinition(stated) }
        proof = try Functions(base: base).instance(proof, of: at, at: a, T, in: &t)
        at = try instantiate(body, with: a, in: &t)
    }
    return proof
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
            if domains.isEmpty {
                try unfolder.set(matrix, Frame(s), &t)
            } else if result(d.type) == .o {
                try unfolder.predicate(matrix, Frame(s), &t)
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

    func set(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        var f = f
        let fact = ConstantFact(constant: constant, type: .i, fact: .existence)
        let (v, hv) = try f.open(try cited(fact, try statement(fact, in: &t), &t), in: &t)
        let V = try f.variable(v, in: &t)
        let def = try eliminated(try graphs.definitionCited(constant, &t), at: [V], in: &t)
        let valued = try t.intern(.folIffElimL(def, try f.hypothesis(hv, in: &t)))
        let formula = try f.scope.lift(matrix, from: depth, in: &t)
        return try f.close(try closing(formula, [V], [try f.hypothesis(hv, in: &t)], valued, in: &t), in: &t)
    }

    func function(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        var f = f
        let (es, hes) = try truthSets(&f, &t)
        let (ks, hks) = try slotClasses(&f, &t)
        let at = atTuple(es)
        let (c, hc) = try f.open(try at.classExists(ks, f, &t), in: &t)
        let (tw, ht) = try f.open(try at.tupleExists(f, &t), in: &t)
        let total = ConstantFact(constant: constant, type: definition.type, fact: .totality)
        let classes = try (ks + [c]).map { try f.variable($0, in: &t) }
        let atC = try eliminated(
            try cited(total, try statement(total, in: &t), &t),
            at: classes,
            premises: [try f.hypothesis(hc, in: &t)],
            in: &t,
        )
        let (r, hr) = try f.open(
            try eliminated(
                atC,
                at: try (at.sets + [tw]).map { try f.variable($0, in: &t) },
                premises: [try f.hypothesis(ht, in: &t)],
                in: &t,
            ),
            in: &t,
        )
        let member = try at.converted(c, ks, hc, tw, ht, value: r, &f, &t)
        let valued = try t.intern(.folIffElimL(member, try f.hypothesis(hr, in: &t)))
        var core = try readBack(ks, hks, es, value: r, f, &t).map { try t.intern(.folIffElimL($0, valued)) } ?? valued
        if let read = try truthsRead(es, hes, value: r, f, &t) { core = try t.intern(.folIffElimL(read, core)) }
        return try f.close(
            try closing(
                try f.scope.lift(matrix, from: depth, in: &t),
                try (es + ks + [c, tw, r]).map { try f.variable($0, in: &t) },
                try (hes + hks + [hc, ht, hr]).map { try f.hypothesis($0, in: &t) },
                core,
                in: &t,
            ),
            in: &t,
        )
    }

    func predicate(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        guard case .folIff(let left, let right) = t[matrix] else { throw UnfoldingError.notAnUnfolding(name) }
        let p = propositions.count
        let k = slots.count
        var fw = f
        let ha = fw.assume(try fw.scope.lift(left, from: depth, in: &t))
        let binders = propositions.map { _ in Binder.set } + slots.map { _ in .cls } + [.cls, .set]
        let o = try fw.open(chain: .hypothesis(ha), binders, in: &t)
        let hes = try o.constraints[..<p].map { try fw.have(try fw.proof($0, in: &t), in: &t) }
        let hks = try o.constraints[p..<(p + k)].map { try fw.have(try fw.proof($0, in: &t), in: &t) }
        let hc = try fw.have(try fw.proof(o.constraints[p + k], in: &t), in: &t)
        let ht = try fw.have(try fw.proof(o.constraints[p + k + 1], in: &t), in: &t)
        let es = Array(o.witnesses[..<p])
        let ks = Array(o.witnesses[p..<(p + k)])
        let member = try atTuple(es).converted(
            o.witnesses[p + k],
            ks,
            hc,
            o.witnesses[p + k + 1],
            ht,
            value: nil,
            &fw,
            &t,
        )
        var reached = try t.intern(.folIffElimL(member, try fw.proof(o.core, in: &t)))
        if let read = try readBack(ks, hks, es, value: nil, fw, &t) {
            reached = try t.intern(.folIffElimL(read, reached))
        }
        if let read = try truthsRead(es, hes, value: nil, fw, &t) { reached = try t.intern(.folIffElimL(read, reached))
        }
        let forward = try fw.close(reached, in: &t)

        var bw = f
        let hb = bw.assume(try bw.scope.lift(right, from: depth, in: &t))
        let (bes, bhes) = try truthSets(&bw, &t)
        let (bks, bhks) = try slotClasses(&bw, &t)
        let at = atTuple(bes)
        let (c, hc2) = try bw.open(try at.classExists(bks, bw, &t), in: &t)
        let (tw, ht2) = try bw.open(try at.tupleExists(bw, &t), in: &t)
        let member2 = try at.converted(c, bks, hc2, tw, ht2, value: nil, &bw, &t)
        var body = try bw.hypothesis(hb, in: &t)
        if let read = try truthsRead(bes, bhes, value: nil, bw, &t) { body = try t.intern(.folIffElimR(read, body)) }
        if let read = try readBack(bks, bhks, bes, value: nil, bw, &t) { body = try t.intern(.folIffElimR(read, body)) }
        let inC = try t.intern(.folIffElimR(member2, body))
        let backward = try bw.close(
            try closing(
                try bw.scope.lift(left, from: depth, in: &t),
                try (bes + bks + [c, tw]).map { try bw.variable($0, in: &t) },
                try (bhes + bhks + [hc2, ht2]).map { try bw.hypothesis($0, in: &t) },
                inC,
                in: &t,
            ),
            in: &t,
        )
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
            let read = try walked(formula: try proposition(j, f.scope, &t), in: &t)
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
            holes.append((atTruthSets[j]!, try walked(formula: atPropositions[j]!, in: &t), hes[n]))
        }
        let have = try walked(try instance(atTruthSets, value: r, f.scope, &t), base: base, in: &t)
        let wanted = try walked(try instance(atPropositions, value: r, f.scope, &t), base: base, in: &t)
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

    private func readBack(
        _ ks: [Int],
        _ hks: [Int],
        _ es: [Int],
        value r: Int?,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID? {
        let arguments = try slots.indices.map { n in
            try LambdaProofs(base: base).classAtArguments(
                try slot(slots[n], f, &t),
                from: f.scope.depth,
                ks[n],
                hks[n],
                f,
                guardOf: isaGuard,
                in: &t,
            )
        }
        let instantiated = { (step: NodeID, n: Int, t: inout Table) throws -> NodeID in
            let at = try t.intern(.folForallElim(step, try f.variable(ks[n], in: &t)))
            guard guardPredicate(domains[slots[n]]) != nil else { return at }
            return try t.intern(.folImpliesElim(at, try t.intern(.folAndElimL(arguments[n]))))
        }
        var joined: NodeID?
        for (n, j) in slots.enumerated() {
            var outer = f.scope
            let later = slots[(n + 1)...].map { outer.fix(domains[$0]) }
            var inner = outer
            let y = inner.fix(domains[j])
            var givenInner = [Int: NodeID]()
            var givenOuter = [Int: NodeID]()
            for (m, i) in slots.enumerated() {
                if m < n {
                    givenInner[i] = try slot(i, Frame(inner), &t)
                    givenOuter[i] = try slot(i, Frame(outer), &t)
                } else if m == n {
                    givenInner[i] = try inner.variable(y, in: &t)
                    givenOuter[i] = try slot(i, Frame(outer), &t)
                } else {
                    givenInner[i] = try inner.variable(later[m - n - 1], in: &t)
                    givenOuter[i] = try outer.variable(later[m - n - 1], in: &t)
                }
            }
            for (m, i) in propositions.enumerated() {
                givenInner[i] = try holds(try inner.variable(es[m], in: &t), in: &t)
                givenOuter[i] = try holds(try outer.variable(es[m], in: &t), in: &t)
            }
            let psi = try instance(givenInner, value: r, inner, &t)
            let wanted = try walked(try instance(givenOuter, value: r, outer, &t), base: base, in: &t)
            var step = try LambdaInstance(base: base).equivalence(
                domains[j],
                psi,
                try walked(psi, base: base, in: &t),
                wanted,
                try slot(j, Frame(outer), &t),
                in: &t,
            )
            for i in slots[(n + 1)...].reversed() { step = try t.intern(.isaAllIntro(domains[i], body: step)) }
            for m in (n + 1)..<slots.count { step = try instantiated(step, m, &t) }
            step = try t.intern(.folImpliesElim(try instantiated(step, n, &t), arguments[n]))
            joined = try joined.map { try chained($0, step, base, &t) } ?? step
        }
        return joined
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
