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
    let statement = children(n)[0]
    var proof = try cited(Unfolding(constant: c, statement: statement), statement, &t)
    var at = stated
    for a in args {
        guard case .ifolAll(let T, let body) = t[at] else { throw UnfoldingError.notADefinition(id) }
        proof = try Functions(base: base).instance(proof, of: at, at: a, T, in: &t)
        at = try instantiate(body, with: a, in: &t)
    }
    return proof
}

struct UnfoldingProofs {
    let base: Base
    let definitions: [Definition]

    func prove(_ r: Unfolding, in t: inout Table) throws -> NodeID {
        let graphs = GraphProofs(base: base, definitions: definitions)
        let d = try graphs.definition(r.constant)
        let domains = d.type.domains
        var s = Scope()
        let variables = domains.map { s.fix($0) }
        var matrix = r.statement
        for _ in domains {
            guard case .ifolAll(_, let body) = t[matrix] else { throw UnfoldingError.notAnUnfolding(r.name) }
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
        for T in domains.reversed() { proof = try t.intern(.isaAllIntro(T, body: proof)) }
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
        let (ks, hks) = try slotClasses(&f, &t)
        let (c, hc) = try f.open(try classExists(ks, f, &t), in: &t)
        let (tw, ht) = try f.open(try tupleExists(f, &t), in: &t)
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
                at: try (sets + [tw]).map { try f.variable($0, in: &t) },
                premises: [try f.hypothesis(ht, in: &t)],
                in: &t,
            ),
            in: &t,
        )
        let member = try converted(c, ks, hc, tw, ht, value: r, &f, &t)
        let valued = try t.intern(.folIffElimL(member, try f.hypothesis(hr, in: &t)))
        let core = try readBack(ks, hks, value: r, f, &t).map { try t.intern(.folIffElimL($0, valued)) } ?? valued
        return try f.close(
            try closing(
                try f.scope.lift(matrix, from: depth, in: &t),
                try (ks + [c, tw, r]).map { try f.variable($0, in: &t) },
                try (hks + [hc, ht, hr]).map { try f.hypothesis($0, in: &t) },
                core,
                in: &t,
            ),
            in: &t,
        )
    }

    func predicate(_ matrix: NodeID, _ f: Frame, _ t: inout Table) throws -> NodeID {
        guard case .folIff(let left, let right) = t[matrix] else { throw UnfoldingError.notAnUnfolding(name) }
        var fw = f
        let ha = fw.assume(try fw.scope.lift(left, from: depth, in: &t))
        let o = try fw.open(chain: .hypothesis(ha), slots.map { _ in .cls } + [.cls, .set], in: &t)
        let k = slots.count
        let hks = try o.constraints[..<k].map { try fw.have(try fw.proof($0, in: &t), in: &t) }
        let hc = try fw.have(try fw.proof(o.constraints[k], in: &t), in: &t)
        let ht = try fw.have(try fw.proof(o.constraints[k + 1], in: &t), in: &t)
        let ks = Array(o.witnesses[..<k])
        let member = try converted(o.witnesses[k], ks, hc, o.witnesses[k + 1], ht, value: nil, &fw, &t)
        var reached = try t.intern(.folIffElimL(member, try fw.proof(o.core, in: &t)))
        if let read = try readBack(ks, hks, value: nil, fw, &t) { reached = try t.intern(.folIffElimL(read, reached)) }
        let forward = try fw.close(reached, in: &t)

        var bw = f
        let hb = bw.assume(try bw.scope.lift(right, from: depth, in: &t))
        let (bks, bhks) = try slotClasses(&bw, &t)
        let (c, hc2) = try bw.open(try classExists(bks, bw, &t), in: &t)
        let (tw, ht2) = try bw.open(try tupleExists(bw, &t), in: &t)
        let member2 = try converted(c, bks, hc2, tw, ht2, value: nil, &bw, &t)
        var body = try bw.hypothesis(hb, in: &t)
        if let read = try readBack(bks, bhks, value: nil, bw, &t) { body = try t.intern(.folIffElimR(read, body)) }
        let inC = try t.intern(.folIffElimR(member2, body))
        let backward = try bw.close(
            try closing(
                try bw.scope.lift(left, from: depth, in: &t),
                try (bks + [c, tw]).map { try bw.variable($0, in: &t) },
                try (bhks + [hc2, ht2]).map { try bw.hypothesis($0, in: &t) },
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

    private var sets: [Int] {
        variables.indices.filter { domains[$0] == .i }.map { variables[$0] }
    }

    private var slots: [Int] {
        variables.indices.filter { domains[$0] != .i }
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

    private func classExists(_ ks: [Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        let fact = ConstantFact(constant: constant, type: definition.type, fact: .classExists)
        return try eliminated(
            try cited(fact, try statement(fact, in: &t), &t),
            at: try ks.map { try f.variable($0, in: &t) },
            in: &t,
        )
    }

    private func tupleExists(_ f: Frame, _ t: inout Table) throws -> NodeID {
        let fact = TupleFact(arity: sets.count, fact: .existence)
        return try eliminated(
            try cited(fact, try statement(fact, in: &t), &t),
            at: try sets.map { try f.variable($0, in: &t) },
            in: &t,
        )
    }

    private func converted(
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

    private func readBack(
        _ ks: [Int],
        _ hks: [Int],
        value r: Int?,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID? {
        let arguments = try slots.indices.map { n in
            try LambdaProofs(base: base).atArguments(
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
