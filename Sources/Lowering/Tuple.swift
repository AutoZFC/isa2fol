import IR

func tuple(_ xs: [NodeID], _ target: NodeID, in t: inout Table) throws -> NodeID {
    guard let last = xs.last else { return try t.intern(.folPred(.base("zero"), args: [target])) }
    var c = Chain()
    let empty = c.bind(.set)
    c.constrain(empty, try c.predicate(.base("zero"), [empty], in: &t))
    var index = empty, prefix = empty
    for x in xs.dropLast() {
        let next = c.bind(.set)
        c.constrain(next, try c.predicate(.base("nsucc"), [index, next], in: &t))
        let grown = c.bind(.set)
        c.constrain(grown, try c.predicate(.base("snoc"), [prefix, index, .outer(x), grown], in: &t))
        (index, prefix) = (next, grown)
    }
    return try c.formula(try c.predicate(.base("snoc"), [prefix, index, .outer(last), .outer(target)], in: &t), in: &t)
}

@frozen public enum TupleError: Error, Equatable, Sendable {
    case notMine(String)
    case misproved(String)
}

func tupleBinders(_ n: Int) -> [Binder] { n == 0 ? [] : Array(repeating: .set, count: 2 * n - 1) }

public struct TupleProver: Prover {
    public let name = "tuple"
    let base: Base

    public init(base: Base) { self.base = base }

    public func owns(_ l: Lemma) -> Owned? { l.request is TupleFact ? .rule : nil }

    public func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        guard let f = l.request as? TupleFact else { throw TupleError.notMine(l.name) }
        let proof: NodeID
        switch f.fact {
        case .existence: proof = f.arity == 0 ? try base.cite(.zeroEX, in: &t) : try existence(f.arity, &t)
        case .uniqueness: proof = f.arity == 0 ? try base.cite(.zeroUNIQ, in: &t) : try uniqueness(f.arity, &t)
        case .injectivity: proof = try injectivity(f.arity, &t)
        }
        guard t.conclusion(of: proof) == statement else { throw TupleError.misproved(l.name) }
        return proof
    }

    public func defines(_ c: Defined) -> Owned? { nil }

    public func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID {
        throw TupleError.notMine(c.name)
    }

    private func existence(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }
        let (e, he) = try f.open(try base.cite(.zeroEX, in: &t), in: &t)
        var witnesses = [e], constraints = [he], index = e, prefix = e
        for j in 0..<(n - 1) {
            let (next, hn) = try f.open(try eliminated(try base.cite(.nsuccEX, in: &t), at: [try f.variable(index, in: &t)], in: &t), in: &t)
            let at = try [prefix, index, xs[j]].map { try f.variable($0, in: &t) }
            let (grown, hg) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
            witnesses += [next, grown]
            constraints += [hn, hg]
            (index, prefix) = (next, grown)
        }
        let at = try [prefix, index, xs[n - 1]].map { try f.variable($0, in: &t) }
        let (tau, ht) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
        let formula = try closing(tupleBinders(n), try witnesses.map { try f.variable($0, in: &t) },
                                  try constraints.map { try f.hypothesis($0, in: &t) }, try f.hypothesis(ht, in: &t), in: &t)
        return try f.close(try t.intern(.isaExIntro(formula, try f.variable(tau, in: &t))), in: &t)
    }

    private func uniqueness(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }, ys = (0..<n).map { _ in f.fix(.i) }
        var equal: [Int] = []
        for j in 0..<n { equal.append(f.assume(try eq(try f.variable(xs[j], in: &t), try f.variable(ys[j], in: &t), &t))) }
        let (tau, tau2) = (f.fix(.i), f.fix(.i))
        let ht = f.assume(try tuple(try xs.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let ht2 = f.assume(try tuple(try ys.map { try f.variable($0, in: &t) }, try f.variable(tau2, in: &t), in: &t))
        let a = try f.open(chain: .hypothesis(ht), tupleBinders(n), in: &t)
        let b = try f.open(chain: .hypothesis(ht2), tupleBinders(n), in: &t)
        let spine = try self.spine(a, b, n, f, &t)
        var prefix = try zeroUnique(a, b, f, &t)
        for j in 0..<n {
            let entries = (try f.hypothesis(equal[j], in: &t))
            let (p, q) = j < n - 1 ? (a.constraints[2 + 2 * j], b.constraints[2 + 2 * j]) : (a.core, b.core)
            prefix = try snocUnique(prefix, spine[j], entries, try f.proof(p, in: &t), try f.proof(q, in: &t), &t)
        }
        return try f.close(prefix, in: &t)
    }

    private func injectivity(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }, ys = (0..<n).map { _ in f.fix(.i) }, tau = f.fix(.i)
        let ht = f.assume(try tuple(try xs.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let ht2 = f.assume(try tuple(try ys.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let a = try f.open(chain: .hypothesis(ht), tupleBinders(n), in: &t)
        let b = try f.open(chain: .hypothesis(ht2), tupleBinders(n), in: &t)
        let spine = try self.spine(a, b, n, f, &t)
        let v = { (w: Int, t: inout Table) throws -> NodeID in try f.variable(w, in: &t) }
        let index = { (o: Opened, j: Int, t: inout Table) throws -> NodeID in try v(o.witnesses[j == 0 ? 0 : 2 * j - 1], &t) }
        let prefix = { (o: Opened, j: Int, t: inout Table) throws -> NodeID in try v(o.witnesses[2 * j], &t) }
        let snoc = { (o: Opened, j: Int, t: inout Table) throws -> NodeID in try f.proof(j < n - 1 ? o.constraints[2 + 2 * j] : o.core, in: &t) }
        let e = try prefix(a, 0, &t), entries = try xs.map { try v($0, &t) }, entries2 = try ys.map { try v($0, &t) }
        let indices = try (0..<n).map { try index(a, $0, &t) }
        let prefixes = try (0..<n).map { try prefix(a, $0, &t) }, primed = try (0..<n).map { $0 == 0 ? e : try prefix(b, $0, &t) }
        let results = try (0..<n).map { $0 < n - 1 ? try prefix(a, $0 + 1, &t) : try v(tau, &t) }
        let results2 = try (0..<n).map { $0 < n - 1 ? try prefix(b, $0 + 1, &t) : try v(tau, &t) }
        var snocs2: [NodeID] = []
        for j in 0..<n {
            let from = try prefix(b, j, &t)
            let start = j == 0 ? try symmetric(spine[0], &t) : try reflexive(from, &t)
            snocs2.append(try eliminated(try base.cite(.snocCONG, in: &t),
                                         at: [from, primed[j], try index(b, j, &t), indices[j], entries2[j], entries2[j], results2[j]],
                                         premises: [start, try symmetric(spine[j], &t), try reflexive(entries2[j], &t), try snoc(b, j, &t)],
                                         in: &t))
        }
        var tuples = [try emptyTuple(e, a, f, &t)], tuples2 = [tuples[0]]
        for j in 0..<(n - 1) {
            let nsucc = try f.proof(a.constraints[1 + 2 * j], in: &t)
            tuples.append(try eliminated(try base.cite(.tupleSnoc, in: &t), at: [prefixes[j], results[j], indices[j], entries[j], indices[j + 1]],
                                         premises: [tuples[j], nsucc, try snoc(a, j, &t)], in: &t))
            tuples2.append(try eliminated(try base.cite(.tupleSnoc, in: &t), at: [primed[j], results2[j], indices[j], entries2[j], indices[j + 1]],
                                          premises: [tuples2[j], nsucc, snocs2[j]], in: &t))
        }
        var equalities: [NodeID] = [], above: NodeID?
        for j in (0..<n).reversed() {
            var second = snocs2[j]
            if let above {
                second = try eliminated(try base.cite(.snocResCong, in: &t), at: [primed[j], indices[j], entries2[j], results2[j], results[j]],
                                        premises: [second, try symmetric(above, &t)], in: &t)
            }
            let pair = try eliminated(try base.cite(.snocInj, in: &t), at: [prefixes[j], primed[j], indices[j], entries[j], entries2[j], results[j]],
                                      premises: [tuples[j], tuples2[j], try snoc(a, j, &t), second], in: &t)
            equalities.insert(try t.intern(.folAndElimR(pair)), at: 0)
            above = try t.intern(.folAndElimL(pair))
        }
        var conclusion = equalities[n - 1]
        for j in (0..<(n - 1)).reversed() { conclusion = try t.intern(.folAndIntro(equalities[j], conclusion)) }
        return try f.close(conclusion, in: &t)
    }

    private func spine(_ a: Opened, _ b: Opened, _ n: Int, _ f: Frame, _ t: inout Table) throws -> [NodeID] {
        var found = [try zeroUnique(a, b, f, &t)]
        for j in 0..<(n - 1) {
            let (index, index2) = (j == 0 ? a.witnesses[0] : a.witnesses[2 * j - 1], j == 0 ? b.witnesses[0] : b.witnesses[2 * j - 1])
            let (next, next2) = (a.witnesses[1 + 2 * j], b.witnesses[1 + 2 * j])
            let (i, i2, m, m2) = (try f.variable(index, in: &t), try f.variable(index2, in: &t), try f.variable(next, in: &t),
                                  try f.variable(next2, in: &t))
            let moved = try eliminated(try base.cite(.nsuccCONG, in: &t), at: [i2, i, m2],
                                       premises: [try symmetric(found[j], &t), try f.proof(b.constraints[1 + 2 * j], in: &t)], in: &t)
            found.append(try eliminated(try base.cite(.nsuccUNIQ, in: &t), at: [i, m, m2],
                                        premises: [try f.proof(a.constraints[1 + 2 * j], in: &t), moved], in: &t))
        }
        return found
    }

    private func zeroUnique(_ a: Opened, _ b: Opened, _ f: Frame, _ t: inout Table) throws -> NodeID {
        try eliminated(try base.cite(.zeroUNIQ, in: &t), at: [try f.variable(a.witnesses[0], in: &t), try f.variable(b.witnesses[0], in: &t)],
                       premises: [try f.proof(a.constraints[0], in: &t), try f.proof(b.constraints[0], in: &t)], in: &t)
    }

    private func snocUnique(_ prefix: NodeID, _ index: NodeID, _ entry: NodeID, _ p: NodeID, _ q: NodeID,
                            _ t: inout Table) throws -> NodeID {
        guard case let .folPred(_, ps)? = t.conclusion(of: p).map({ t[$0] }), case let .folPred(_, qs)? = t.conclusion(of: q).map({ t[$0] })
        else { throw TableError.principalConnective(p) }
        let moved = try eliminated(try base.cite(.snocCONG, in: &t), at: [qs[0], ps[0], qs[1], ps[1], qs[2], ps[2], qs[3]],
                                   premises: [try symmetric(prefix, &t), try symmetric(index, &t), try symmetric(entry, &t), q], in: &t)
        return try eliminated(try base.cite(.snocUNIQ, in: &t), at: [ps[0], ps[1], ps[2], ps[3], qs[3]], premises: [p, moved], in: &t)
    }

    private func emptyTuple(_ e: NodeID, _ a: Opened, _ f: Frame, _ t: inout Table) throws -> NodeID {
        let empty = try t.intern(.folIffElimL(try eliminated(try base.cite(.zeroDef, in: &t), at: [e], in: &t), try f.proof(a.constraints[0], in: &t)))
        return try eliminated(try base.cite(.tupleZero, in: &t), at: [e], premises: [empty], in: &t)
    }

    private func symmetric(_ p: NodeID, _ t: inout Table) throws -> NodeID {
        guard case let .folPred(.base("eq"), xs)? = t.conclusion(of: p).map({ t[$0] }) else { throw TableError.principalConnective(p) }
        return try eliminated(try base.cite(.eqSymm, in: &t), at: xs, premises: [p], in: &t)
    }

    private func reflexive(_ x: NodeID, _ t: inout Table) throws -> NodeID {
        try eliminated(try base.cite(.eqRefl, in: &t), at: [x], in: &t)
    }
}

private func eq(_ a: NodeID, _ b: NodeID, _ t: inout Table) throws -> NodeID { try t.intern(.folPred(.base("eq"), args: [a, b])) }
