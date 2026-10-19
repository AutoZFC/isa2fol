import IR

func tuple(_ xs: [NodeID], _ target: NodeID, in t: inout Table) throws -> NodeID {
    guard let last = xs.last else { return try t.intern(.folPred(.base("zero"), args: [target])) }
    var c = Chain()
    let empty = c.bind(.set)
    c.constrain(empty, try c.predicate(.base("zero"), [empty], in: &t))
    var index = empty
    var prefix = empty
    for x in xs.dropLast() {
        let next = c.bind(.set)
        c.constrain(next, try c.predicate(.base("nsucc"), [index, next], in: &t))
        let grown = c.bind(.set)
        c.constrain(grown, try c.predicate(.base("snoc"), [prefix, index, .outer(x), grown], in: &t))
        (index, prefix) = (next, grown)
    }
    return try c.formula(try c.predicate(.base("snoc"), [prefix, index, .outer(last), .outer(target)], in: &t), in: &t)
}

@frozen
public enum TupleError: Error, Equatable, Sendable {
    case notMine(String)
    case misproved(String)
}

func tupleBinders(_ n: Int) -> [Binder] {
    n == 0 ? [] : Array(repeating: .set, count: 2 * n - 1)
}

/// A tuple's pieces, held: the empty set, each index after it, each prefix — `prefixes[j - 1]` is `p_j`, with
/// `snoc(p_{j-1}, n_{j-1}, x_j, p_j)` — and the last `snoc` into the tuple. The index and the prefix before the first
/// are the empty set.
struct TupleChain {
    let zero: (level: Int, fact: Fact)
    let indices: [(level: Int, fact: Fact)]
    let prefixes: [(level: Int, fact: Fact)]
    let last: Fact

    func index(_ j: Int) -> Int {
        j == 0 ? zero.level : indices[j - 1].level
    }

    func prefix(_ j: Int) -> Int {
        j == 0 ? zero.level : prefixes[j - 1].level
    }
}

/// `tuple(x⃗, τ)`, S1's universal tuple, at a chain of its pieces: each binder fixed and its constraint assumed, its
/// piece the chain's by uniqueness, the last `snoc` carried to it.
func universalTuple(
    _ entries: [Int],
    _ tau: Int,
    _ chain: TupleChain,
    base: Base,
    in s: Scope,
    _ t: inout Table,
) throws -> NodeID {
    let m = entries.count
    var f = Frame(s)
    let target = try tuple(try entries.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t)
    var rest = target
    var restScope = f.scope
    var levels = [Int]()
    var hyps = [Int]()
    while true {
        let here = try lifted(rest, from: restScope, to: f.scope, in: &t)
        guard case .ifolAll(.i, let body) = t[here], case .folImplies(let c, let after) = t[body] else { break }
        levels.append(f.fix(.i))
        hyps.append(f.assume(c))
        rest = after
        restScope = f.scope
    }
    let index = { (j: Int) -> Int in j == 0 ? levels[0] : levels[2 * j - 1] }
    let prefix = { (j: Int) -> Int in j == 0 ? levels[0] : levels[2 * j] }
    var indexEqual = try eliminated(
        try base.cite(.zeroUNIQ, in: &t),
        at: [try f.variable(levels[0], in: &t), try f.variable(chain.zero.level, in: &t)],
        premises: [try f.hypothesis(hyps[0], in: &t), try f.proof(chain.zero.fact, in: &t)],
        in: &t,
    )
    var prefixEqual = indexEqual
    for j in 1..<m {
        let next = try eliminated(
            try base.cite(.nsuccEq, in: &t),
            at: try [index(j - 1), chain.index(j - 1), index(j), chain.index(j)].map { try f.variable($0, in: &t) },
            premises: [
                indexEqual,
                try f.hypothesis(hyps[2 * j - 1], in: &t),
                try f.proof(chain.indices[j - 1].fact, in: &t),
            ],
            in: &t,
        )
        prefixEqual = try eliminated(
            try base.cite(.snocEQ, in: &t),
            at: try [
                prefix(j - 1),
                chain.prefix(j - 1),
                index(j - 1),
                chain.index(j - 1),
                entries[j - 1],
                prefix(j),
                chain.prefix(j),
            ].map { try f.variable($0, in: &t) },
            premises: [
                prefixEqual,
                indexEqual,
                try f.hypothesis(hyps[2 * j], in: &t),
                try f.proof(chain.prefixes[j - 1].fact, in: &t),
            ],
            in: &t,
        )
        indexEqual = next
    }
    let entry = try f.variable(entries[m - 1], in: &t)
    let core = try eliminated(
        try base.cite(.snocCONG, in: &t),
        at: try [chain.prefix(m - 1), prefix(m - 1), chain.index(m - 1), index(m - 1)].map {
            try f.variable($0, in: &t)
        } + [entry, entry, try f.variable(tau, in: &t)],
        premises: [
            try symmetric(prefixEqual, base, &t),
            try symmetric(indexEqual, base, &t),
            try eliminated(try base.cite(.eqRefl, in: &t), at: [entry], in: &t),
            try f.proof(chain.last, in: &t),
        ],
        in: &t,
    )
    guard t.conclusion(of: core) == (try lifted(rest, from: restScope, to: f.scope, in: &t)) else {
        throw TupleError.misproved("a tuple's formula")
    }
    return try f.close(core, in: &t)
}

private func symmetric(_ p: NodeID, _ base: Base, _ t: inout Table) throws -> NodeID {
    guard case .folPred(.base("eq"), let xs)? = t.conclusion(of: p).map({ t[$0] })
    else { throw TableError.principalConnective(p) }
    return try eliminated(try base.cite(.eqSymm, in: &t), at: xs, premises: [p], in: &t)
}

public struct TupleProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "tuple"

    public func owns(_ l: Lemma) -> Owned? {
        l.request is TupleFact ? .rule : nil
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _: [Definition],
        _: [String: NodeID],
        in t: inout Table,
    ) throws -> Proved {
        guard let f = l.request as? TupleFact else { throw TupleError.notMine(l.name) }
        let proof: NodeID =
            switch f.fact {
            case .existence: f.arity == 0 ? try base.cite(.zeroEX, in: &t) : try existence(f.arity, &t)
            case .uniqueness: f.arity == 0 ? try base.cite(.zeroUNIQ, in: &t) : try uniqueness(f.arity, &t)
            case .injectivity: try injectivity(f.arity, &t)
            case .congruence: try congruence(f.arity, &t)
            }
        guard t.conclusion(of: proof) == statement else { throw TupleError.misproved(l.name) }
        return .proof(proof)
    }

    public func defines(_: Defined) -> Owned? {
        nil
    }

    public func define(_ c: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        throw TupleError.notMine(c.name)
    }

    let base: Base

    /// The empty set, and each index after it, opened in `f`: an arity's index spine.
    private func spine(_ n: Int, _ f: inout Frame, _ t: inout Table) throws -> (zero: (Int, Int), indices: [(
        Int,
        Int,
    )]) {
        let (e, he) = try f.open(try base.cite(.zeroEX, in: &t), in: &t)
        var indices = [(Int, Int)]()
        var last = e
        for _ in 1..<n {
            let (next, hn) = try f.open(
                try eliminated(try base.cite(.nsuccEX, in: &t), at: [try f.variable(last, in: &t)], in: &t),
                in: &t,
            )
            indices.append((next, hn))
            last = next
        }
        return ((e, he), indices)
    }

    /// The prefixes of `xs` over a spine, opened in `f`: `p_j`, with `snoc(p_{j-1}, n_{j-1}, x_j, p_j)`, for every
    /// entry
    /// but the last.
    private func prefixes(
        _ xs: [Int],
        _ spine: (zero: (Int, Int), indices: [(Int, Int)]),
        _ f: inout Frame,
        _ t: inout Table,
    ) throws -> [(Int, Int)] {
        var found = [(Int, Int)]()
        var prefix = spine.zero.0
        for j in 0..<(xs.count - 1) {
            let index = j == 0 ? spine.zero.0 : spine.indices[j - 1].0
            let at = try [prefix, index, xs[j]].map { try f.variable($0, in: &t) }
            let (grown, hg) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
            found.append((grown, hg))
            prefix = grown
        }
        return found
    }

    /// `h`, a tuple of `ys`, at a spine and prefixes built for `xs`: its last `snoc`, each earlier one carried from
    /// `xs` to `ys` by `cong_snoc_v` at `eqs[j]`, `eq(x_j, y_j)`, where the two differ.
    private func core(
        _ h: NodeID,
        _ spine: (zero: (Int, Int), indices: [(Int, Int)]),
        _ prefixes: [(Int, Int)],
        _ xs: [Int],
        _ ys: [Int],
        _ eqs: [Int]?,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var p = try eliminated(
            h,
            at: [try f.variable(spine.zero.0, in: &t)],
            premises: [try f.hypothesis(spine.zero.1, in: &t)],
            in: &t,
        )
        for j in 1..<xs.count {
            let (index, hi) = spine.indices[j - 1]
            p = try eliminated(p, at: [try f.variable(index, in: &t)], premises: [try f.hypothesis(hi, in: &t)], in: &t)
            let (grown, hg) = prefixes[j - 1]
            var snoc = try f.hypothesis(hg, in: &t)
            if let eqs, xs[j - 1] != ys[j - 1] {
                let previous = j == 1 ? spine.zero.0 : prefixes[j - 2].0
                let previousIndex = j == 1 ? spine.zero.0 : spine.indices[j - 2].0
                let iff = try eliminated(
                    try base.cite(.congSnocV, in: &t),
                    at: try [previous, previousIndex, xs[j - 1], ys[j - 1], grown].map { try f.variable($0, in: &t) },
                    premises: [try f.hypothesis(eqs[j - 1], in: &t)],
                    in: &t,
                )
                snoc = try t.intern(.folIffElimL(iff, snoc))
            }
            p = try eliminated(p, at: [try f.variable(grown, in: &t)], premises: [snoc], in: &t)
        }
        return p
    }

    private func existence(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }
        let spine = try spine(n, &f, &t)
        let grown = try prefixes(xs, spine, &f, &t)
        let prefix = n == 1 ? spine.zero.0 : grown[n - 2].0
        let index = n == 1 ? spine.zero.0 : spine.indices[n - 2].0
        let at = try [prefix, index, xs[n - 1]].map { try f.variable($0, in: &t) }
        let (tau, ht) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
        let chain = TupleChain(
            zero: (spine.zero.0, .hypothesis(spine.zero.1)),
            indices: spine.indices.map { ($0.0, .hypothesis($0.1)) },
            prefixes: grown.map { ($0.0, .hypothesis($0.1)) },
            last: .hypothesis(ht),
        )
        let formula = try universalTuple(xs, tau, chain, base: base, in: f.scope, &t)
        let entries = try xs.map { try f.variable($0, in: &t) }
        let some = try t.intern(.ifolEx(.i, body: try tuple(
            try entries.map { try shift($0, by: 1, in: &t) },
            try t.intern(.isaBound(0, .i)),
            in: &t,
        )))
        return try f.close(try introduced(some, at: [try f.variable(tau, in: &t)], from: formula, in: &t), in: &t)
    }

    /// TUPLE_UNIQ: both tuples at one spine and the prefixes of the first, the second's entries carried by their
    /// equations; their last `snoc`s agree, so `snoc_UNIQ`.
    private func uniqueness(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }
        let ys = (0..<n).map { _ in f.fix(.i) }
        var equal = [Int]()
        for j in 0..<n {
            equal.append(f.assume(try eq(try f.variable(xs[j], in: &t), try f.variable(ys[j], in: &t), &t)))
        }
        let tau = f.fix(.i)
        let tau2 = f.fix(.i)
        let ht = f.assume(try tuple(try xs.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let ht2 = f.assume(try tuple(try ys.map { try f.variable($0, in: &t) }, try f.variable(tau2, in: &t), in: &t))
        let spine = try spine(n, &f, &t)
        let grown = try prefixes(xs, spine, &f, &t)
        let first = try core(try f.hypothesis(ht, in: &t), spine, grown, xs, xs, nil, f, &t)
        var second = try core(try f.hypothesis(ht2, in: &t), spine, grown, xs, ys, equal, f, &t)
        let prefix = n == 1 ? spine.zero.0 : grown[n - 2].0
        let index = n == 1 ? spine.zero.0 : spine.indices[n - 2].0
        let iff = try eliminated(
            try base.cite(.congSnocV, in: &t),
            at: try [prefix, index, xs[n - 1], ys[n - 1], tau2].map { try f.variable($0, in: &t) },
            premises: [try f.hypothesis(equal[n - 1], in: &t)],
            in: &t,
        )
        second = try t.intern(.folIffElimR(iff, second))
        let same = try eliminated(
            try base.cite(.snocUNIQ, in: &t),
            at: try [prefix, index, xs[n - 1], tau, tau2].map { try f.variable($0, in: &t) },
            premises: [first, second],
            in: &t,
        )
        return try f.close(same, in: &t)
    }

    /// TUPLE_INJ: both tuples at one spine, each at its own prefixes; `snoc_inj` from the last `snoc` down, each
    /// prefix carried to the other's by the equation the level above gives.
    private func injectivity(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }
        let ys = (0..<n).map { _ in f.fix(.i) }
        let tau = f.fix(.i)
        let ht = f.assume(try tuple(try xs.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let ht2 = f.assume(try tuple(try ys.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        let spine = try spine(n, &f, &t)
        let px = try prefixes(xs, spine, &f, &t)
        let py = try prefixes(ys, spine, &f, &t)
        let lastX = try core(try f.hypothesis(ht, in: &t), spine, px, xs, xs, nil, f, &t)
        let lastY = try core(try f.hypothesis(ht2, in: &t), spine, py, ys, ys, nil, f, &t)
        let v = { (w: Int, t: inout Table) throws -> NodeID in try f.variable(w, in: &t) }
        let index = { (j: Int) -> Int in j == 0 ? spine.zero.0 : spine.indices[j - 1].0 }
        let prefixX = { (j: Int) -> Int in j == 0 ? spine.zero.0 : px[j - 1].0 }
        let prefixY = { (j: Int) -> Int in j == 0 ? spine.zero.0 : py[j - 1].0 }
        let empty = try t.intern(.folIffElimL(
            try eliminated(try base.cite(.zeroDef, in: &t), at: [try v(spine.zero.0, &t)], in: &t),
            try f.hypothesis(spine.zero.1, in: &t),
        ))
        var tuplesX = [try eliminated(try base.cite(.tupleZero, in: &t), at: [try v(spine.zero.0, &t)], premises: [
            empty
        ], in: &t)]
        var tuplesY = [tuplesX[0]]
        for j in 0..<(n - 1) {
            let nsucc = try f.hypothesis(spine.indices[j].1, in: &t)
            tuplesX.append(try eliminated(
                try base.cite(.tupleSnoc, in: &t),
                at: try [prefixX(j), prefixX(j + 1), index(j), xs[j], index(j + 1)].map { try v($0, &t) },
                premises: [tuplesX[j], nsucc, try f.hypothesis(px[j].1, in: &t)],
                in: &t,
            ))
            tuplesY.append(try eliminated(
                try base.cite(.tupleSnoc, in: &t),
                at: try [prefixY(j), prefixY(j + 1), index(j), ys[j], index(j + 1)].map { try v($0, &t) },
                premises: [tuplesY[j], nsucc, try f.hypothesis(py[j].1, in: &t)],
                in: &t,
            ))
        }
        var equalities = [NodeID]()
        var above: NodeID?
        for j in (0..<n).reversed() {
            let result = j == n - 1 ? tau : prefixX(j + 1)
            let snocX = j == n - 1 ? lastX : try f.hypothesis(px[j].1, in: &t)
            var snocY = j == n - 1 ? lastY : try f.hypothesis(py[j].1, in: &t)
            if let above {
                snocY = try eliminated(
                    try base.cite(.snocResCong, in: &t),
                    at: try [prefixY(j), index(j), ys[j], prefixY(j + 1), prefixX(j + 1)].map { try v($0, &t) },
                    premises: [snocY, try symmetric(above, base, &t)],
                    in: &t,
                )
            }
            let pair = try eliminated(
                try base.cite(.snocInj, in: &t),
                at: try [prefixX(j), prefixY(j), index(j), xs[j], ys[j], result].map { try v($0, &t) },
                premises: [tuplesX[j], tuplesY[j], snocX, snocY],
                in: &t,
            )
            equalities.insert(try t.intern(.folAndElimR(pair)), at: 0)
            above = try t.intern(.folAndElimL(pair))
        }
        var conclusion = equalities[n - 1]
        for j in (0..<(n - 1)).reversed() { conclusion = try t.intern(.folAndIntro(equalities[j], conclusion)) }
        return try f.close(conclusion, in: &t)
    }

    /// TUPLE_CONG: the target's binders fixed and its constraints assumed, the hypothesis's eliminated at them, each
    /// entry carried by `cong_snoc_v` and its equation.
    private func congruence(_ n: Int, _ t: inout Table) throws -> NodeID {
        var f = Frame()
        let xs = (0..<n).map { _ in f.fix(.i) }
        let ys = (0..<n).map { _ in f.fix(.i) }
        let eqs = try (0..<n).map { j in
            f.assume(try eq(try f.variable(xs[j], in: &t), try f.variable(ys[j], in: &t), &t))
        }
        let tau = f.fix(.i)
        let h = f.assume(try tuple(try xs.map { try f.variable($0, in: &t) }, try f.variable(tau, in: &t), in: &t))
        var g = Frame(f.scope)
        var target = try tuple(try ys.map { try g.variable($0, in: &t) }, try g.variable(tau, in: &t), in: &t)
        var targetScope = g.scope
        var held = try g.hypothesis(h, in: &t)
        var heldScope = g.scope
        let moved = { (from: NodeID, to: NodeID, forward: Bool, g: Frame, t: inout Table) throws -> NodeID? in
            guard
                case .folPred(.base("snoc"), let a) = t[try formula(from, t)],
                case .folPred(.base("snoc"), let b) = t[to], a[2] != b[2]
            else { return nil }
            let (x, y) = forward ? (a[2], b[2]) : (b[2], a[2])
            guard
                let j = try xs.indices.first(where: {
                    try g.variable(xs[$0], in: &t) == x && g.variable(ys[$0], in: &t) == y
                })
            else { throw TupleError.misproved("TUPLE_CONG_\(n)") }
            let iff = try eliminated(
                try base.cite(.congSnocV, in: &t),
                at: [a[0], a[1], x, y, a[3]],
                premises: [try g.hypothesis(eqs[j], in: &t)],
                in: &t,
            )
            return try t.intern(forward ? .folIffElimL(iff, from) : .folIffElimR(iff, from))
        }
        while true {
            let here = try lifted(target, from: targetScope, to: g.scope, in: &t)
            guard case .ifolAll(.i, let body) = t[here] else { break }
            let w = g.fix(.i)
            guard case .folImplies(let c, let rest) = t[body] else { throw TupleError.misproved("TUPLE_CONG_\(n)") }
            let hc = g.assume(c)
            target = rest
            targetScope = g.scope
            let at = try t.intern(.isaAllElim(
                try lifted(held, from: heldScope, to: g.scope, in: &t),
                try g.variable(w, in: &t),
            ))
            guard case .folImplies(let wanted, _)? = t.conclusion(of: at).map({ t[$0] }) else {
                throw TupleError.misproved("TUPLE_CONG_\(n)")
            }
            let given = try g.hypothesis(hc, in: &t)
            held = try t.intern(.folImpliesElim(at, try moved(given, wanted, false, g, &t) ?? given))
            heldScope = g.scope
        }
        let have = try lifted(held, from: heldScope, to: g.scope, in: &t)
        let want = try lifted(target, from: targetScope, to: g.scope, in: &t)
        let core = try moved(have, want, true, g, &t) ?? have
        return try f.close(try g.close(core, in: &t), in: &t)
    }

    private func formula(_ p: NodeID, _ t: Table) throws -> NodeID {
        guard let c = t.conclusion(of: p) else { throw TableError.expectedStep(p) }
        return c
    }
}

private func eq(_ a: NodeID, _ b: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.folPred(
        .base("eq"),
        args: [a, b],
    ))
}
