import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

/// DESIGN "Proof size": an instance at a compound term, and Pure's equality at objects, measured by what their proofs
/// cite and how many distinct steps they hold.
private struct Sized {
    var t = Table()

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func x(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, i))
    }

    mutating func zero() throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.zero)), i, args: []))
    }

    mutating func pow(_ a: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.pow)), fn(i, i), args: [a]))
    }

    mutating func mem(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [a, b]))
    }

    mutating func eq(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try t.equation(i, a, b)
    }

    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folImplies(a, b))
    }

    /// `P₁ ⟹ … ⟹ Pₙ ⟹ C`, proved by `body` under the premises as hypotheses, innermost last.
    mutating func under(_ premises: [NodeID], _ body: (inout Sized, [NodeID]) throws -> NodeID) throws -> Statement {
        let hs = try premises.indices.map { k in try n(.hyp(premises.count - 1 - k, premises[k])) }
        var proof = try body(&self, hs)
        guard var root = t.conclusion(of: proof) else { throw TableError.expectedStep(proof) }
        for p in premises.reversed() {
            root = try n(.folImplies(p, root))
            proof = try n(.folImpliesIntro(p, body: proof))
        }
        return Statement(name: "T.sized", root: root, proof: proof, theory: "Test")
    }
}

private struct Lowered {
    let unit: Unit
    let proof: NodeID
}

private func lowered(_ s: Sized, _ statement: Statement) throws -> Lowered {
    var t = s.t
    let b = try base(in: &t)
    var unit = Unit(table: t, statements: [statement])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
    guard let proof = unit.statements.first(where: { $0.name == statement.name })?.proof else {
        throw TableError.expectedStep(statement.root)
    }
    return Lowered(unit: unit, proof: proof)
}

private func cited(_ l: Lowered) -> (lemmas: [String], base: Set<String>) {
    var lemmas = Set<String>()
    var claims = Set<String>()
    var seen = Set<NodeID>()
    var stack = [l.proof]
    while let id = stack.popLast() {
        guard seen.insert(id).inserted else { continue }
        switch l.unit.table[id] {
        case .use(.lemma(let lemma), _, _): lemmas.insert(lemma.name)
        case .use(.base(let name), _, _): claims.insert(name)
        default: l.unit.table[id].forEachChild { c, _ in stack.append(c) }
        }
    }
    return (lemmas.sorted(), claims)
}

private func steps(_ l: Lowered) -> Int {
    var seen = Set<NodeID>()
    var stack = [l.proof]
    while let id = stack.popLast() {
        guard seen.insert(id).inserted else { continue }
        l.unit.table[id].forEachChild { c, _ in if l.unit.table.conclusion(of: c) != nil { stack.append(c) } }
    }
    return seen.count
}

private func kinds(_ names: [String]) -> [String] {
    names.map { $0.prefix(while: { $0 != "_" }) + "_" }
}

/// `(∀x. x ∈ x) ⟹ Pow(0) ∈ Pow(0)`: the instance is `forall_elim` at `Pow(0)`'s value, the instantiated formula meeting
/// it through its lemma; no UNIQ, no membership congruence at the site.
@Test
func anInstanceAtACompoundTermInAPositivePositionClosesWithTheTermsPieces() throws {
    var s = Sized()
    let premise = try s.n(.ifolAll(i, body: try s.mem(try s.x(0), try s.x(0))))
    let a = try s.pow(try s.zero())
    let statement = try s.under([premise]) { s, hs in try s.n(.isaAllElim(hs[0], a)) }
    let l = try lowered(s, statement)
    let (lemmas, claims) = cited(l)
    #expect(Set(kinds(lemmas)).isSubset(of: ["EX_", "MEET_"]))
    #expect(steps(l) <= 60, "468 steps when each occurrence was converted in both directions")
    #expect(claims.isDisjoint(with: ["cong_elem_l", "cong_elem_r"]))
}

/// `(∀x. x ∈ x ⟶ ⊥) ⟹ (Pow(0) ∈ Pow(0) ⟶ ⊥)`: the negative atom too, only through the formula's lemma.
@Test
func anInstanceAtACompoundTermInANegativePositionOpensByUniq() throws {
    var s = Sized()
    let bottom = try s.n(.folBottom)
    let premise = try s.n(.ifolAll(i, body: try s.imp(try s.mem(try s.x(0), try s.x(0)), bottom)))
    let a = try s.pow(try s.zero())
    let statement = try s.under([premise]) { s, hs in try s.n(.isaAllElim(hs[0], a)) }
    let l = try lowered(s, statement)
    let (lemmas, _) = cited(l)
    #expect(Set(kinds(lemmas)).isSubset(of: ["EX_", "MEET_"]))
    #expect(steps(l) <= 60, "477 steps when each occurrence was converted in both directions")
}

/// `transitive` at `i` between compound terms: `eq_trans` at the values, nothing else at the site.
@Test
func transitiveAtIBetweenCompoundTermsIsProvedOnValues() throws {
    var s = Sized()
    let a = try s.pow(try s.zero())
    let b = try s.pow(a)
    let c = try s.pow(b)
    let statement = try s.under([try s.eq(a, b), try s.eq(b, c)]) { s, hs in
        try s.n(.isaTransitive(i, hs[0], hs[1]))
    }
    let l = try lowered(s, statement)
    let (lemmas, _) = cited(l)
    #expect(Set(kinds(lemmas)).isSubset(of: ["EX_", "MEET_"]))
    #expect(steps(l) <= 70, "2,127 steps as three instances of eq_trans at compound terms")
}

/// `symmetric` and `reflexive` at `i`: `eq_symm`, `eq_refl` at the values.
@Test
func symmetricAndReflexiveAtIBetweenCompoundTermsAreProvedOnValues() throws {
    var s = Sized()
    let a = try s.pow(try s.zero())
    let b = try s.pow(a)
    let symmetric = try s.under([try s.eq(a, b)]) { s, hs in try s.n(.isaSymmetric(i, hs[0])) }
    let sl = try lowered(s, symmetric)
    #expect(Set(kinds(cited(sl).lemmas)).isSubset(of: ["EX_", "MEET_"]))
    #expect(steps(sl) <= 50, "1,045 steps as two instances of eq_symm at compound terms")
    var r = Sized()
    let reflexive = try r.under([]) { r, _ in try r.n(.isaReflexive(try r.pow(try r.zero()))) }
    let rl = try lowered(r, reflexive)
    #expect(Set(kinds(cited(rl).lemmas)).isSubset(of: ["EX_", "MEET_"]))
    #expect(steps(rl) <= 40, "456 steps as an instance of eq_refl at a compound term")
}

/// `combination` at an object argument: the premise at `a`, then its Leibniz lemma moving `a` to `b`.
@Test
func combinationAtAnObjectArgumentIsProvedOnValues() throws {
    var s = Sized()
    let a = try s.pow(try s.zero())
    let b = try s.pow(a)
    let f = try s.n(.isaAbs(i, body: try s.pow(try s.x(0))))
    let premise = try s.t.equation(fn(i, i), f, f)
    let statement = try s.under([premise, try s.eq(a, b)]) { s, hs in
        try s.n(.isaCombination(fn(i, i), hs[0], hs[1]))
    }
    let l = try lowered(s, statement)
    #expect(Set(kinds(cited(l).lemmas)).isSubset(of: ["EX_", "MEET_", "SUBST_"]))
    #expect(steps(l) <= 120, "2,432 steps as three instances at compound terms")
}

/// DESIGN "Linear proof size": a chain of `n` equations between terms `n` deep, its proof's steps — the theorem's and
/// every lemma's it cites — growing linearly with `n`.
@Test
func aChainOfEquationsGrowsLinearly() throws {
    func written(_ n: Int) throws -> Int {
        var s = Sized()
        var terms = [try s.zero()]
        for _ in 0..<n { terms.append(try s.pow(terms[terms.count - 1])) }
        let premises = try (0..<n).map { try s.eq(terms[$0], terms[$0 + 1]) }
        let statement = try s.under(premises) { s, hs in
            var p = hs[0]
            for h in hs.dropFirst() { p = try s.n(.isaTransitive(i, p, h)) }
            return p
        }
        let l = try lowered(s, statement)
        return everyStep(l)
    }
    let small = try written(4)
    let large = try written(16)
    #expect(Double(large) / Double(small) <= 4 * 1.5, "\(small) steps at 4, \(large) at 16")
}

/// Every distinct step of the theorem's proof and of every lemma's proof the unit holds.
private func everyStep(_ l: Lowered) -> Int {
    var seen = Set<NodeID>()
    var stack = l.unit.statements.compactMap(\.proof)
    while let id = stack.popLast() {
        guard seen.insert(id).inserted else { continue }
        l.unit.table[id].forEachChild { c, _ in if l.unit.table.conclusion(of: c) != nil { stack.append(c) } }
    }
    return seen.count
}

/// `⋀P. (∀x. x ∈ x) ⟹ (Pow(0) ∈ Pow(0) ⟹ P) ⟹ P`, a schema whose proof holds `Pow(0)`'s value, and a theorem citing it
/// at its own letter: each keeps its letter on its spine, the values met and fixed below it (DESIGN "Linear proof
/// size", 6).
@Test
func aSchemaHoldingACompoundTermKeepsItsLetterAboveItsValues() throws {
    var s = Sized()
    let letter = try s.n(.isaBound(0, o))
    let every = try s.n(.ifolAll(i, body: try s.mem(try s.x(0), try s.x(0))))
    let a = try s.pow(try s.zero())
    let premise = try s.imp(try s.mem(a, a), letter)
    let root = try s.n(.ifolAll(o, body: try s.imp(every, try s.imp(premise, letter))))
    let body = try s.n(.folImpliesElim(try s.n(.hyp(0, premise)), try s.n(.isaAllElim(try s.n(.hyp(1, every)), a))))
    let proof = try s.n(.isaAllIntro(o, body: try s.n(.folImpliesIntro(
        every,
        body: try s.n(.folImpliesIntro(premise, body: body)),
    ))))
    let schema = Statement(name: "T.schema", root: root, proof: proof, theory: "Test")
    let cited = try s.n(.isaAllElim(try s.n(.use(.theorem("T.schema"), [], root)), letter))
    let user = Statement(name: "T.user", root: root, proof: try s.n(.isaAllIntro(o, body: cited)), theory: "Test")
    var t = s.t
    let b = try base(in: &t)
    var unit = Unit(table: t, statements: [schema, user])
    try pipeline(b).run(&unit)
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
