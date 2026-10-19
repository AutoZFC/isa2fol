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

/// `(∀x. x ∈ x) ⟹ Pow(0) ∈ Pow(0)`: the atom is positive, so the instance closes `Pow(0)`'s pieces from its EX at both
/// occurrences — no UNIQ, no membership congruence.
@Test
func anInstanceAtACompoundTermInAPositivePositionClosesWithTheTermsPieces() throws {
    var s = Sized()
    let premise = try s.n(.ifolAll(i, body: try s.mem(try s.x(0), try s.x(0))))
    let a = try s.pow(try s.zero())
    let statement = try s.under([premise]) { s, hs in try s.n(.isaAllElim(hs[0], a)) }
    let l = try lowered(s, statement)
    let (lemmas, claims) = cited(l)
    #expect(kinds(lemmas) == ["EX_"])
    #expect(steps(l) <= 120, "468 steps when each occurrence was converted in both directions")
    #expect(claims.isDisjoint(with: ["cong_elem_l", "cong_elem_r"]))
}

/// `(∀x. x ∈ x ⟶ ⊥) ⟹ (Pow(0) ∈ Pow(0) ⟶ ⊥)`: the atom is negative, so the instance opens its namings and moves each
/// occurrence to the value by UNIQ.
@Test
func anInstanceAtACompoundTermInANegativePositionOpensByUniq() throws {
    var s = Sized()
    let bottom = try s.n(.folBottom)
    let premise = try s.n(.ifolAll(i, body: try s.imp(try s.mem(try s.x(0), try s.x(0)), bottom)))
    let a = try s.pow(try s.zero())
    let statement = try s.under([premise]) { s, hs in try s.n(.isaAllElim(hs[0], a)) }
    let l = try lowered(s, statement)
    let (lemmas, _) = cited(l)
    #expect(Set(kinds(lemmas)) == ["EX_", "UNIQ_"])
    #expect(steps(l) <= 260, "477 steps when each occurrence was converted in both directions")
}

/// `transitive` at `i` between compound terms: the premises' namings opened, the middle term's two namings related by
/// its UNIQ — no EX, no instance of `eq_trans` at a compound term.
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
    #expect(kinds(lemmas) == ["UNIQ_"])
    #expect(steps(l) <= 480, "2,127 steps as three instances of eq_trans at compound terms")
}

/// `symmetric` at `i` cites nothing: the premise's own pieces close the conclusion; `reflexive` only EX.
@Test
func symmetricAndReflexiveAtIBetweenCompoundTermsAreProvedOnValues() throws {
    var s = Sized()
    let a = try s.pow(try s.zero())
    let b = try s.pow(a)
    let symmetric = try s.under([try s.eq(a, b)]) { s, hs in try s.n(.isaSymmetric(i, hs[0])) }
    let sl = try lowered(s, symmetric)
    #expect(cited(sl).lemmas.isEmpty)
    #expect(steps(sl) <= 200, "1,045 steps as two instances of eq_symm at compound terms")
    var r = Sized()
    let reflexive = try r.under([]) { r, _ in try r.n(.isaReflexive(try r.pow(try r.zero()))) }
    let rl = try lowered(r, reflexive)
    #expect(kinds(cited(rl).lemmas) == ["EX_"])
    #expect(steps(rl) <= 110, "456 steps as an instance of eq_refl at a compound term")
}

/// `combination` at an object argument: `⟦a = b⟧` opened, the pointwise premise and the congruence at the values, the
/// conclusion closed with `a`'s and `b`'s pieces — no EX, no UNIQ.
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
    #expect(cited(l).lemmas.isEmpty)
    #expect(steps(l) <= 420, "2,432 steps as three instances at compound terms")
}
