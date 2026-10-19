import IR
import Testing
@testable import Lowering

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private let predicate = fn(i, o)
private let quantifier = fn(i, fn(predicate, o))
private let relation = fn(i, fn(i, o))
private let replace = fn(i, fn(relation, i))

/// Isabelle's `Ball`, `Bex` and `⊆`, defined as `ZF_Base` defines them, and the axioms' statements over them, each
/// closed in the export's order: the free variables as they first occur.
private struct Fixture {
    var l = LogicTable()
    let ball = Defined(.zf, "ZF_Base.Ball", .object)
    let bex = Defined(.zf, "ZF_Base.Bex", .object)
    let subset = Defined(.zf, "ZF_Base.Subset", .object)
    let succ = Defined(.zf, "ZF_Base.succ", .object)

    mutating func definitions() throws -> [Definition] {
        let x = try l.bound(0, i)
        let p = try l.bound(1, predicate)
        let a = try l.bound(2, i)
        let px = try l.t.intern(.isaVarApp(head: p, args: [x]))
        let ballBody = try l.all(i, try l.imp(try l.mem(x, a), px))
        let bexBody = try l.t.intern(.ifolEx(i, body: try l.and(try l.mem(x, a), px)))
        let subsetBody = try ball(try l.bound(1, i), try l.lam(i, try l.mem(x, try l.bound(1, i))))
        let union = try l.const(.primitive(.zf(.union)), fn(i, i), try l.bound(0, i))
        return [
            try l.definition(ball, quantifier, parameters: 2, try l.lam(i, try l.lam(predicate, ballBody))),
            try l.definition(bex, quantifier, parameters: 2, try l.lam(i, try l.lam(predicate, bexBody))),
            try l.definition(subset, relation, parameters: 2, try l.lam(i, try l.lam(i, subsetBody))),
            try l.definition(succ, fn(i, i), parameters: 1, try l.lam(i, union)),
        ]
    }

    mutating func ball(_ a: NodeID, _ p: NodeID) throws -> NodeID {
        try l.const(.defined(ball), quantifier, a, p)
    }

    mutating func bex(_ a: NodeID, _ p: NodeID) throws -> NodeID {
        try l.const(.defined(bex), quantifier, a, p)
    }

    mutating func subset(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try l.const(.defined(subset), relation, a, b)
    }

    mutating func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try l.and(try l.imp(a, b), try l.imp(b, a))
    }

    /// `A ∈ ⋃(C) ⟷ (∃B∈C. A ∈ B)`
    mutating func unionIff() throws -> NodeID {
        let a = try l.bound(1, i)
        let c = try l.bound(0, i)
        let inUnion = try l.mem(a, try l.const(.primitive(.zf(.union)), fn(i, i), c))
        let some = try bex(c, try l.lam(i, try l.mem(try l.bound(2, i), try l.bound(0, i))))
        return try l.all(i, try l.all(i, try iff(inUnion, some)))
    }

    /// `A ∈ Pow(B) ⟷ A ⊆ B`
    mutating func powIff() throws -> NodeID {
        let a = try l.bound(1, i)
        let b = try l.bound(0, i)
        let inPow = try l.mem(a, try l.const(.primitive(.zf(.pow)), fn(i, i), b))
        return try l.all(i, try l.all(i, try iff(inPow, try subset(a, b))))
    }

    /// `A = B ⟷ A ⊆ B ∧ B ⊆ A`
    mutating func extensionIff() throws -> NodeID {
        let a = try l.bound(1, i)
        let b = try l.bound(0, i)
        let both = try l.and(try subset(a, b), try subset(b, a))
        return try l.all(i, try l.all(i, try iff(try l.equal(i, a, b), both)))
    }

    /// `A = 0 ∨ (∃x∈A. ∀y∈x. y ∉ A)`
    mutating func foundation() throws -> NodeID {
        let a = try l.bound(0, i)
        let empty = try l.equal(i, a, try l.const(.primitive(.zf(.zero)), i))
        let notIn = try l.imp(try l.mem(try l.bound(0, i), try l.bound(2, i)), try l.bottom())
        let minimal = try l.lam(i, try ball(try l.bound(0, i), try l.lam(i, notIn)))
        return try l.all(i, try l.t.intern(.folOr(empty, try bex(a, minimal))))
    }

    /// `(∀x∈A. ∀y z. P(x, y) ∧ P(x, z) ⟶ y = z) ⟹ b ∈ PrimReplace(A, P) ⟷ (∃x∈A. P(x, b))`
    mutating func replacement() throws -> NodeID {
        let applied = { (f: NodeID, x: NodeID, y: NodeID, l: inout LogicTable) throws -> NodeID in
            try l.t.intern(.isaVarApp(head: f, args: [x, y]))
        }
        let functional = try l.lam(i, try l.all(i, try l.all(i, try l.imp(
            try l.and(
                try applied(try l.bound(4, relation), try l.bound(2, i), try l.bound(1, i), &l),
                try applied(try l.bound(4, relation), try l.bound(2, i), try l.bound(0, i), &l),
            ),
            try l.equal(i, try l.bound(1, i), try l.bound(0, i)),
        ))))
        let a = try l.bound(2, i)
        let b = try l.bound(0, i)
        let eta = try l.lam(
            i,
            try l.lam(i, try applied(try l.bound(3, relation), try l.bound(1, i), try l.bound(0, i), &l)),
        )
        let inImage = try l.mem(b, try l.const(.primitive(.zf(.primReplace)), replace, a, eta))
        let some = try bex(
            a,
            try l.lam(i, try applied(try l.bound(2, relation), try l.bound(0, i), try l.bound(1, i), &l)),
        )
        let body = try l.imp(try ball(a, functional), try iff(inImage, some))
        return try l.all(i, try l.all(relation, try l.all(i, body)))
    }

    /// `upair.succ_iff`: `i ∈ succ(j) ⟷ i = j ∨ i ∈ j`, `i` then `j` as they first occur.
    mutating func succIff() throws -> NodeID {
        let x = try l.bound(1, i)
        let y = try l.bound(0, i)
        let member = try l.mem(x, try l.const(.defined(succ), fn(i, i), y))
        let either = try l.t.intern(.folOr(try l.equal(i, x, y), try l.mem(x, y)))
        return try l.all(i, try l.all(i, try iff(member, either)))
    }

    /// `0 ∈ Inf ∧ (∀y∈Inf. succ(y) ∈ Inf)`
    mutating func infinity() throws -> NodeID {
        let inf = try l.const(.primitive(.zf(.inf)), i)
        let zero = try l.const(.primitive(.zf(.zero)), i)
        let next = try l.mem(try l.const(.defined(succ), fn(i, i), try l.bound(0, i)), inf)
        return try l.and(try l.mem(zero, inf), try ball(inf, try l.lam(i, next)))
    }
}

private func lowered(_ axiom: Axiom.ZF, _ build: (inout Fixture) throws -> NodeID) throws -> IR.Unit {
    var f = Fixture()
    let definitions = try f.definitions()
    let root = try build(&f)
    let proof = try f.l.t.intern(.use(.axiom(.zf(axiom)), [], root))
    var t = f.l.t
    let b = try base(in: &t)
    var unit = IR.Unit(
        table: t,
        statements: [Statement(name: axiom.rawValue, root: root, proof: proof, theory: "ZF_Base")],
        definitions: definitions,
    )
    try pipeline(b).run(&unit)
    return unit
}

private func checked(_ unit: IR.Unit, _ axiom: Axiom.ZF) throws {
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    #expect(Set([axiom.rawValue, axiom.rawValue + "_AXIOM"]).isSubset(of: Set(unit.statements.map(\.name))))
    try kernelChecks(unit)
}

/// `Union_iff`'s lemma reads base's statement back: `⋃`'s class at its tuple, `Bex` by its pointwise definition.
@Test
func unionIffIsReadFromBasesStatement() throws {
    try checked(try lowered(.unionIff) { try $0.unionIff() }, .unionIff)
}

/// `Pow_iff`: `Pow`'s class at its tuple, `⊆` through `Ball`.
@Test
func powIffIsReadFromBasesStatement() throws {
    try checked(try lowered(.powIff) { try $0.powIff() }, .powIff)
}

/// `extension`: no primitive's class; `⊆` read twice over, by its definition and then `Ball`'s.
@Test
func extensionIsReadFromBasesStatement() throws {
    try checked(try lowered(.extension) { try $0.extensionIff() }, .extension)
}

/// `foundation`: `0` in base's words already; `Bex` and the `Ball` inside its λ.
@Test
func foundationIsReadFromBasesStatement() throws {
    try checked(try lowered(.foundation) { try $0.foundation() }, .foundation)
}

/// `replacement`: `PrimReplace`'s slot class kept as the statement names it, its class read at its tuple.
@Test
func replacementIsReadFromBasesStatement() throws {
    try checked(try lowered(.replacement) { try $0.replacement() }, .replacement)
}

/// `infinity` reads `succ(y)` by `upair.succ_iff`; a unit without it refuses the lemma citing it, and the theorem with
/// it.
@Test
func infinityWithoutSuccIffIsRefusedCitingIt() throws {
    let unit = try lowered(.infinity) { try $0.infinity() }
    let refusals = Dictionary(uniqueKeysWithValues: unit.refused.map { ($0.name, $0.refusal) })
    #expect(refusals["ZF_Base.infinity_AXIOM"] == .cites("upair.succ_iff"))
    #expect(refusals["ZF_Base.infinity"] == .cites("ZF_Base.infinity_AXIOM"))
}

/// `infinity` reads `succ(y) ∈ Inf` by the theorem stating `succ`'s members: the proof concludes the lemma's statement,
/// each hypothesis its binder's, through Fol, and the lemmas it cites are proved in turn. The kernel sees it in the ZF
/// session, where `upair.succ_iff` is proved; a fixture's has no proof to give.
@Test
func infinityReadsSuccByTheTheoremStatingItsMembers() throws {
    var f = Fixture()
    let definitions = try f.definitions()
    let stated = try f.infinity()
    let succIff = try f.succIff()
    var t = f.l.t
    let b = try base(in: &t)
    let statement = try formula(stated, .statement, in: &t)
    let members = try formula(succIff, .statement, in: &t)
    let fact = AxiomFact(axiom: .infinity, stated: stated, statement: statement)
    let answer = try AxiomProver(base: b).prove(
        Lemma(fact),
        statement,
        definitions,
        ["upair.succ_iff": members],
        in: &t,
    )
    guard case .proof(let p) = answer else {
        Issue.record("not proved: \(answer)")
        return
    }
    #expect(t.conclusion(of: p) == statement)
    #expect(try misscoped(p, in: t).isEmpty)
    let lowered = try Fol(base: b).run([statement, p], [], in: &t)
    #expect(t.conclusion(of: lowered[1]) == lowered[0])
    try legalize(lowered[1], in: t)
    var requests = [(Lemma, NodeID)]()
    var seen = Set<NodeID>()
    var work = [p]
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case .use(.lemma(let l), _, let root) = t[id] { requests.append((l, root)) }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    let (_, unbuilt) = try proveAll(requests, definitions, in: &t)
    #expect(unbuilt.isEmpty)
}

/// `Union_iff` with its bounded `∃` written out, so no predicate unfolds at a λ: `⋃`'s class read at its tuple against
/// NBG's words — the named form's pieces opened by their existence one way, fixed and met by UNIQ the other.
@Test
func unionIffWithItsBoundedExistentialWrittenOutIsReadByItsClass() throws {
    var f = Fixture()
    let definitions = try f.definitions()
    let a = try f.l.bound(1, i)
    let c = try f.l.bound(0, i)
    let inUnion = try f.l.mem(a, try f.l.const(.primitive(.zf(.union)), fn(i, i), c))
    let both = try f.l.and(
        try f.l.mem(try f.l.bound(0, i), try f.l.bound(1, i)),
        try f.l.mem(try f.l.bound(2, i), try f.l.bound(0, i)),
    )
    let some = try f.l.t.intern(.ifolEx(i, body: both))
    let stated = try f.l.all(i, try f.l.all(i, try f.iff(inUnion, some)))
    var t = f.l.t
    let statement = try formula(stated, .statement, in: &t)
    let fact = AxiomFact(axiom: .unionIff, stated: stated, statement: statement)
    let (proved, unbuilt) = try proveAll([(Lemma(fact), statement)], definitions, in: &t)
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, in: &t)
}

/// `foundation` with its bounded quantifiers written out: `A = 0`'s named form, `∀v. 0(v) → A = v`, read against NBG's
/// `∃v. 0(v) ∧ A = v` — `0`'s value opened by its EX one way, met by its UNIQ the other.
@Test
func foundationWithItsBoundedQuantifiersWrittenOutReadsZeroByItsValue() throws {
    var f = Fixture()
    let definitions = try f.definitions()
    let empty = try f.l.equal(i, try f.l.bound(0, i), try f.l.const(.primitive(.zf(.zero)), i))
    let notIn = try f.l.imp(
        try f.l.mem(try f.l.bound(0, i), try f.l.bound(1, i)),
        try f.l.imp(try f.l.mem(try f.l.bound(0, i), try f.l.bound(2, i)), try f.l.bottom()),
    )
    let minimal = try f.l.and(try f.l.mem(try f.l.bound(0, i), try f.l.bound(1, i)), try f.l.all(i, notIn))
    let stated = try f.l.all(i, try f.l.t.intern(.folOr(empty, try f.l.t.intern(.ifolEx(i, body: minimal)))))
    var t = f.l.t
    let statement = try formula(stated, .statement, in: &t)
    let fact = AxiomFact(axiom: .foundation, stated: stated, statement: statement)
    let (proved, unbuilt) = try proveAll([(Lemma(fact), statement)], definitions, in: &t)
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, in: &t)
}

/// `infinity` with its bounded `∀` written out: `0 ∈ Inf` by the constants' values, `succ(y) ∈ Inf` by the theorem
/// stating `succ`'s members, `Inf` again by its value — the proof concludes the lemma's statement and its lemmas are
/// proved in turn.
@Test
func infinityWithItsBoundedForallWrittenOutReadsSuccByItsMembers() throws {
    var f = Fixture()
    let definitions = try f.definitions()
    let inf = try f.l.const(.primitive(.zf(.inf)), i)
    let zero = try f.l.const(.primitive(.zf(.zero)), i)
    let next = try f.l.mem(try f.l.const(.defined(f.succ), fn(i, i), try f.l.bound(0, i)), inf)
    let stated = try f.l.and(
        try f.l.mem(zero, inf),
        try f.l.all(i, try f.l.imp(try f.l.mem(try f.l.bound(0, i), inf), next)),
    )
    let succIff = try f.succIff()
    var t = f.l.t
    let b = try base(in: &t)
    let statement = try formula(stated, .statement, in: &t)
    let members = try formula(succIff, .statement, in: &t)
    let fact = AxiomFact(axiom: .infinity, stated: stated, statement: statement)
    let answer = try AxiomProver(base: b).prove(
        Lemma(fact),
        statement,
        definitions,
        ["upair.succ_iff": members],
        in: &t,
    )
    guard case .proof(let p) = answer else {
        Issue.record("not proved: \(answer)")
        return
    }
    #expect(t.conclusion(of: p) == statement)
    #expect(try misscoped(p, in: t).isEmpty)
    let lowered = try Fol(base: b).run([statement, p], [], in: &t)
    #expect(t.conclusion(of: lowered[1]) == lowered[0])
    try legalize(lowered[1], in: t)
    var requests = [(Lemma, NodeID)]()
    var seen = Set<NodeID>()
    var work = [p]
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case .use(.lemma(let l), _, let root) = t[id] { requests.append((l, root)) }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    let (_, unbuilt) = try proveAll(requests, definitions, in: &t)
    #expect(unbuilt.isEmpty)
}
