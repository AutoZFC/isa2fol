import Testing
import IR
import Lowering

private let i = IRType.i
private let o = IRType.o
private let oo = IRType.fn(o, o)

private struct K {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, o)) }
    mutating func p(_ name: String) throws -> NodeID { try n(.folPred(.base(name), args: [])) }
    mutating func c(_ name: String) throws -> NodeID { try n(.isaConst(.declared(name), o, args: [])) }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
    mutating func and(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folAnd(a, b)) }
    mutating func or(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folOr(a, b)) }
    mutating func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folIff(a, b)) }
    mutating func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID { try n(.folImpliesIntro(a, body: body)) }
    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try n(.hyp(k, a)) }
    mutating func letters(_ k: Int, _ body: NodeID) throws -> NodeID {
        k == 0 ? body : try n(.ifolAll(o, body: try letters(k - 1, body)))
    }
    mutating func schema(_ b: Base, _ s: BaseStatement, _ instances: NodeID...) throws -> NodeID {
        var step = try b.cite(s, in: &t)
        for a in instances { step = try n(.folSchemaInst(step, a)) }
        return step
    }
}

private func holdsNothingLogicOwns(_ proof: NodeID, _ k: K, _ b: Base) -> Bool {
    patterns(under: [proof], in: k.t).allSatisfy { Logic(base: b).owns($0) == nil }
}

/// The 11 axioms of IFOL and FOL binding only propositions, each as the reader reads it after Expand (`⟹` and `⟶`
/// one node, `≡` at `o` read as `↔`, `¬P` unfolded to `P ⟶ ⊥`): a citation of each becomes the kernel's proof of the
/// cited statement, by ID, holding nothing Logic owns.
@Test func eachPropositionalAxiomIsTheKernelsProofOfItsStatement() throws {
    var k = K()
    let b = try base(in: &k.t)
    let bottom = try k.n(.folBottom)
    let p1 = try k.v(0)
    let (p2, q2) = (try k.v(1), try k.v(0))
    let (p3, q3, r3) = (try k.v(2), try k.v(1), try k.v(0))
    let implication = try k.letters(2, try k.imp(try k.imp(p2, q2), try k.imp(p2, q2)))
    let axioms: [(Axiom, NodeID)] = [
        (.ifol(.impI), implication),
        (.ifol(.mp), implication),
        (.ifol(.conjI), try k.letters(2, try k.imp(p2, try k.imp(q2, try k.and(p2, q2))))),
        (.ifol(.conjunct1), try k.letters(2, try k.imp(try k.and(p2, q2), p2))),
        (.ifol(.conjunct2), try k.letters(2, try k.imp(try k.and(p2, q2), q2))),
        (.ifol(.disjI1), try k.letters(2, try k.imp(p2, try k.or(p2, q2)))),
        (.ifol(.disjI2), try k.letters(2, try k.imp(q2, try k.or(p2, q2)))),
        (.ifol(.disjE), try k.letters(3, try k.imp(try k.or(p3, q3), try k.imp(try k.imp(p3, r3), try k.imp(try k.imp(q3, r3), r3))))),
        (.ifol(.falseE), try k.letters(1, try k.imp(bottom, p1))),
        (.ifol(.iffReflection), try k.letters(2, try k.imp(try k.and(try k.imp(p2, q2), try k.imp(q2, p2)), try k.iff(p2, q2)))),
        (.fol(.classical), try k.letters(1, try k.imp(try k.imp(try k.imp(p1, bottom), p1), p1))),
    ]
    for (a, statement) in axioms {
        let cited = try k.n(.use(.axiom(a), [], statement))
        #expect(Logic(base: b).owns(Pattern(k.t[cited], in: k.t)) == .rule, "\(a)")
        let proof = try Logic(base: b).run([cited], [], in: &k.t)[0]
        #expect(k.t.conclusion(of: proof) == statement, "\(a)")
        #expect(holdsNothingLogicOwns(proof, k, b), "\(a)")
    }
}

/// `conjI` cited and eliminated at `A` and `B`: the eliminations reduce the kernel's proof, so the use is the kernel's
/// own `and_intro` at `A` and `B`.
@Test func aCitationOfAnAxiomEliminatedAtItsLettersIsTheKernelsRuleThere() throws {
    var k = K()
    let b = try base(in: &k.t)
    let p = try k.v(1), q = try k.v(0)
    let conjI = try k.letters(2, try k.imp(p, try k.imp(q, try k.and(p, q))))
    let a = try k.c("A"), c = try k.c("B")
    let cited = try k.n(.use(.axiom(.ifol(.conjI)), [], conjI))
    let out = try Logic(base: b).run([try k.n(.isaAllElim(try k.n(.isaAllElim(cited, a)), c))], [], in: &k.t)
    #expect(out == [try k.assume(a, try k.assume(c, try k.n(.folAndIntro(try k.hyp(1, a), try k.hyp(0, c)))))])
}

/// `⋀P. P ⟹ P`, an inlined box eliminated at once at `C`: reduced at the proof level, `C ⟹ C` by its hypothesis.
@Test func aBoxEliminatedAtOnceAtAPropositionReduces() throws {
    var k = K()
    let b = try base(in: &k.t)
    let p = try k.v(0), c = try k.c("C")
    let box = try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))
    let out = try Logic(base: b).run([try k.n(.isaAllElim(box, c))], [], in: &k.t)
    #expect(out == [try k.assume(c, try k.hyp(0, c))])
}

/// A cited theorem binding a proposition at its top is a schema: its elimination at `C` is `schema_inst`, and the
/// theorem's own statement and proof keep their letter.
@Test func aCitedSchemaIsInstantiatedAndItsOwnProofKeepsItsLetter() throws {
    var k = K()
    let b = try base(in: &k.t)
    let p = try k.v(0), c = try k.c("C")
    let root = try k.letters(1, try k.imp(p, p))
    let proof = try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))
    let cited = try k.n(.use(.theorem("id"), [], root))
    let out = try Logic(base: b).run([root, proof, try k.n(.isaAllElim(cited, c))], [], in: &k.t)
    #expect(out == [root, proof, try k.n(.folSchemaInst(cited, c))])
}

/// `⋀x::i. ⋀P::o. P ⟹ P`, a box eliminated at once at `a` and `C`: the redex at `i` stays, so the elimination at `C`
/// meets no ⋀-intro and is `schema_inst`, with its letter off its spine.
@Test func aBoxBehindARedexAtIIsAnInstantiation() throws {
    var k = K()
    let b = try base(in: &k.t)
    let p = try k.v(0), c = try k.c("C")
    let box = try k.n(.isaAllIntro(i, body: try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))))
    let atI = try k.n(.isaAllElim(box, try k.n(.isaConst(.declared("a"), i, args: []))))
    let out = try Logic(base: b).run([try k.n(.isaAllElim(atI, c))], [], in: &k.t)
    #expect(out == [try k.n(.folSchemaInst(atI, c))])
}

/// At `o`, `reflexive`, `symmetric` and `transitive` are base's `iff_refl`, `iff_symm` and `iff_trans`, instantiated at
/// the sides and applied to the premises.
@Test func equalityAtOIsBasesIffSchemas() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B, C) = (try k.p("A"), try k.p("B"), try k.p("C"))
    let (ab, bc) = (try k.hyp(1, try k.iff(A, B)), try k.hyp(0, try k.iff(B, C)))
    let steps = [try k.n(.isaReflexive(A)), try k.n(.isaSymmetric(o, ab)), try k.n(.isaTransitive(o, ab, bc))]
    let out = try Logic(base: b).run(steps, [], in: &k.t)
    let symmetric = try k.n(.folImpliesElim(try k.schema(b, .iffSymm, A, B), ab))
    let transitive = try k.n(.folImpliesElim(try k.n(.folImpliesElim(try k.schema(b, .iffTrans, A, B, C), ab)), bc))
    #expect(out == [try k.schema(b, .iffRefl, A), symmetric, transitive])
}

/// The simplifier's rewrite `equal_elim (symmetric (combination (reflexive Trueprop) q)) fact`: the identity's
/// congruence at `A`, `B` is its hypothesis, applied to `q`; base's `iff_symm` turns it; `iff_elim_l` concludes.
@Test func theSimplifiersRewriteIsBasesSymmetryAtTheIdentitysCongruence() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B) = (try k.p("A"), try k.p("B"))
    let AB = try k.iff(A, B)
    let (q, fact) = (try k.hyp(1, AB), try k.hyp(0, B))
    let identity = try k.n(.isaAbs(o, body: try k.v(0)))
    let combined = try k.n(.isaCombination(oo, try k.n(.isaReflexive(identity)), q))
    let read = try k.n(.folIffElimL(try k.n(.isaSymmetric(o, combined)), fact))
    let out = try Logic(base: b).run([read], [], in: &k.t)[0]
    let congruence = try k.n(.folImpliesElim(try k.assume(AB, try k.hyp(0, AB)), q))
    let turned = try k.n(.folImpliesElim(try k.schema(b, .iffSymm, A, B), congruence))
    #expect(out == (try k.n(.folIffElimL(turned, fact))))
    #expect(k.t.conclusion(of: out) == A)
}

/// `∧` taking two equations, one argument at a time: `cong_and` at the four sides, the second combination reducing
/// what the first left under the letters that remain.
@Test func aSectionOfAndTakingTwoEquationsGoesThroughCongAnd() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A1, B1, A2, B2) = (try k.p("A1"), try k.p("B1"), try k.p("A2"), try k.p("B2"))
    let (q1, q2) = (try k.hyp(1, try k.iff(A1, B1)), try k.hyp(0, try k.iff(A2, B2)))
    let and = try k.n(.isaAbs(o, body: try k.n(.isaAbs(o, body: try k.and(try k.v(1), try k.v(0))))))
    let first = try k.n(.isaCombination(.fn(o, oo), try k.n(.isaReflexive(and)), q1))
    let out = try Logic(base: b).run([try k.n(.isaCombination(oo, first, q2))], [], in: &k.t)[0]
    #expect(k.t.conclusion(of: out) == (try k.iff(try k.and(A1, A2), try k.and(B1, B2))))
    #expect(holdsNothingLogicOwns(out, k, b))
    #expect(misplacedLetters([out], in: k.t).isEmpty)
}

/// `symmetric` and `transitive` at `o ⇒ o` keep the congruence form, base's `iff_symm` and `iff_trans` inside it.
@Test func symmetricAndTransitiveAtAFunctionOfPropositionsKeepTheCongruenceForm() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A1, B1, C1, A2, B2) = (try k.p("A1"), try k.p("B1"), try k.p("C1"), try k.p("A2"), try k.p("B2"))
    let (q1, q3, q2) = (try k.hyp(2, try k.iff(A1, B1)), try k.hyp(1, try k.iff(B1, C1)), try k.hyp(0, try k.iff(A2, B2)))
    let and = try k.n(.isaAbs(o, body: try k.n(.isaAbs(o, body: try k.and(try k.v(1), try k.v(0))))))
    let f1 = try k.n(.isaCombination(.fn(o, oo), try k.n(.isaReflexive(and)), q1))
    let f2 = try k.n(.isaCombination(.fn(o, oo), try k.n(.isaReflexive(and)), q3))
    let turned = try k.n(.isaCombination(oo, try k.n(.isaSymmetric(oo, f1)), q2))
    let chained = try k.n(.isaCombination(oo, try k.n(.isaTransitive(oo, f1, f2)), q2))
    let out = try Logic(base: b).run([turned, chained], [], in: &k.t)
    #expect(k.t.conclusion(of: out[0]) == (try k.iff(try k.and(B1, A2), try k.and(A1, B2))))
    #expect(k.t.conclusion(of: out[1]) == (try k.iff(try k.and(A1, A2), try k.and(C1, B2))))
    #expect(out.allSatisfy { holdsNothingLogicOwns($0, k, b) })
    #expect(misplacedLetters(out, in: k.t).isEmpty)
}

/// A hole under a `⋀` at `o`, as Expand's `&&&` makes them: the letter's own steps, their letters off their spine.
@Test func aHoleUnderALetterBinderLeavesItsLettersOffTheirSpine() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B) = (try k.p("A"), try k.p("B"))
    let q = try k.hyp(0, try k.iff(A, B))
    let context = try k.n(.isaAbs(o, body: try k.letters(1, try k.imp(try k.imp(try k.v(1), try k.v(0)), try k.v(0)))))
    let out = try Logic(base: b).run([try k.n(.isaCombination(oo, try k.n(.isaReflexive(context)), q))], [], in: &k.t)[0]
    let at = { (x: NodeID, k: inout K) in try k.letters(1, try k.imp(try k.imp(x, try k.v(0)), try k.v(0))) }
    #expect(k.t.conclusion(of: out) == (try k.iff(try at(A, &k), try at(B, &k))))
    #expect(!misplacedLetters([out], in: k.t).isEmpty)
}

/// A hole inside a constant's argument has no congruence of propositions: a reading missing upstream stops the run.
@Test func aHoleUnderAConstantStopsTheRun() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B) = (try k.p("A"), try k.p("B"))
    let q = try k.hyp(0, try k.iff(A, B))
    let context = try k.n(.isaAbs(o, body: try k.n(.isaConst(.declared("D"), oo, args: [try k.v(0)]))))
    let read = try k.n(.isaCombination(oo, try k.n(.isaReflexive(context)), q))
    #expect(throws: LogicError.self) { try Logic(base: b).run([read], [], in: &k.t) }
}
