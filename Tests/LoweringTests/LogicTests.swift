import Testing
import IR
import Lowering

private let o = IRType.o

private struct K {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, o)) }
    mutating func p(_ name: String) throws -> NodeID { try n(.folPred(.base(name), args: [])) }
    mutating func c(_ name: String) throws -> NodeID { try n(.isaConst(.declared(name), o, args: [])) }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
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

/// `⋀P. P ⟹ P` introduced by Pure's `⋀` in a proof and eliminated at once at `C`: a truth set, its intro
/// `truth(E) → (holds(E) → holds(E))` under `∀E`, and the elimination the truth instance, concluding `C → C` as read.
@Test func pureAllIntroducedInAProofAndInstantiatedIsTheTruthInstance() throws {
    var k = K()
    let b = try base(in: &k.t)
    let p = try k.n(.isaPropBound(0)), c = try k.c("C")
    let inner = try k.n(.isaPropIntro(body: try k.assume(p, try k.hyp(0, p))))
    let out = try Logic(base: b).run([try k.n(.isaAllElim(inner, c))], [], in: &k.t)
    #expect(k.t.conclusion(of: out[0]) == (try k.imp(c, c)))
    #expect(misplacedLetters(out, in: k.t).isEmpty)
}

/// Pure's `⋀` over a proposition in a premise: `∀E. truth(E) → φ*`, its variable read `holds(E)`.
@Test func pureAllOverAPropositionIsATruthSet() throws {
    var k = K()
    let b = try base(in: &k.t)
    let c = try k.c("C")
    let bound = try k.n(.isaPropBound(0))
    let premise = try k.n(.isaPropAll(body: try k.imp(bound, bound)))
    let out = try Logic(base: b).run([try k.imp(premise, c)], [], in: &k.t)
    let holds = try k.n(.folPred(.base("holds"), args: [try k.n(.folBound(0))]))
    let truth = try k.n(.folPred(.base("truth"), args: [try k.n(.folBound(0))]))
    let read = try k.n(.folForall(body: try k.imp(truth, try k.imp(holds, holds))))
    #expect(out == [try k.imp(read, c)])
}

/// `reflexive Trueprop`, `λP. P` at `o ⇒ o`, is pointwise over truth sets: `∀E. truth(E) → (holds(E) ↔ holds(E))`; its
/// `combination` with `q : A ↔ B` concludes `A ↔ B`, as the table β-reduces it; a stated equation is the same formula.
@Test func anEquationBetweenFunctionsOfPropositionsIsPointwiseOverTruthSets() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B) = (try k.p("A"), try k.p("B"))
    let identity = try k.n(.isaAbs(o, body: try k.v(0)))
    let reflexive = try k.n(.isaReflexive(identity))
    let q = try k.hyp(0, try k.iff(A, B))
    let stated = try k.t.equation(.fn(o, o), identity, identity)
    let out = try Logic(base: b).run([reflexive, try k.n(.isaCombination(.fn(o, o), reflexive, q)), stated], [], in: &k.t)
    let holds = try k.n(.folPred(.base("holds"), args: [try k.n(.folBound(0))]))
    let truth = try k.n(.folPred(.base("truth"), args: [try k.n(.folBound(0))]))
    let pointwise = try k.n(.folForall(body: try k.imp(truth, try k.iff(holds, holds))))
    #expect(k.t.conclusion(of: out[0]) == pointwise)
    #expect(k.t.conclusion(of: out[1]) == (try k.iff(A, B)))
    #expect(out[2] == pointwise)
}

/// A section of `∧`, `λP Q. P ∧ Q`, rewritten in both operands through two `combination`s, at `o ⇒ (o ⇒ o)` and at
/// `o ⇒ o`.
@Test func aSectionOfAConnectiveRewritesThroughTwoCombinations() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, A2, B, B2) = (try k.p("A"), try k.p("A2"), try k.p("B"), try k.p("B2"))
    let and = try k.n(.isaAbs(o, body: try k.n(.isaAbs(o, body: try k.n(.folAnd(try k.v(1), try k.v(0)))))))
    let first = try k.n(.isaCombination(.fn(o, .fn(o, o)), try k.n(.isaReflexive(and)), try k.hyp(1, try k.iff(A, A2))))
    let both = try k.n(.isaCombination(.fn(o, o), first, try k.hyp(0, try k.iff(B, B2))))
    let out = try Logic(base: b).run([both], [], in: &k.t)
    #expect(k.t.conclusion(of: out[0]) == (try k.iff(try k.n(.folAnd(A, B)), try k.n(.folAnd(A2, B2)))))
}

/// `transitive` at `o ⇒ o` of two stated equations is the pointwise equation of its ends.
@Test func transitiveAtAFunctionOfPropositionsIsPointwise() throws {
    var k = K()
    let b = try base(in: &k.t)
    let C = try k.p("C")
    let f = try k.n(.isaAbs(o, body: try k.v(0)))
    let g = try k.n(.isaAbs(o, body: try k.n(.folAnd(try k.v(0), try k.v(0)))))
    let h = try k.n(.isaAbs(o, body: try k.n(.folAnd(try k.v(0), C))))
    let (fg, gh) = (try k.t.equation(.fn(o, o), f, g), try k.t.equation(.fn(o, o), g, h))
    let both = try k.n(.isaTransitive(.fn(o, o), try k.hyp(1, fg), try k.hyp(0, gh)))
    let out = try Logic(base: b).run([both, try k.t.equation(.fn(o, o), f, h)], [], in: &k.t)
    #expect(k.t.conclusion(of: out[0]) == out[1])
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
    #expect(misplacedLetters(out, in: k.t).isEmpty)
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

/// After Expand, `classical` is the kernel's reductio over `h : (A → ⊥) → A`, and `iff_reflection` the kernel's `iff_intro`
/// of `h : (A → B) ∧ (B → A)`'s conjuncts: each concludes as read, in fol-zfc alone.
@Test func classicalAndIffReflectionAreTheKernelsStepsAfterExpand() throws {
    var k = K()
    let b = try base(in: &k.t)
    let (A, B) = (try k.p("A"), try k.p("B"))
    let premise = try k.imp(try k.imp(A, try k.n(.folBottom)), A)
    let both = try k.n(.folAnd(try k.imp(A, B), try k.imp(B, A)))
    let classical = try k.n(.isaClassical(A, try k.hyp(0, premise)))
    let reflection = try k.n(.isaIffReflection(A, B, try k.hyp(0, both)))
    let out = try Logic(base: b).run([classical, reflection], [], in: &k.t)
    #expect(k.t.conclusion(of: out[0]) == A)
    #expect(k.t.conclusion(of: out[1]) == (try k.iff(A, B)))
    #expect(patterns(under: out, in: k.t).allSatisfy { $0.dialects == [.fol] || $0.dialects == [.isa, .fol] })
}
