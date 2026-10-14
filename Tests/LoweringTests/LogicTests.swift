import Testing
import IR
import Lowering

private let i = IRType.i
private let o = IRType.o

private struct K {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, o)) }
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
}

/// The 16 axioms of the logic binding only propositions, each as the reader reads it after Expand (`⟹` and `⟶` one
/// node, `≡` at `o` read as `↔`, `¬P` unfolded to `P ⟶ ⊥`): a citation of each becomes the kernel's proof of the cited
/// statement, by ID, holding nothing Logic owns.
@Test func eachPropositionalAxiomIsTheKernelsProofOfItsStatement() throws {
    var k = K()
    let bottom = try k.n(.folBottom)
    let p1 = try k.v(0)
    let (p2, q2) = (try k.v(1), try k.v(0))
    let (p3, q3, r3) = (try k.v(2), try k.v(1), try k.v(0))
    let implication = try k.letters(2, try k.imp(try k.imp(p2, q2), try k.imp(p2, q2)))
    let axioms: [(Axiom, [IRType], NodeID)] = [
        (.pure(.equalIntr), [], try k.letters(2, try k.imp(try k.imp(p2, q2), try k.imp(try k.imp(q2, p2), try k.iff(p2, q2))))),
        (.pure(.equalElim), [], try k.letters(2, try k.imp(try k.iff(p2, q2), try k.imp(p2, q2)))),
        (.pure(.reflexive), [o], try k.letters(1, try k.iff(p1, p1))),
        (.pure(.symmetric), [o], try k.letters(2, try k.imp(try k.iff(p2, q2), try k.iff(q2, p2)))),
        (.pure(.transitive), [o], try k.letters(3, try k.imp(try k.iff(p3, q3), try k.imp(try k.iff(q3, r3), try k.iff(p3, r3))))),
        (.ifol(.impI), [], implication),
        (.ifol(.mp), [], implication),
        (.ifol(.conjI), [], try k.letters(2, try k.imp(p2, try k.imp(q2, try k.and(p2, q2))))),
        (.ifol(.conjunct1), [], try k.letters(2, try k.imp(try k.and(p2, q2), p2))),
        (.ifol(.conjunct2), [], try k.letters(2, try k.imp(try k.and(p2, q2), q2))),
        (.ifol(.disjI1), [], try k.letters(2, try k.imp(p2, try k.or(p2, q2)))),
        (.ifol(.disjI2), [], try k.letters(2, try k.imp(q2, try k.or(p2, q2)))),
        (.ifol(.disjE), [], try k.letters(3, try k.imp(try k.or(p3, q3), try k.imp(try k.imp(p3, r3), try k.imp(try k.imp(q3, r3), r3))))),
        (.ifol(.falseE), [], try k.letters(1, try k.imp(bottom, p1))),
        (.ifol(.iffReflection), [], try k.letters(2, try k.imp(try k.and(try k.imp(p2, q2), try k.imp(q2, p2)), try k.iff(p2, q2)))),
        (.fol(.classical), [], try k.letters(1, try k.imp(try k.imp(try k.imp(p1, bottom), p1), p1))),
    ]
    for (a, types, statement) in axioms {
        let cited = try k.n(.use(.axiom(a), types, statement))
        #expect(Logic().owns(Pattern(k.t[cited], in: k.t)) == .rule, "\(a)")
        let proof = try Logic().run([cited], [], in: &k.t)[0]
        #expect(k.t.conclusion(of: proof) == statement, "\(a)")
        #expect(patterns(under: [proof], in: k.t).allSatisfy { Logic().owns($0) == nil }, "\(a)")
    }
}

/// `conjI` cited and eliminated at `A` and `B`: the eliminations reduce the kernel's proof, so the use is the kernel's
/// own `and_intro` at `A` and `B`.
@Test func aCitationOfAnAxiomEliminatedAtItsLettersIsTheKernelsRuleThere() throws {
    var k = K()
    let p = try k.v(1), q = try k.v(0)
    let conjI = try k.letters(2, try k.imp(p, try k.imp(q, try k.and(p, q))))
    let a = try k.c("A"), b = try k.c("B")
    let cited = try k.n(.use(.axiom(.ifol(.conjI)), [], conjI))
    let out = try Logic().run([try k.n(.isaAllElim(try k.n(.isaAllElim(cited, a)), b))], [], in: &k.t)
    #expect(out == [try k.assume(a, try k.assume(b, try k.n(.folAndIntro(try k.hyp(1, a), try k.hyp(0, b)))))])
}

/// `⋀P. P ⟹ P`, an inlined box eliminated at once at `C`: reduced at the proof level, `C ⟹ C` by its hypothesis.
@Test func aBoxEliminatedAtOnceAtAPropositionReduces() throws {
    var k = K()
    let p = try k.v(0), c = try k.c("C")
    let box = try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))
    let out = try Logic().run([try k.n(.isaAllElim(box, c))], [], in: &k.t)
    #expect(out == [try k.assume(c, try k.hyp(0, c))])
}

/// A cited theorem binding a proposition at its top is a schema: its elimination at `C` is `schema_inst`, and the
/// theorem's own statement and proof keep their letter.
@Test func aCitedSchemaIsInstantiatedAndItsOwnProofKeepsItsLetter() throws {
    var k = K()
    let p = try k.v(0), c = try k.c("C")
    let root = try k.letters(1, try k.imp(p, p))
    let proof = try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))
    let cited = try k.n(.use(.theorem("id"), [], root))
    let out = try Logic().run([root, proof, try k.n(.isaAllElim(cited, c))], [], in: &k.t)
    #expect(out == [root, proof, try k.n(.folSchemaInst(cited, c))])
}

/// `⋀x::i. ⋀P::o. P ⟹ P`, a box eliminated at once at `a` and `C`: the redex at `i` stays, so the elimination at `C`
/// meets no ⋀-intro and is `schema_inst`, with its letter off its spine.
@Test func aBoxBehindARedexAtIIsAnInstantiation() throws {
    var k = K()
    let p = try k.v(0), c = try k.c("C")
    let box = try k.n(.isaAllIntro(i, body: try k.n(.isaAllIntro(o, body: try k.assume(p, try k.hyp(0, p))))))
    let atI = try k.n(.isaAllElim(box, try k.n(.isaConst(.declared("a"), i, args: []))))
    let out = try Logic().run([try k.n(.isaAllElim(atI, c))], [], in: &k.t)
    #expect(out == [try k.n(.folSchemaInst(atI, c))])
}
