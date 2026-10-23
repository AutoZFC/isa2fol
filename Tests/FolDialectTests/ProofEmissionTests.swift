import Foundation
import IR
import Testing
@testable import FolDialect

struct Pf {
    var t = Table()

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func b(_ k: Int) throws -> NodeID {
        try n(.folBound(k))
    }

    mutating func p(_ name: String, _ xs: NodeID...) throws -> NodeID {
        try n(.folPred(.base(name), args: xs))
    }

    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID {
        try n(.hyp(k, a))
    }

    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folImplies(a, b))
    }

    mutating func not(_ a: NodeID) throws -> NodeID {
        try n(.folNot(a))
    }

    mutating func intro(_ a: NodeID, _ body: NodeID) throws -> NodeID {
        try n(.folImpliesIntro(a, body: body))
    }
}

/// DESIGN.md §4.7: binders are emitted as `fix` and `assume`; a hypothesis renders as the
/// name of the `assume` that introduced it.
@Test
func aProofTreeIsEmittedAsTheCheckersStackProgram() throws {
    var f = Pf()
    let set0 = try f.p("set", try f.b(0))
    let p0 = try f.p("P", try f.b(0))
    let proof = try f.n(.folForallIntro(body: try f.intro(set0, try f.intro(p0, try f.hyp(0, p0)))))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            fix f0
            _0 = assume set(f0)
            _1 = assume P(f0)
            _2 = implies_intro _1
            _3 = implies_intro _2
            _4 = forall_intro _3
            qed _4

        """)
}

/// A cut, `folCut(p, body)`, is `p`'s step and the body citing it: no `assume`, no discharge, no formula restated.
@Test
func aCutIsWrittenAsItsProofsStepTheBodyCitingIt() throws {
    var f = Pf()
    let aAndB = try f.n(.folAnd(try f.p("A"), try f.p("B")))
    let swapped = try f.n(.folAndIntro(try f.hyp(0, try f.p("B")), try f.n(.folAndElimL(try f.hyp(1, aAndB)))))
    let proof = try f.intro(aAndB, try f.n(.folCut(try f.n(.folAndElimR(try f.hyp(0, aAndB))), body: swapped)))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A & B)
            _1 = and_elim_r _0
            _2 = and_elim_l _0
            _3 = and_intro _1, _2
            _4 = implies_intro _3
            qed _4

        """)
}

/// A line already written in an open block is cited, never written again: the projection under `assume C` is another
/// node — its hypothesis one deeper — and the same line, `and_elim_r _0`.
@Test
func aLineWrittenInAnOpenBlockIsCitedNotWrittenAgain() throws {
    var f = Pf()
    let aAndB = try f.n(.folAnd(try f.p("A"), try f.p("B")))
    let inner = try f.intro(try f.p("C"), try f.n(.folAndElimR(try f.hyp(1, aAndB))))
    let proof = try f.intro(aAndB, try f.n(.folAndIntro(try f.n(.folAndElimR(try f.hyp(0, aAndB))), inner)))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A & B)
            _1 = and_elim_r _0
            _2 = assume C
            _3 = implies_intro _1
            _4 = and_intro _1, _3
            _5 = implies_intro _4
            qed _5

        """)
}

/// A line that closes a block closes the one open, so two sibling blocks ending on one step outside them each write
/// their own `implies_intro _1`: shared, the second block would never close.
@Test
func aClosingLineIsNeverShared() throws {
    var f = Pf()
    let both = try f.n(.folAnd(try f.p("A"), try f.p("B")))
    let fromC = try f.intro(try f.p("C"), try f.n(.folAndElimR(try f.hyp(1, both))))
    let fromD = try f.intro(try f.p("D"), try f.n(.folAndElimR(try f.hyp(1, both))))
    let proof = try f.intro(both, try f.n(.folAndIntro(
        try f.n(.folAndElimR(try f.hyp(0, both))),
        try f.n(.folAndIntro(fromC, fromD)),
    )))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A & B)
            _1 = and_elim_r _0
            _2 = assume C
            _3 = implies_intro _1
            _4 = assume D
            _5 = implies_intro _1
            _6 = and_intro _3, _5
            _7 = and_intro _1, _6
            _8 = implies_intro _7
            qed _8

        """)
}

/// A step met alike in two sibling blocks is written once, in the innermost block holding both, before the first:
/// closed with the first block, it would be written again in the second.
@Test
func aStepMetAlikeInTwoSiblingBlocksIsWrittenOnceAboveThem() throws {
    var f = Pf()
    let both = try f.n(.folAnd(try f.p("A"), try f.p("B")))
    let proof = try f.intro(both, try siblings(&f, both))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A & B)
            _1 = and_elim_r _0
            _2 = assume C
            _3 = implies_intro _1
            _4 = assume D
            _5 = implies_intro _1
            _6 = and_intro _3, _5
            _7 = implies_intro _6
            qed _7

        """)
}

/// A step under the hypothesis of each branch of a case split is one node and two facts: written once, closed over the
/// hypothesis, in the block holding both branches, and each branch instantiates it.
@Test
func aStepUnderEachBranchsHypothesisIsWrittenOnceClosedOverIt() throws {
    var f = Pf()
    let proof = try caseSplit(&f, steps: 5)
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A -> B)
            _1 = assume (A | A)
            _2 = assume A
            _3 = implies_elim _0, _2
            _4 = and_intro _3, _2
            _5 = and_intro _4, _3
            _6 = and_intro _5, _2
            _7 = and_intro _6, _3
            _8 = implies_intro _7
            _9 = assume A
            _10 = implies_elim _8, _9
            _11 = and_intro _10, _9
            _12 = implies_intro _11
            _13 = assume A
            _14 = implies_elim _8, _13
            _15 = and_intro _13, _13
            _16 = and_elim_l _15
            _17 = and_intro _14, _16
            _18 = implies_intro _17
            _19 = or_elim _1, _12, _18
            _20 = implies_intro _19
            _21 = implies_intro _20
            qed _21

        """)
}

/// A step under two fixed variables is closed over the variable, `forall_elim` at each block's.
@Test
func aStepUnderTwoFixedVariablesIsClosedOverTheVariable() throws {
    var f = Pf()
    let proof = try twoFixes(&f)
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume forall b0. (P(b0) -> Q(b0))
            _1 = assume forall b0. (Q(b0) -> R(b0))
            fix f1
            _2 = forall_elim _0, f1
            _3 = forall_elim _1, f1
            _4 = and_intro _2, _3
            _5 = and_intro _4, _2
            _6 = and_intro _5, _3
            _7 = forall_intro _6
            fix f0
            _8 = forall_elim _7, f0
            _9 = forall_elim _0, f0
            _10 = and_intro _8, _9
            _11 = forall_intro _10
            fix f0
            _12 = forall_elim _7, f0
            _13 = forall_elim _0, f0
            _14 = and_intro _13, _13
            _15 = and_elim_l _14
            _16 = and_intro _12, _15
            _17 = forall_intro _16
            _18 = and_intro _11, _17
            _19 = implies_intro _18
            _20 = implies_intro _19
            qed _20

        """)
}

/// A one-line step under two hypotheses stays a line at each: closed, its binders and instantiations write more.
@Test
func aOneLineStepUnderTwoHypothesesIsWrittenAtEach() throws {
    var f = Pf()
    let proof = try caseSplit(&f, steps: 1)
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume (A -> B)
            _1 = assume (A | A)
            _2 = assume A
            _3 = implies_elim _0, _2
            _4 = and_intro _3, _2
            _5 = implies_intro _4
            _6 = assume A
            _7 = implies_elim _0, _6
            _8 = and_intro _6, _6
            _9 = and_elim_l _8
            _10 = and_intro _7, _9
            _11 = implies_intro _10
            _12 = or_elim _1, _5, _11
            _13 = implies_intro _12
            _14 = implies_intro _13
            qed _14

        """)
}

/// `assume C ⊢ B` and `assume D ⊢ B`, both from the projection of `both`, outside them.
private func siblings(_ f: inout Pf, _ both: NodeID) throws -> NodeID {
    let fromC = try f.intro(try f.p("C"), try f.n(.folAndElimR(try f.hyp(1, both))))
    let fromD = try f.intro(try f.p("D"), try f.n(.folAndElimR(try f.hyp(1, both))))
    return try f.n(.folAndIntro(fromC, fromD))
}

/// `(A → B) → (A ∨ A) → S ∧ A`, by cases on `A ∨ A`, each branch deriving `S` from its own `A` in `steps` lines: `B`,
/// then alternately `∧ A` and `∧ B`. The branches differ in how they prove `A` again, so they are two nodes.
private func caseSplit(_ f: inout Pf, steps: Int) throws -> NodeID {
    let A = try f.p("A")
    let B = try f.p("B")
    let h = try f.hyp(0, A)
    let first = try f.n(.folImpliesElim(try f.hyp(2, try f.imp(A, B)), h))
    var s = first
    for k in 1..<steps { s = try f.n(.folAndIntro(s, k % 2 == 1 ? h : first)) }
    let again = try f.n(.folAndElimL(try f.n(.folAndIntro(h, h))))
    let one = try f.intro(A, try f.n(.folAndIntro(s, h)))
    let other = try f.intro(A, try f.n(.folAndIntro(s, again)))
    let aOrA = try f.n(.folOr(A, A))
    return try f.intro(try f.imp(A, B), try f.intro(aOrA, try f.n(.folOrElim(try f.hyp(0, aOrA), one, other))))
}

/// `∀P→Q, ∀Q→R ⊢ (∀x. S(x) ∧ (P(x) → Q(x))) ∧ (∀x. S(x) ∧ (P(x) → Q(x)))`, `S(x)` five lines over `x` alone.
private func twoFixes(_ f: inout Pf) throws -> NodeID {
    let pq = try f.n(.folForall(body: try f.imp(try f.p("P", try f.b(0)), try f.p("Q", try f.b(0)))))
    let qr = try f.n(.folForall(body: try f.imp(try f.p("Q", try f.b(0)), try f.p("R", try f.b(0)))))
    let x = try f.b(0)
    let m1 = try f.n(.folForallElim(try f.hyp(1, pq), x))
    let m2 = try f.n(.folForallElim(try f.hyp(0, qr), x))
    let s = try f.n(.folAndIntro(
        try f.n(.folAndIntro(try f.n(.folAndIntro(m1, m2)), m1)),
        m2,
    ))
    let one = try f.n(.folForallIntro(body: try f.n(.folAndIntro(s, m1))))
    let other = try f.n(.folForallIntro(body: try f.n(.folAndIntro(
        s,
        try f.n(.folAndElimL(try f.n(.folAndIntro(m1, m1)))),
    ))))
    return try f.intro(pq, try f.intro(qr, try f.n(.folAndIntro(one, other))))
}

/// A value fixed at a proof's top is named at its binder by its level, `f0`, and written so wherever it stands; a `fix`
/// below is named past it, and its hypothesis's halves are cited inside the binder's block (DESIGN "A value fixed at a
/// proof's top, named by itself").
@Test
func aValueFixedAtTheTopIsNamedByItsBinder() throws {
    var f = Pf()
    let proof = try valueAtTheTop(&f)
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume exists b0. (set(b0) & P(b0))
            _1 = assume forall b0. (set(b0) -> (P(b0) -> R))
            _2 = exists_elim _0, f0
            fix f1
            _3 = assume Q(f1)
            _4 = forall_elim _1, f0
            _5 = and_elim_l _2
            _6 = implies_elim _4, _5
            _7 = and_elim_r _2
            _8 = implies_elim _6, _7
            _9 = implies_intro _8
            _10 = forall_intro _9
            _11 = exists_intro _10
            _12 = implies_intro _11
            _13 = implies_intro _12
            qed _13

        """)
}

/// `(∃x. set(x) ∧ P(x)) → (∀x. set(x) → P(x) → R) → ∀y. Q(y) → R`, the existence's value fixed by name below the
/// hypotheses, its guard and fact discharged under `fix`.
private func valueAtTheTop(_ f: inout Pf) throws -> NodeID {
    let x = try f.b(0)
    let some = try f.n(.folExists(body: try f.n(.folAnd(try f.p("set", x), try f.p("P", x)))))
    let R = try f.p("R")
    let every = try f.n(.folForall(body: try f.imp(try f.p("set", x), try f.imp(try f.p("P", x), R))))
    let v = try f.n(.value(try f.n(.isaConst(.primitive(.zf(.zero)), .i, args: []))))
    let fact = try f.n(.valueFact(v, try f.n(.folAnd(try f.p("set", v), try f.p("P", v)))))
    let atV = try f.n(.folImpliesElim(
        try f.n(.folForallElim(try f.hyp(1, every), v)),
        try f.n(.folAndElimL(fact)),
    ))
    let body = try f.n(.folImpliesElim(atV, try f.n(.folAndElimR(fact))))
    let under = try f.n(.folForallIntro(body: try f.intro(try f.p("Q", x), body)))
    return try f.intro(some, try f.intro(every, try f.n(.valueElim(v, try f.hyp(1, some), body: under))))
}

/// An `assume` opens a block, so one inside another of the same formula is written again: each is its own scope.
@Test
func anAssumptionIsNeverShared() throws {
    var f = Pf()
    let A = try f.p("A")
    let proof = try f.intro(A, try f.intro(A, try f.hyp(0, A)))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t) == """
        proof probe:
            _0 = assume A
            _1 = assume A
            _2 = implies_intro _1
            _3 = implies_intro _2
            qed _3

        """)
}

/// An instance has no claim name yet: rendering it by its theorem's name would conflate its instances.
@Test
func aCitationOfAnInstanceIsNotRendered() throws {
    var f = Pf()
    let a = try f.p("A")
    let cited = try f.n(.use(.theorem("thm"), [.i], a))
    let claim = Declaration(kind: .claim, name: "probe", root: a)
    #expect(throws: RenderError.instanceCitation(cited)) { try render(proof: cited, of: claim, in: f.t) }
}

@Test
func aProofMustConcludeItsClaim() throws {
    var f = Pf()
    let a = try f.p("A")
    let b = try f.p("B")
    let proof = try f.intro(a, try f.hyp(0, a))
    #expect(throws: RenderError.proofConcludes(expected: b, found: try #require(f.t.conclusion(of: proof)))) {
        try render(proof: proof, of: Declaration(kind: .claim, name: "c", root: b), in: f.t)
    }
    #expect(throws: RenderError.notAProof(a)) {
        try render(proof: a, of: Declaration(kind: .claim, name: "c", root: a), in: f.t)
    }
    #expect(throws: RenderError.notAFormula(proof)) { try render(formula: proof, in: f.t) }
}

@Test
func anIsaStepIsNotEmitted() throws {
    var f = Pf()
    let set0 = try f.p("set", try f.b(0))
    let step = try f.n(.isaAllIntro(.i, body: try f.intro(set0, try f.hyp(0, set0))))
    let root = try #require(f.t.conclusion(of: step))
    #expect(throws: RenderError.sourceKind(step)) {
        try render(proof: step, of: Declaration(kind: .claim, name: "c", root: root), in: f.t)
    }
}

/// A base schema instantiated at every letter is one `schema_inst` step, its letters named as base declares them; at
/// some
/// letters only, it is no step the checker has.
@Test
func aSchemaInstanceRendersAsOneStepNamingItsLetters() throws {
    var f = Pf()
    let (_, schema) = try parse(schema: "schema iff_symm [A(0), B(0)]: ((A <-> B) -> (B <-> A))", in: &f.t)
    let letters = schemaLetters(from: ["schema iff_symm [A(0), B(0)]: ((A <-> B) -> (B <-> A))"])
    #expect(letters == ["iff_symm": ["A", "B"]])
    let P = try f.p("P")
    let Q = try f.p("Q")
    let cited = try f.n(.use(.base("iff_symm"), [], schema))
    let instance = try f.n(.folSchemaInst(try f.n(.folSchemaInst(cited, P)), Q))
    let pq = try f.n(.folIff(P, Q))
    let proof = try f.intro(pq, try f.n(.folImpliesElim(instance, try f.hyp(0, pq))))
    let claim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: proof)))
    #expect(try render(proof: proof, of: claim, in: f.t, letters: letters) == """
        proof probe:
            _0 = assume (P <-> Q)
            _1 = schema_inst iff_symm { A: P, B: Q }
            _2 = implies_elim _1, _0
            _3 = implies_intro _2
            qed _3

        """)
    let partial = try f.n(.folSchemaInst(cited, P))
    let partialClaim = Declaration(kind: .claim, name: "probe", root: try #require(f.t.conclusion(of: partial)))
    #expect(throws: RenderError.schema(partial)) { try render(
        proof: partial,
        of: partialClaim,
        in: f.t,
        letters: letters,
    ) }
}

/// A letter with arguments is instantiated at a λ, the table β-reducing its applications, and the λ renders as the
/// kernel reads it, `\b1. elem(b1, f0)`.
@Test
func aLetterWithArgumentsIsInstantiatedAtALambdaAndRendered() throws {
    var f = Pf()
    let line = "schema mono [P(1)]: ((forall z. P(z)) -> (forall z. P(z)))"
    let (_, schema) = try parse(schema: line, in: &f.t)
    let letters = schemaLetters(from: [line])
    #expect(letters == ["mono": ["P"]])
    let lambda = try f.n(.folLetterAbs(body: try f.p("elem", try f.b(0), try f.b(1))))
    let instance = try f.n(.folSchemaInst(try f.n(.use(.base("mono"), [], schema)), lambda))
    let every = try f.n(.folForall(body: try f.p("elem", try f.b(0), try f.b(1))))
    let claim = Declaration(kind: .claim, name: "probe", root: try f.n(.folForall(body: try f.imp(every, every))))
    #expect(try render(proof: try f.n(.folForallIntro(body: instance)), of: claim, in: f.t, letters: letters) == """
        proof probe:
            fix f0
            _0 = schema_inst mono { P: \\b1. elem(b1, f0) }
            _1 = forall_intro _0
            qed _1

        """)
}

/// ⚠ THE CHECKER IS THE ONLY AUTHORITY: one claim per rule family, each PROVED by the real
/// checker from what emission writes.
@Test
func theRealCheckerProvesWhatEmissionWrites() throws {
    let ck = ProcessInfo.processInfo.environment["PROOF_CHECKER"]
        ?? NSString(string: "~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker").expandingTildeInPath
    try #require(FileManager.default.isExecutableFile(atPath: ck), "no proof_checker at \(ck); set PROOF_CHECKER")
    let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
        .deletingLastPathComponent().deletingLastPathComponent()

    var f = Pf()
    var proofs = [(String, NodeID)]()
    let A = try f.p("A")
    let B = try f.p("B")
    let bottom = try f.n(.folBottom)
    let hA = try f.hyp(0, A)
    let aa = try f.intro(A, hA)

    let set0 = try f.p("set", try f.b(0))
    let p0 = try f.p("P", try f.b(0))
    proofs.append(("p_forall", try f.n(.folForallIntro(body: try f.intro(set0, try f.intro(p0, try f.hyp(0, p0)))))))

    let elem01 = try f.p("elem", try f.b(0), try f.b(1))
    let someY = try f.n(.folExists(body: elem01))
    let reintroduced = try f.n(.folExistsIntro(try f.hyp(0, elem01), try f.b(0)))
    proofs.append(("p_exists", try f.n(.folForallIntro(body: try f.intro(
        someY,
        try f.n(.folExistsElim(
            try f.hyp(0, someY),
            body: reintroduced,
        )),
    )))))

    let nA = try f.not(A)
    let nnA = try f.not(nA)
    proofs.append(("p_classical", try f.intro(nnA, try f.n(.folClassicalAbsurd(
        A,
        body: try f.n(.folNotElim(
            try f.hyp(1, nnA),
            try f.hyp(0, nA),
        )),
    )))))
    proofs.append(("p_not_intro", try f.intro(A, try f.n(.folNotIntro(
        nA,
        body: try f.n(.folNotElim(
            try f.hyp(0, nA),
            try f.hyp(1, A),
        )),
    )))))

    let aOrBottom = try f.n(.folOr(A, bottom))
    let fromBottom = try f.intro(bottom, try f.n(.folBottomElim(try f.hyp(0, bottom), A)))
    proofs.append(("p_or_elim", try f.intro(aOrBottom, try f.n(.folOrElim(try f.hyp(0, aOrBottom), aa, fromBottom)))))
    proofs.append(("p_or_intro_l", try f.intro(A, try f.n(.folOrIntroL(hA, B)))))
    proofs.append(("p_or_intro_r", try f.intro(A, try f.n(.folOrIntroR(B, hA)))))

    proofs.append(("p_iff_intro", try f.n(.folIffIntro(aa, aa))))
    let aIffB = try f.n(.folIff(A, B))
    proofs.append(("p_iff_elim", try f.intro(aIffB, try f.intro(A, try f.n(.folIffElimL(try f.hyp(1, aIffB), hA))))))

    let aAndB = try f.n(.folAnd(A, B))
    let hAB = try f.hyp(0, aAndB)
    proofs.append((
        "p_and",
        try f.intro(aAndB, try f.n(.folAndIntro(try f.n(.folAndElimR(hAB)), try f.n(.folAndElimL(hAB))))),
    ))

    // `B -> B` is used inside `A -> false`'s block, after `B` is derived there, and after the block: written once
    // before
    // the block, the checker keys it by its formula with no scope of the block's.
    let notA = try f.imp(A, bottom)
    let fromNotA = try f.imp(notA, B)
    let bb = try f.intro(B, try f.hyp(0, B))
    let inside = try f.n(.folAndIntro(try f.n(.folImpliesElim(try f.hyp(1, fromNotA), try f.hyp(0, notA))), bb))
    proofs.append(("p_block", try f.intro(fromNotA, try f.n(.folAndIntro(try f.intro(notA, inside), bb)))))

    let swapped = try f.n(.folAndIntro(try f.hyp(0, B), try f.n(.folAndElimL(try f.hyp(1, aAndB)))))
    proofs.append(("p_cut", try f.intro(aAndB, try f.n(.folCut(try f.n(.folAndElimR(hAB)), body: swapped)))))

    let both = try f.n(.folAnd(set0, elem01))
    let someSet = try f.n(.folExists(body: both))
    let again = try f.n(.folExistsIntro(try f.n(.folAndIntro(try f.hyp(1, set0), try f.hyp(0, elem01))), try f.b(0)))
    let opened = try f.n(.folCut(
        try f.n(.folAndElimL(try f.hyp(0, both))),
        body: try f.n(.folCut(try f.n(.folAndElimR(try f.hyp(1, both))), body: again)),
    ))
    proofs.append(("p_exists_cut", try f.n(.folForallIntro(body: try f.intro(
        someSet,
        try f.n(.folExistsElim(try f.hyp(0, someSet), body: opened)),
    )))))

    let deeper = try f.intro(try f.p("C"), try f.n(.folAndElimR(try f.hyp(1, aAndB))))
    proofs.append(("p_cited", try f.intro(aAndB, try f.n(.folAndIntro(try f.n(.folAndElimR(hAB)), deeper)))))
    proofs.append(("p_assume_twice", try f.intro(A, try f.intro(A, hA))))
    let fromC = try f.intro(try f.p("C"), try f.n(.folAndElimR(try f.hyp(1, aAndB))))
    let fromD = try f.intro(try f.p("D"), try f.n(.folAndElimR(try f.hyp(1, aAndB))))
    proofs.append(("p_closers", try f.intro(aAndB, try f.n(.folAndIntro(
        try f.n(.folAndElimR(hAB)),
        try f.n(.folAndIntro(fromC, fromD)),
    )))))

    let elem10 = try f.p("elem", try f.b(1), try f.b(0))
    let membersAreSets = try f.n(.folForall(body: try f.n(.folForall(body: try f.imp(
        elem10,
        try f.p("set", try f.b(1)),
    )))))
    let cited = try f.n(.folForallElim(
        try f.n(.folForallElim(try f.n(.use(.theorem("members_are_sets"), [], membersAreSets)), try f.b(1))),
        try f.b(0),
    ))
    proofs.append(("p_use", try f.n(.folForallIntro(body: try f.n(.folForallIntro(body:
        try f.intro(elem10, try f.n(.folImpliesElim(cited, try f.hyp(0, elem10))))))))))
    proofs.append(("p_siblings", try f.intro(aAndB, try siblings(&f, aAndB))))
    proofs.append(("p_closed_hypothesis", try caseSplit(&f, steps: 5)))
    proofs.append(("p_closed_variable", try twoFixes(&f)))
    proofs.append(("p_value", try valueAtTheTop(&f)))

    var def = ""
    var proof = ""
    for (name, step) in proofs {
        let claim = Declaration(kind: .claim, name: name, root: try #require(f.t.conclusion(of: step)))
        def += try render(claim, in: f.t) + "\n"
        proof += try render(proof: step, of: claim, in: f.t) + "\n"
    }

    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-emit-\(getpid())")
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: dir) }
    let defURL = dir.appendingPathComponent("p.fol.def")
    let prfURL = dir.appendingPathComponent("p.fol.proof")
    try def.write(to: defURL, atomically: true, encoding: .utf8)
    try proof.write(to: prfURL, atomically: true, encoding: .utf8)

    let proc = Process()
    proc.executableURL = URL(fileURLWithPath: ck)
    proc.arguments = [defURL.path, prfURL.path, repo.appendingPathComponent("base/axioms.fol.def").path]
    let out = Pipe()
    let err = Pipe()
    proc.standardOutput = out
    proc.standardError = err
    try proc.run()
    let stdout = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let stderr = String(decoding: err.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    proc.waitUntilExit()

    #expect(proc.terminationStatus == 0, "checker rejected:\n\(def)\n\(proof)\n\(stdout)\(stderr)")
    #expect(stderr.isEmpty, "stderr must be empty: \(stderr)")
    for (name, _) in proofs {
        #expect(stdout.contains("+ \(name)\n"), "\(name) did not prove:\n\(stdout)")
    }
}
