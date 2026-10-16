import Foundation
import Testing
import IR
@testable import FolDialect

struct Pf {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func b(_ k: Int) throws -> NodeID { try n(.folBound(k)) }
    mutating func p(_ name: String, _ xs: NodeID...) throws -> NodeID { try n(.folPred(.base(name), args: xs)) }
    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try n(.hyp(k, a)) }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
    mutating func not(_ a: NodeID) throws -> NodeID { try n(.folNot(a)) }
    mutating func intro(_ a: NodeID, _ body: NodeID) throws -> NodeID { try n(.folImpliesIntro(a, body: body)) }
}

/// DESIGN.md §4.7: binders are emitted as `fix` and `assume`; a hypothesis renders as the
/// name of the `assume` that introduced it.
@Test func aProofTreeIsEmittedAsTheCheckersStackProgram() throws {
    var f = Pf()
    let set0 = try f.p("set", try f.b(0)), p0 = try f.p("P", try f.b(0))
    let proof = try f.n(.folForallIntro(body: try f.intro(set0, try f.intro(p0, try f.hyp(0, p0)))))
    let claim = Declaration(kind: .claim, name: "probe", root: f.t.conclusion(of: proof)!)
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

/// An instance has no claim name yet: rendering it by its theorem's name would conflate its instances.
@Test func aCitationOfAnInstanceIsNotRendered() throws {
    var f = Pf()
    let a = try f.p("A")
    let cited = try f.n(.use(.theorem("thm"), [.i], a))
    let claim = Declaration(kind: .claim, name: "probe", root: a)
    #expect(throws: RenderError.instanceCitation(cited)) { try render(proof: cited, of: claim, in: f.t) }
}

@Test func aProofMustConcludeItsClaim() throws {
    var f = Pf()
    let a = try f.p("A"), b = try f.p("B")
    let proof = try f.intro(a, try f.hyp(0, a))
    #expect(throws: RenderError.proofConcludes(expected: b, found: f.t.conclusion(of: proof)!)) {
        try render(proof: proof, of: Declaration(kind: .claim, name: "c", root: b), in: f.t)
    }
    #expect(throws: RenderError.notAProof(a)) {
        try render(proof: a, of: Declaration(kind: .claim, name: "c", root: a), in: f.t)
    }
    #expect(throws: RenderError.notAFormula(proof)) { try render(formula: proof, in: f.t) }
}

@Test func anIsaStepIsNotEmitted() throws {
    var f = Pf()
    let set0 = try f.p("set", try f.b(0))
    let step = try f.n(.isaAllIntro(.i, body: try f.intro(set0, try f.hyp(0, set0))))
    let root = f.t.conclusion(of: step)!
    #expect(throws: RenderError.sourceKind(step)) {
        try render(proof: step, of: Declaration(kind: .claim, name: "c", root: root), in: f.t)
    }
}

/// A base schema instantiated at every letter is one `schema_inst` step, its letters named as base declares them; at some
/// letters only, it is no step the checker has.
@Test func aSchemaInstanceRendersAsOneStepNamingItsLetters() throws {
    var f = Pf()
    let (_, schema) = try parse(schema: "schema iff_symm [A(0), B(0)]: ((A <-> B) -> (B <-> A))", in: &f.t)
    let letters = schemaLetters(from: ["schema iff_symm [A(0), B(0)]: ((A <-> B) -> (B <-> A))"])
    #expect(letters == ["iff_symm": ["A", "B"]])
    let (P, Q) = (try f.p("P"), try f.p("Q"))
    let cited = try f.n(.use(.base("iff_symm"), [], schema))
    let instance = try f.n(.folSchemaInst(try f.n(.folSchemaInst(cited, P)), Q))
    let pq = try f.n(.folIff(P, Q))
    let proof = try f.intro(pq, try f.n(.folImpliesElim(instance, try f.hyp(0, pq))))
    let claim = Declaration(kind: .claim, name: "probe", root: f.t.conclusion(of: proof)!)
    #expect(try render(proof: proof, of: claim, in: f.t, letters: letters) == """
        proof probe:
            _0 = assume (P <-> Q)
            _1 = schema_inst iff_symm { A: P, B: Q }
            _2 = implies_elim _1, _0
            _3 = implies_intro _2
            qed _3

        """)
    let partial = try f.n(.folSchemaInst(cited, P))
    let partialClaim = Declaration(kind: .claim, name: "probe", root: f.t.conclusion(of: partial)!)
    #expect(throws: RenderError.schema(partial)) { try render(proof: partial, of: partialClaim, in: f.t, letters: letters) }
}

/// A letter with arguments is instantiated at a λ, the table β-reducing its applications, and the λ renders as the
/// kernel reads it, `\b1. elem(b1, f0)`.
@Test func aLetterWithArgumentsIsInstantiatedAtALambdaAndRendered() throws {
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
@Test func theRealCheckerProvesWhatEmissionWrites() throws {
    let ck = ProcessInfo.processInfo.environment["PROOF_CHECKER"]
        ?? NSString(string: "~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker").expandingTildeInPath
    guard FileManager.default.isExecutableFile(atPath: ck) else {
        Issue.record("no proof_checker at \(ck); set PROOF_CHECKER")
        return
    }
    let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
        .deletingLastPathComponent().deletingLastPathComponent()

    var f = Pf()
    var proofs: [(String, NodeID)] = []
    let A = try f.p("A"), B = try f.p("B"), bottom = try f.n(.folBottom)
    let hA = try f.hyp(0, A), aa = try f.intro(A, hA)

    let set0 = try f.p("set", try f.b(0)), p0 = try f.p("P", try f.b(0))
    proofs.append(("p_forall", try f.n(.folForallIntro(body: try f.intro(set0, try f.intro(p0, try f.hyp(0, p0)))))))

    let elem01 = try f.p("elem", try f.b(0), try f.b(1))
    let someY = try f.n(.folExists(body: elem01))
    let reintroduced = try f.n(.folExistsIntro(try f.hyp(0, elem01), try f.b(0)))
    proofs.append(("p_exists", try f.n(.folForallIntro(body: try f.intro(someY,
        try f.n(.folExistsElim(try f.hyp(0, someY), body: reintroduced)))))))

    let nA = try f.not(A), nnA = try f.not(nA)
    proofs.append(("p_classical", try f.intro(nnA, try f.n(.folClassicalAbsurd(A,
        body: try f.n(.folNotElim(try f.hyp(1, nnA), try f.hyp(0, nA))))))))
    proofs.append(("p_not_intro", try f.intro(A, try f.n(.folNotIntro(nA,
        body: try f.n(.folNotElim(try f.hyp(0, nA), try f.hyp(1, A))))))))

    let aOrBottom = try f.n(.folOr(A, bottom))
    let fromBottom = try f.intro(bottom, try f.n(.folBottomElim(try f.hyp(0, bottom), A)))
    proofs.append(("p_or_elim", try f.intro(aOrBottom, try f.n(.folOrElim(try f.hyp(0, aOrBottom), aa, fromBottom)))))
    proofs.append(("p_or_intro_l", try f.intro(A, try f.n(.folOrIntroL(hA, B)))))
    proofs.append(("p_or_intro_r", try f.intro(A, try f.n(.folOrIntroR(B, hA)))))

    proofs.append(("p_iff_intro", try f.n(.folIffIntro(aa, aa))))
    let aIffB = try f.n(.folIff(A, B))
    proofs.append(("p_iff_elim", try f.intro(aIffB, try f.intro(A, try f.n(.folIffElimL(try f.hyp(1, aIffB), hA))))))

    let aAndB = try f.n(.folAnd(A, B)), hAB = try f.hyp(0, aAndB)
    proofs.append(("p_and", try f.intro(aAndB, try f.n(.folAndIntro(try f.n(.folAndElimR(hAB)), try f.n(.folAndElimL(hAB)))))))

    let elem10 = try f.p("elem", try f.b(1), try f.b(0))
    let membersAreSets = try f.n(.folForall(body: try f.n(.folForall(body: try f.imp(elem10, try f.p("set", try f.b(1)))))))
    let cited = try f.n(.folForallElim(try f.n(.folForallElim(try f.n(.use(.theorem("members_are_sets"), [], membersAreSets)), try f.b(1))), try f.b(0)))
    proofs.append(("p_use", try f.n(.folForallIntro(body: try f.n(.folForallIntro(body:
        try f.intro(elem10, try f.n(.folImpliesElim(cited, try f.hyp(0, elem10))))))))))

    var def = "", proof = ""
    for (name, step) in proofs {
        let claim = Declaration(kind: .claim, name: name, root: f.t.conclusion(of: step)!)
        def += try render(claim, in: f.t) + "\n"
        proof += try render(proof: step, of: claim, in: f.t) + "\n"
    }

    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-emit-\(getpid())")
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: dir) }
    let defURL = dir.appendingPathComponent("p.fol.def"), prfURL = dir.appendingPathComponent("p.fol.proof")
    try def.write(to: defURL, atomically: true, encoding: .utf8)
    try proof.write(to: prfURL, atomically: true, encoding: .utf8)

    let proc = Process()
    proc.executableURL = URL(fileURLWithPath: ck)
    proc.arguments = [defURL.path, prfURL.path, repo.appendingPathComponent("base/axioms.fol.def").path]
    let out = Pipe(), err = Pipe()
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
