import Foundation
import IR
import Testing
@testable import FolDialect

private let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
    .deletingLastPathComponent()

private func script(_ name: String, _ arguments: [String]) throws -> (status: Int32, output: String) {
    let p = Process()
    p.executableURL = URL(fileURLWithPath: "/bin/bash")
    p.arguments = [repo.appendingPathComponent("scripts/\(name)").path] + arguments
    let out = Pipe()
    p.standardOutput = out
    p.standardError = out
    try p.run()
    let text = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    p.waitUntilExit()
    return (p.terminationStatus, text)
}

private struct BaseNotValid: Error { let output: String }

private let baseLibraries = Result { () throws -> URL in
    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-base-\(getpid())")
    let (status, output) = try script("check-base.sh", [dir.path])
    guard status == 0 else { throw BaseNotValid(output: output) }
    return dir
}

private func baseTextsOfRepo() throws -> [String] {
    try baseTexts(repo.appendingPathComponent("base"))
}

private func freshDirectory(_ name: String) throws -> URL {
    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-\(name)-\(getpid())")
    try? FileManager.default.removeItem(at: dir)
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    return dir
}

/// Every part valid, by `check-unit.sh` against base's libraries.
private func unitChecks(_ dir: URL) throws -> String {
    let (status, output) = try script("check-unit.sh", [dir.path, try baseLibraries.get().path])
    #expect(status == 0, "check-unit.sh:\n\(output)")
    return output
}

private struct Named: Request {
    let name: String
}

extension Pf {
    fileprivate mutating func eqReflAt(_ k: Int) throws -> NodeID {
        let eq0 = try p("eq", try b(0), try b(0))
        return try n(.folForallElim(try n(.use(.base("eq_refl"), [], try n(.folForall(body: eq0)))), try b(k)))
    }

    fileprivate mutating func forallIntro(_ body: NodeID) throws -> NodeID {
        try n(.folForallIntro(body: body))
    }

    fileprivate mutating func and(_ p: NodeID, _ q: NodeID) throws -> NodeID {
        try n(.folAndIntro(p, q))
    }

    fileprivate mutating func letter(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, .o))
    }
}

private func claim(_ name: String, _ proof: NodeID, _ t: Table) -> Declaration {
    Declaration(kind: .claim, name: name, root: t.conclusion(of: proof)!)
}

/// Decision 2: `p` used twice in one scope is one step, cited by its handle.
@Test
func aSubproofUsedTwiceInOneScopeIsWrittenOnce() throws {
    var f = Pf()
    let p = try f.eqReflAt(0)
    let proof = try f.forallIntro(try f.and(p, p))
    #expect(try render(proof: proof, of: claim("once", proof, f.t), in: f.t) == """
        proof once:
            fix f0
            _0 = use eq_refl
            _1 = forall_elim _0, f0
            _2 = and_intro _1, _1
            _3 = forall_intro _2
            qed _3

        """)
}

/// `p` depends on its scope's `f0`, so under two sibling `fix`es it is written twice; the closed `use` once.
@Test
func aSubproofInTwoSiblingScopesIsWrittenTwice() throws {
    var f = Pf()
    let p = try f.eqReflAt(0)
    let proof = try f.and(try f.forallIntro(p), try f.forallIntro(try f.and(p, p)))
    #expect(try render(proof: proof, of: claim("siblings", proof, f.t), in: f.t) == """
        proof siblings:
            fix f0
            _0 = use eq_refl
            _1 = forall_elim _0, f0
            _2 = forall_intro _1
            fix f0
            _3 = forall_elim _0, f0
            _4 = and_intro _3, _3
            _5 = forall_intro _4
            _6 = and_intro _2, _5
            qed _6

        """)
}

private func independent(_ f: inout Pf) throws -> NodeID {
    let q = try f.forallIntro(try f.eqReflAt(0))
    let a = try f.p("A")
    let b = try f.p("B")
    return try f.and(try f.intro(a, q), try f.intro(b, q))
}

/// A step that depends on no assumption or variable of a closing scope stays derived after it: `q`, written under
/// `assume A`, is cited under `assume B` — the `↔` of a congruence proved once, not once per direction.
@Test
func aStepIndependentOfAClosingScopeIsCitedAfterIt() throws {
    var f = Pf()
    let proof = try independent(&f)
    #expect(try render(proof: proof, of: claim("independent", proof, f.t), in: f.t) == """
        proof independent:
            _0 = assume A
            fix f0
            _1 = use eq_refl
            _2 = forall_elim _1, f0
            _3 = forall_intro _2
            _4 = implies_intro _3
            _5 = assume B
            _6 = implies_intro _3
            _7 = and_intro _4, _6
            qed _7

        """)
}

/// One node with a loose index is two facts under two binders, `eq(f0, f0)` and `eq(f1, f1)`; the closed `use` is one.
@Test
func oneNodeUnderTwoBindersIsTwoFacts() throws {
    var f = Pf()
    let p = try f.eqReflAt(0)
    let proof = try f.forallIntro(try f.and(p, try f.forallIntro(p)))
    #expect(try render(proof: proof, of: claim("binders", proof, f.t), in: f.t) == """
        proof binders:
            fix f0
            _0 = use eq_refl
            _1 = forall_elim _0, f0
            fix f1
            _2 = forall_elim _0, f1
            _3 = forall_intro _2
            _4 = and_intro _1, _3
            _5 = forall_intro _4
            qed _5

        """)
}

private func selfImplication(_ f: inout Pf) throws -> (root: NodeID, proof: NodeID) {
    let a = try f.letter(0)
    let root = try f.n(.ifolAll(.o, body: try f.imp(a, a)))
    let proof = try f.n(.isaAllIntro(.o, body: try f.intro(a, try f.hyp(0, a))))
    return (root, proof)
}

/// A statement whose spine binds a letter is a schema: the letter declared by its place, its proof without its intro.
@Test
func aSchemaIsDeclaredWithItsSpineLettersAndItsProofHasNoIntroForThem() throws {
    var f = Pf()
    let (root, proof) = try selfImplication(&f)
    let d = Declaration(kind: .schema(letters: ["A0"]), name: "selfImp", root: root)
    #expect(try render(d, in: f.t) == "schema selfImp [A0(0)]: (A0 -> A0)")
    #expect(try render(proof: proof, of: d, in: f.t) == """
        proof selfImp:
            _0 = assume A0
            _1 = implies_intro _0
            qed _1

        """)
}

private func underAForall(_ f: inout Pf) throws -> (root: NodeID, proof: NodeID) {
    let a = try f.letter(0)
    let set0 = try f.p("set", try f.b(0))
    let root = try f.n(.folForall(body: try f.imp(set0, try f.n(.ifolAll(.o, body: try f.imp(a, a))))))
    let proof = try f.forallIntro(try f.intro(set0, try f.n(.isaAllIntro(.o, body: try f.intro(a, try f.hyp(0, a))))))
    return (root, proof)
}

/// A letter under `∀` on the spine is declared at the top: it hoists across `∀` and the right of `→`.
@Test
func aLetterUnderAForallIsDeclaredAtTheTop() throws {
    var f = Pf()
    let (root, proof) = try underAForall(&f)
    let d = Declaration(kind: .schema(letters: ["A0"]), name: "hoisted", root: root)
    #expect(try render(d, in: f.t) == "schema hoisted [A0(0)]: forall b0. (set(b0) -> (A0 -> A0))")
    #expect(try render(proof: proof, of: d, in: f.t) == """
        proof hoisted:
            fix f0
            _0 = assume set(f0)
            _1 = assume A0
            _2 = implies_intro _1
            _3 = implies_intro _2
            _4 = forall_intro _3
            qed _4

        """)
}

private func citingHoisted(_ f: inout Pf, _ schemaRoot: NodeID) throws -> NodeID {
    let set0 = try f.p("set", try f.b(0))
    let eq00 = try f.p("eq", try f.b(0), try f.b(0))
    let atX = try f.n(.folImpliesElim(
        try f.n(.folForallElim(try f.n(.use(.theorem("hoisted"), [], schemaRoot)), try f.b(0))),
        try f.hyp(0, set0),
    ))
    return try f.forallIntro(try f.intro(set0, try f.n(.folSchemaInst(atX, eq00))))
}

/// A citation of the unit's schema is one `schema_inst` with every letter, ahead of the spine's `forall_elim`s.
@Test
func aCitationOfASchemaIsOneSchemaInstAheadOfItsForallElims() throws {
    var f = Pf()
    let (root, _) = try underAForall(&f)
    let proof = try citingHoisted(&f, root)
    #expect(try render(proof: proof, of: claim("cites", proof, f.t), in: f.t, letters: ["hoisted": ["A0"]]) == """
        proof cites:
            fix f0
            _0 = assume set(f0)
            _1 = schema_inst hoisted { A0: eq(f0, f0) }
            _2 = forall_elim _1, f0
            _3 = implies_elim _2, _0
            _4 = implies_intro _3
            _5 = forall_intro _4
            qed _5

        """)
}

@Test
func aNameBaseDeclaresStopsEmission() throws {
    var f = Pf()
    let p = try f.forallIntro(try f.eqReflAt(0))
    let unit = IR.Unit(
        table: f.t,
        statements: [Statement(name: "eq_refl", root: try #require(f.t.conclusion(of: p)), proof: p, theory: "T")],
    )
    #expect(throws: EmitError.declaredByBase("eq_refl")) {
        try emit(unit, to: try freshDirectory("clash"), base: try baseTextsOfRepo())
    }
}

/// `A.t1` and the lemma `L` in A's part, `B.t2` citing both in B's, which loads A's library: L's first citer is A's.
private func twoTheories(_ f: inout Pf) throws -> IR.Unit {
    let p = try f.forallIntro(try f.eqReflAt(0))
    let r = f.t.conclusion(of: p)!
    var lemma = Statement(lemma: Lemma(Named(name: "L")), root: r)
    lemma.proof = p
    let viaL = try f.n(.use(.lemma(Lemma(Named(name: "L"))), [], r))
    let t1 = Statement(name: "A.t1", root: r, proof: viaL, theory: "A")
    let both = try f.and(try f.n(.use(.theorem("A.t1"), [], r)), viaL)
    let t2 = Statement(name: "B.t2", root: f.t.conclusion(of: both)!, proof: both, theory: "B")
    return IR.Unit(table: f.t, statements: [t2, t1, lemma])
}

@Test
func aTheoremGoesInItsTheorysPartAndALemmaInItsFirstCitersPart() throws {
    var f = Pf()
    let dir = try freshDirectory("parts")
    let emitted = try emit(try twoTheories(&f), to: dir, base: try baseTextsOfRepo())
    #expect(emitted.parts.map(\.name) == ["A", "B"])
    #expect(emitted.parts.map(\.loads) == [[], ["A"]])
    #expect(Dictionary(uniqueKeysWithValues: emitted.statements.map { ($0.name, $0.part) }) == [
        "A.t1": "A",
        "L": "A",
        "B.t2": "B",
    ])
    #expect(try String(contentsOf: dir.appendingPathComponent("parts"), encoding: .utf8) == "A:\nB: A\n")
    let report = try unitChecks(dir)
    #expect(report.contains("Proved (2 of 2)") && report.contains("Proved (1 of 1)"))
}

/// A lemma no statement cites — its citer refused after the registry proved it — is the last part's, `_uncited`.
@Test
func aLemmaNoStatementCitesGoesInTheLastPart() throws {
    var f = Pf()
    let p = try f.forallIntro(try f.eqReflAt(0))
    let r = try #require(f.t.conclusion(of: p))
    var orphan = Statement(lemma: Lemma(Named(name: "orphan")), root: r)
    orphan.proof = p
    let unit = IR.Unit(table: f.t, statements: [orphan, Statement(name: "A.t", root: r, proof: p, theory: "A")])
    let dir = try freshDirectory("uncited")
    let emitted = try emit(unit, to: dir, base: try baseTextsOfRepo())
    #expect(emitted.parts.map(\.name) == ["A", "_uncited"])
    #expect(emitted.statements.first { $0.name == "orphan" }?.part == "_uncited")
    _ = try unitChecks(dir)
}

/// A part over its bound is split, each piece citing only earlier ones, and checked in order.
@Test
func aPartOverItsBoundIsSplitInOrder() throws {
    var f = Pf()
    let dir = try freshDirectory("split")
    let emitted = try emit(try twoTheories(&f), to: dir, base: try baseTextsOfRepo(), partBytes: 1)
    #expect(emitted.parts.map(\.name) == ["A", "A.2", "B"])
    #expect(emitted.parts.map(\.loads) == [[], ["A"], ["A", "A.2"]])
    _ = try unitChecks(dir)
}

/// Every claim and schema a unit emits is Proved by the real checker, part by part: the sharing tests' proofs, a name
/// and
/// a predicate with a reserved segment, a schema and its citation.
@Test
func whatEmissionWritesTheCheckerProves() throws {
    var f = Pf()
    var statements = [Statement]()
    let p = try f.eqReflAt(0)
    for (name, proof) in [
        ("once", try f.forallIntro(try f.and(p, p))),
        ("siblings", try f.and(try f.forallIntro(p), try f.forallIntro(try f.and(p, p)))),
        ("binders", try f.forallIntro(try f.and(p, try f.forallIntro(p)))),
        ("independent", try independent(&f)),
    ] {
        statements.append(Statement(
            name: name,
            root: try #require(f.t.conclusion(of: proof)),
            proof: proof,
            theory: "T",
        ))
    }
    let not = try f.p("Bool.not")
    let reserved = try f.intro(not, try f.hyp(0, not))
    statements.append(Statement(
        name: "T.ok.false",
        root: try #require(f.t.conclusion(of: reserved)),
        proof: reserved,
        theory: "T",
    ))
    let (root, proof) = try underAForall(&f)
    statements.append(Statement(name: "hoisted", root: root, proof: proof, theory: "T"))
    let cites = try citingHoisted(&f, root)
    statements.append(Statement(
        name: "cites",
        root: try #require(f.t.conclusion(of: cites)),
        proof: cites,
        theory: "T",
    ))
    let dir = try freshDirectory("checked")
    let emitted = try emit(IR.Unit(table: f.t, statements: statements), to: dir, base: try baseTextsOfRepo())
    #expect(emitted.statements.first { $0.name == "once" }.map { [$0.written, $0.tree, $0.dag] } == [4, 6, 4])
    let report = try unitChecks(dir)
    #expect(report.contains("Proved (6 of 6)  Schemas proved (1 of 1)"))
}
