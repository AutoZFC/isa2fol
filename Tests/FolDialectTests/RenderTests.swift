import Foundation
import IR
import Testing
@testable import FolDialect

private struct Fol {
    var t = Table()

    mutating func b(_ k: Int) throws -> NodeID {
        try t.intern(.folBound(k))
    }

    mutating func p(_ n: String, _ args: NodeID...) throws -> NodeID {
        try t.intern(.folPred(.base(n), args: args))
    }

    mutating func all(_ body: NodeID) throws -> NodeID {
        try t.intern(.folForall(body: body))
    }

    mutating func ex(_ body: NodeID) throws -> NodeID {
        try t.intern(.folExists(body: body))
    }

    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try t.intern(.folImplies(a, b))
    }

    mutating func text(_ root: NodeID) throws -> String {
        try render(formula: root, in: t)
    }
}

@Test
func aGuardedForallRendersWithLevelNames() throws {
    var f = Fol()
    let root = try f.all(try f.all(try f.imp(try f.p("set", try f.b(1)), try f.p("elem", try f.b(1), try f.b(0)))))
    #expect(try f.text(root) == "forall b0. forall b1. (set(b0) -> elem(b0, b1))")
}

/// `level = depth − 1 − k`: the same index names different binders at different depths.
@Test
func aBoundIndexIsNamedByItsBindersLevel() throws {
    var f = Fol()
    let inner = try f.all(try f.p("elem", try f.b(0), try f.b(2)))
    let root = try f.all(try f.all(try f.imp(try f.p("elem", try f.b(1), try f.b(0)), inner)))
    #expect(try f.text(root) == "forall b0. forall b1. (elem(b0, b1) -> (forall b2. elem(b2, b0)))")
}

@Test
func everyConnectiveHasTheCheckersSyntax() throws {
    var f = Fol()
    let set0 = try f.p("set", try f.b(0))
    let notBottom = try f.t.intern(.folNot(try f.t.intern(.folBottom)))
    let conj = try f.t.intern(.folAnd(set0, notBottom))
    let iff = try f.t.intern(.folIff(try f.p("elem", try f.b(0), try f.b(0)), set0))
    let root = try f.ex(try f.t.intern(.folOr(conj, iff)))
    #expect(try f.text(root) == "exists b0. ((set(b0) & ~false) | (elem(b0, b0) <-> set(b0)))")
    let negatedForall = try f.t.intern(.folNot(try f.all(set0)))
    #expect(try f.text(negatedForall) == "~(forall b0. set(b0))")
    #expect(try f.text(try f.p("nullary")) == "nullary")
}

@Test
func aDeclarationRendersAsItsLine() throws {
    var f = Fol()
    let body = try f.all(try f.p("set", try f.b(0)))
    #expect(try render(Declaration(kind: .claim, name: "QPair.QPair_iff", root: body), in: f.t)
        == "claim QPair.QPair_iff: forall b0. set(b0)")
    #expect(try render(
        Declaration(kind: .definition(predicate: "ZF_Base.Pow"), name: "ZF_Base.Pow_def", root: body),
        in: f.t,
    )
        == "@def(ZF_Base.Pow) axiom ZF_Base.Pow_def: forall b0. set(b0)")
}

@Test
func qualifiedNamesPrimesAndFactIndicesAreNames() throws {
    var f = Fol()
    for name in ["ZF_Base.mem", "IFOL.allE'", "Univ.rank_rls.4", "set", "eq_refl"] {
        #expect(try f.text(try f.p(name)) == name)
    }
}

/// A segment after the first that the checker reads as a keyword is written quoted; the name is unchanged.
@Test
func aReservedSegmentAfterTheFirstIsQuoted() throws {
    var f = Fol()
    for (name, written) in [
        ("Com.bexp.false", "Com.bexp.\"false\""),
        ("FOL.excluded_middle", "FOL.\"excluded_middle\""),
        ("Bool.not", "Bool.\"not\""),
        ("T.use.4", "T.\"use\".4"),
    ] {
        #expect(try f.text(try f.p(name)) == written)
    }
}

@Test
func aMalformedNameIsRefused() throws {
    var f = Fol()
    for bad in ["1bad", "forall", "a..b", "a.", ".a", "ZF Base", "a'b", "mem(4)", "use.T"] {
        #expect(throws: RenderError.notAName(bad)) { try f.text(try f.p(bad)) }
    }
    let body = try f.p("set", try f.b(0))
    #expect(throws: RenderError.notAName("claim")) {
        try render(Declaration(kind: .claim, name: "claim", root: try f.all(body)), in: f.t)
    }
}

@Test
func anOpenRootIsRefused() throws {
    var f = Fol()
    let open = try f.p("set", try f.b(0))
    #expect(throws: RenderError.notClosed(open)) { try f.text(open) }
}

@Test
func anIsaNodeIsRefused() throws {
    var f = Fol()
    let a = try f.t.intern(.isaFree("a", .i))
    let atom = try f.t.intern(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [a, a]))
    let root = try f.t.intern(.folAnd(try f.t.intern(.folBottom), atom))
    #expect(throws: RenderError.sourceKind(atom)) { try f.text(root) }
}

/// A letter is a schema's alone: a formula or a claim holding one is refused, a schema declaration binds it.
@Test
func aLetterOutsideASchemaIsRefused() throws {
    var f = Fol()
    let letter = try f.t.intern(.isaBound(0, .o))
    let schema = try f.t.intern(.ifolAll(.o, body: try f.imp(letter, letter)))
    #expect(throws: RenderError.schema(schema)) { try f.text(schema) }
}

/// ⚠ THE CHECKER'S GRAMMAR IS THE ONLY AUTHORITY. Every construct `render` emits is fed to
/// the real checker; `probe_bottom` PROVES something only true if `false` is ⊥ — a mere parse
/// would accept `False`, which lexes as a nullary predicate.
@Test
func theRealCheckerAcceptsWhatRenderEmits() throws {
    let ck = ProcessInfo.processInfo.environment["PROOF_CHECKER"]
        ?? NSString(string: "~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker").expandingTildeInPath
    try #require(FileManager.default.isExecutableFile(atPath: ck), "no proof_checker at \(ck); set PROOF_CHECKER")
    let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
        .deletingLastPathComponent().deletingLastPathComponent()
    let axioms = repo.appendingPathComponent("base/axioms.fol.def")

    var f = Fol()
    let membersAreSets = try f.all(try f.all(try f.imp(
        try f.p("elem", try f.b(1), try f.b(0)),
        try f.p("set", try f.b(1)),
    )))
    let notBottom = try f.t.intern(.folNot(try f.t.intern(.folBottom)))
    let set0 = try f.p("set", try f.b(0))
    let every = try f.ex(try f.t.intern(.folOr(
        try f.t.intern(.folAnd(set0, notBottom)),
        try f.t.intern(.folIff(
            try f.p("elem", try f.b(0), try f.b(0)),
            try f.t.intern(.folNot(try f.all(try f.p("elem", try f.b(0), try f.b(1))))),
        )),
    )))
    let decls = [
        Declaration(kind: .claim, name: "probe", root: membersAreSets),
        Declaration(kind: .claim, name: "probe_bottom", root: notBottom),
        Declaration(kind: .claim, name: "probe_syntax", root: every),
    ]
    let def = try decls.map { try render($0, in: f.t) }.joined(separator: "\n") + "\n"
    let proof = """
        proof probe:
            _a = use members_are_sets
            qed _a

        proof probe_bottom:
            _a = assume false
            _b = not_intro _a
            qed _b

        proof probe_syntax: UNPROVED

        """

    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-render-\(getpid())")
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: dir) }
    let defURL = dir.appendingPathComponent("p.fol.def")
    let prfURL = dir.appendingPathComponent("p.fol.proof")
    try def.write(to: defURL, atomically: true, encoding: .utf8)
    try proof.write(to: prfURL, atomically: true, encoding: .utf8)

    let proc = Process()
    proc.executableURL = URL(fileURLWithPath: ck)
    proc.arguments = [defURL.path, prfURL.path, axioms.path]
    let out = Pipe()
    let err = Pipe()
    proc.standardOutput = out
    proc.standardError = err
    try proc.run()
    let stdout = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let stderr = String(decoding: err.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    proc.waitUntilExit()

    #expect(proc.terminationStatus == 0, "checker rejected what render emits:\n\(def)\n\(stdout)\(stderr)")
    #expect(stderr.isEmpty, "stderr must be empty: \(stderr)")
    #expect(stdout.contains("+ probe\n") || stdout.contains("+ probe "), "probe did not prove:\n\(stdout)")
    #expect(stdout.contains("+ probe_bottom"), "probe_bottom did not prove -- is false rendered as ⊥?\n\(stdout)")
}
