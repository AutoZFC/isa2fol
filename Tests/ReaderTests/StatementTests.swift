import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func read(_ file: String, into t: inout Table) throws -> Outcome {
    var f = Forest()
    let body = try f.parse(Array(file.utf8))
    return try StatementReader(decode: Decode(forest: f), constants: try testConstants()).read(body, into: &t)
}

private let memAa = trueprop(app(const("ZF_Base.mem"), free("a"), free("A")))

@Test func aProofFileReadsToItsStatementAndItsOrderedFrees() throws {
    var t = Table()
    let got = try read(proofFile(frees: [("a", i), ("A", i)], prop: memAa), into: &t)
    let a = try t.intern(.isaFree("a", .i)), A = try t.intern(.isaFree("A", .i))
    let mem = try t.intern(.isaConst("ZF_Base.mem", .fn(.i, .fn(.i, .o)), args: [a, A]))
    #expect(got == .translated(root: mem, frees: [a, A]))
}

@Test func aTypeVariableInTheHeaderRefusesTheWholeStatement() throws {
    var t = Table()
    #expect(try read(proofFile(tfrees: ["'a"], frees: [("a", i), ("A", i)], prop: memAa), into: &t)
            == .refused(.typeVariable("'a")))
}

@Test func aFreeOfAPolymorphicTypeRefusesTheWholeStatement() throws {
    var t = Table()
    #expect(try read(proofFile(frees: [("a", i), ("A", typeA)], prop: memAa), into: &t) == .refused(.typeVariable("'a")))
}

@Test func theFreesHeaderMustBeThePropositionsFreesInFirstOccurrenceOrder() throws {
    var t = Table()
    #expect(throws: MalformedExport.freesHeader(header: ["A", "a"], occurring: ["a", "A"])) {
        try read(proofFile(frees: [("A", i), ("a", i)], prop: memAa), into: &t)
    }
    #expect(throws: MalformedExport.freesHeader(header: ["a", "A", "b"], occurring: ["a", "A"])) {
        try read(proofFile(frees: [("a", i), ("A", i), ("b", i)], prop: memAa), into: &t)
    }
}

@Test func aFactIndexIsSpelledAsAFinalSegment() throws {
    #expect(try claimName("Arith.raw_add.simps(1)") == "Arith.raw_add.simps.1")
    #expect(try claimName("ZF_Base.CollectI") == "ZF_Base.CollectI")
    #expect(try claimName("QPair.qsum'(12)") == "QPair.qsum'.12")
}

@Test func aNameWithADigitInitialSegmentIsRefused() {
    #expect(throws: ReaderRefusal.nameSegment("T.3foo")) { try claimName("T.3foo") }
    #expect(throws: ReaderRefusal.nameSegment("T..foo")) { try claimName("T..foo") }
}

private func zfBase() throws -> (Table, [String: Read])? {
    let root = "data/zf_export"
    guard FileManager.default.fileExists(atPath: "\(root)/ZF.ZF_Base/proofs") else {
        Issue.record("export missing at \(root) — run scripts/03-export-zf.sh from the repo root")
        return nil
    }
    var export = try Export(root: root)
    var t = Table()
    let reads = try export.statements("ZF.ZF_Base", into: &t)
    return (t, Dictionary(uniqueKeysWithValues: reads.compactMap { r in r.name.map { ($0, r) } }))
}

@Test func ballDefReadsEtaLongAsAnIff() throws {
    guard case (var t, let reads)? = try zfBase() else { return }
    let read = try #require(reads["ZF_Base.Ball_def"])
    let A = try t.intern(.isaFree("A", .i)), P = try t.intern(.isaFree("P", .fn(.i, .o)))
    let x = try t.intern(.isaBound(0, .i))
    let Px = try t.intern(.isaVarApp(head: P, args: [x]))
    let ball = try t.intern(.isaConst("ZF_Base.Ball", .fn(.i, .fn(.fn(.i, .o), .o)), args: [A, try t.intern(.isaAbs(.i, body: Px))]))
    let mem = try t.intern(.isaConst("ZF_Base.mem", .fn(.i, .fn(.i, .o)), args: [x, A]))
    let all = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(mem, Px))))
    #expect(read.outcome == .translated(root: try t.intern(.folIff(ball, all)), frees: [A, P]))
}

@Test func splitDefIsRefusedForItsTypeVariable() throws {
    guard let (_, reads) = try zfBase() else { return }
    let read = try #require(reads["ZF_Base.split_def"])
    guard case .refused(.typeVariable) = read.outcome else {
        Issue.record("expected a type-variable refusal, got \(read.outcome)")
        return
    }
}

@Test func aMalformedFileIsReportedWithItsPath() throws {
    let root = FileManager.default.temporaryDirectory.appendingPathComponent("isa2fol-\(UUID())").path
    defer { try? FileManager.default.removeItem(atPath: root) }
    for dir in ["ZF.T/theory", "ZF.T/proofs"] {
        try FileManager.default.createDirectory(atPath: "\(root)/\(dir)", withIntermediateDirectories: true)
    }
    let consts = constEntity("IFOL.Trueprop", parameters: [], scheme: fn(o, prop))
        + constEntity("ZF_Base.mem", parameters: [], scheme: fn(i, fn(i, o)))
    try consts.write(toFile: "\(root)/ZF.T/theory/consts", atomically: true, encoding: .utf8)
    try proofFile(frees: [("A", i), ("a", i)], prop: memAa).write(toFile: "\(root)/ZF.T/proofs/7", atomically: true, encoding: .utf8)
    var export = try Export(root: root)
    var t = Table()
    do {
        _ = try export.statements("ZF.T", into: &t)
        Issue.record("expected a ReadFailure")
    } catch let failure as ReadFailure {
        #expect(failure.file == "ZF.T/proofs/7")
        #expect(failure.error as? MalformedExport == .freesHeader(header: ["A", "a"], occurring: ["a", "A"]))
    }
}

/// `elim_format` states a rule over `W :: prop`; FOUNDATION S4 classifies an arity-0 propositional variable out.
@Test func aMetaLevelPropositionalVariableIsRefusedByName() throws {
    var t = Table()
    let prop = app(const("Pure.imp"), memAa, free("W"))
    #expect(try read(proofFile(frees: [("a", i), ("A", i), ("W", typeT("prop"))], prop: prop), into: &t)
            == .refused(.propositionalVariable("W")))
}
