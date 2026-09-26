import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func read(_ file: String, at types: [IRType] = [], into t: inout Table) throws -> Proposition {
    var f = Forest()
    let body = try f.parse(Array(file.utf8))
    let d = Decode(forest: f)
    let (e, _) = try d.proofFile(body)
    var terms = try Terms(decode: d, constants: try testConstants(), file: e, at: types)
    return try terms.statement(e.prop, try testClasses(), in: &t)
}

private let memT = IRType.fn(.i, .fn(.i, .o))
private let memAa = trueprop(app(const("ZF_Base.mem"), free("a"), free("A")))
private let refl = trueprop(app(const("IFOL.eq", typeA), free("a"), free("a")))

/// Isabelle's closure (`forall_intr_variables_term`): the frees in first-occurrence order, the first outermost.
@Test func aStatementReadsClosedOverItsFreesTheFirstOutermost() throws {
    var t = Table()
    let got = try read(proofFile(frees: [("a", i), ("A", i)], prop: memAa), into: &t)
    let mem = try t.intern(.isaConst("ZF_Base.mem", memT, args: [try t.intern(.isaBound(1, .i)), try t.intern(.isaBound(0, .i))]))
    let closed = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: mem))))
    #expect(got == .claim(closed, classPremises: 0))
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

@Test func aPolymorphicStatementReadsAtItsInstance() throws {
    var t = Table()
    let file = proofFile(tfrees: ["'a"], frees: [("a", typeA)], prop: refl)
    for T in [IRType.i, .o] {
        let a = try t.intern(.isaBound(0, T))
        let eq = try t.intern(.isaConst("IFOL.eq", .fn(T, .fn(T, .o)), args: [a, a]))
        #expect(try read(file, at: [T], into: &t) == .claim(try t.intern(.ifolAll(T, body: eq)), classPremises: 0))
    }
    #expect(throws: MalformedExport.instanceArity(expected: 1, found: 0)) { try read(file, into: &t) }
}

@Test func aPolymorphicStatementReadsAsStated() throws {
    var t = Table()
    let a = IRType.variable("'a")
    let x = try t.intern(.isaBound(0, a))
    let eq = try t.intern(.isaConst("IFOL.eq", .fn(a, .fn(a, .o)), args: [x, x]))
    let got = try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)], prop: refl), at: [a], into: &t)
    #expect(got == .claim(try t.intern(.ifolAll(a, body: eq)), classPremises: 0))
}

@Test func aSortedTypeVariableInTheHeaderIsMalformed() {
    var t = Table()
    let header = node(node(node("'a"), node(node("IFOL.term"))))
    let file = header + node(node(node(node("a"), node(typeA))) + node(node(refl) + node(pnop)))
    #expect(throws: MalformedExport.sortedTypeVariable("'a")) { try read(file, at: [.variable("'a")], into: &t) }
}

@Test func aRepeatedTypeVariableInTheHeaderIsMalformed() {
    var t = Table()
    #expect(throws: MalformedExport.tfreesHeader(["'a", "'a"])) {
        try read(proofFile(tfrees: ["'a", "'a"], frees: [("a", typeA)], prop: refl), at: [.i, .i], into: &t)
    }
}

/// The class `term` has no axioms, so `OFCLASS(T, term)` holds of every `T` it is asked of: a
/// premise stating it is bookkeeping, and the count says how many discharges a citation absorbs.
@Test func leadingClassPremisesAreStrippedAndCounted() throws {
    var t = Table()
    let got = try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)],
                                 prop: app(const("Pure.imp"), ofclass(typeA, "IFOL.term"), refl)), at: [.i], into: &t)
    let a = try t.intern(.isaBound(0, .i))
    let eq = try t.intern(.isaConst("IFOL.eq", memT, args: [a, a]))
    #expect(got == .claim(try t.intern(.ifolAll(.i, body: eq)), classPremises: 1))
}

@Test func aStatementThatIsOnlyAClassFactIsBookkeeping() throws {
    var t = Table()
    #expect(try read(proofFile(frees: [], prop: ofclass(i, "IFOL.term")), into: &t) == .classFact("IFOL.term"))
}

@Test func aClassWithAxiomsIsNotAbsorbed() {
    var t = Table()
    #expect(throws: ReaderRefusal.ofclass("T.withAxioms")) {
        try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)],
                           prop: app(const("Pure.imp"), ofclass(typeA, "T.withAxioms"), refl)), at: [.i], into: &t)
    }
    #expect(throws: MalformedExport.undeclaredClass("T.nowhere")) {
        try read(proofFile(frees: [], prop: ofclass(i, "T.nowhere")), into: &t)
    }
}

/// `elim_format`'s `W :: prop` is a formula variable: Pure's `prop` reads as `o` (DESIGN §4.3).
@Test func aMetaLevelPropositionalVariableReadsAsAFormulaVariable() throws {
    var t = Table()
    let got = try read(proofFile(frees: [("a", i), ("A", i), ("W", prop)], prop: app(const("Pure.imp"), memAa, free("W"))), into: &t)
    let mem = try t.intern(.isaConst("ZF_Base.mem", memT, args: [try t.intern(.isaBound(2, .i)), try t.intern(.isaBound(1, .i))]))
    let body = try t.intern(.folImplies(mem, try t.intern(.isaBound(0, .o))))
    let closed = try [IRType.o, .i, .i].reduce(body) { b, T in try t.intern(.ifolAll(T, body: b)) }
    #expect(got == .claim(closed, classPremises: 0))
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

private func zfBase(_ name: String, at types: [IRType] = []) throws -> (Table, Proposition)? {
    let root = "data/zf_export"
    guard FileManager.default.fileExists(atPath: "\(root)/ZF.ZF_Base/proofs") else {
        Issue.record("export missing at \(root) — run scripts/03-export-zf.sh from the repo root")
        return nil
    }
    var export = try Export(root: root)
    let serial = try #require(try export.names("ZF.ZF_Base").first { $0.value == name }?.key)
    let body = try export.forest.parse(contentsOf: "\(root)/ZF.ZF_Base/proofs/\(serial)")
    let d = Decode(forest: export.forest)
    let (e, _) = try d.proofFile(body)
    var terms = try Terms(decode: d, constants: export.constants, file: e, at: types)
    var t = Table()
    let statement = try terms.statement(e.prop, export.classes, in: &t)
    return (t, statement)
}

@Test func ballDefReadsEtaLongAsAnIff() throws {
    guard case (var t, let got)? = try zfBase("ZF_Base.Ball_def") else { return }
    let P = IRType.fn(.i, .o)
    let x = try t.intern(.isaBound(0, .i)), A = try t.intern(.isaBound(1, .i)), AunderX = try t.intern(.isaBound(2, .i))
    let Px = try t.intern(.isaVarApp(head: try t.intern(.isaBound(1, P)), args: [x]))
    let ball = try t.intern(.isaConst("ZF_Base.Ball", .fn(.i, .fn(P, .o)), args: [A, try t.intern(.isaAbs(.i, body: Px))]))
    let mem = try t.intern(.isaConst("ZF_Base.mem", memT, args: [x, AunderX]))
    let all = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(mem, Px))))
    let closed = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(P, body: try t.intern(.folIff(ball, all))))))
    #expect(got == .claim(closed, classPremises: 0))
}

@Test func splitDefReadsAtAnInstance() throws {
    guard case (_, .claim(_, 0))? = try zfBase("ZF_Base.split_def", at: [.i]) else {
        Issue.record("split_def does not read at i")
        return
    }
}

@Test func splitDefReadsAsStated() throws {
    let a = IRType.variable("'a")
    guard case let (t, .claim(root, 0))? = try zfBase("ZF_Base.split_def", at: [a]) else {
        Issue.record("split_def does not read as stated")
        return
    }
    guard case .ifolAll(.fn(.i, .fn(.i, a)), _) = t[root] else {
        Issue.record("\(t[root])")
        return
    }
}
