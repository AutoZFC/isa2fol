import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func read(_ file: String, at types: [IRType] = [], into t: inout Table) throws -> NodeID {
    var f = Forest()
    let body = try f.parse(Array(file.utf8))
    let d = Decode(forest: f)
    let (e, _) = try d.proofFile(body)
    var terms = try Terms(decode: d, constants: try testConstants(), classes: try testClasses(), file: e, at: types)
    return try terms.statement(e.prop, in: &t)
}

private let memT = IRType.fn(.i, .fn(.i, .o))
private let memAa = trueprop(app(const("ZF_Base.mem"), free("a"), free("A")))
private let refl = trueprop(app(const("IFOL.eq", typeA), free("a"), free("a")))

/// Isabelle's closure (`forall_intr_variables_term`): the frees in first-occurrence order, the first outermost.
@Test func aStatementReadsClosedOverItsFreesTheFirstOutermost() throws {
    var t = Table()
    let got = try read(proofFile(frees: [("a", i), ("A", i)], prop: memAa), into: &t)
    let mem = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [try t.intern(.isaBound(1, .i)), try t.intern(.isaBound(0, .i))]))
    let closed = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: mem))))
    #expect(got == closed)
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
        let eq = try t.intern(.isaConst(.primitive(.ifol(.eq)), .fn(T, .fn(T, .o)), args: [a, a]))
        #expect(try read(file, at: [T], into: &t) == (try t.intern(.ifolAll(T, body: eq))))
    }
    #expect(throws: MalformedExport.instanceArity(expected: 1, found: 0)) { try read(file, into: &t) }
}

@Test func aPolymorphicStatementReadsAsStated() throws {
    var t = Table()
    let a = IRType.variable("'a")
    let x = try t.intern(.isaBound(0, a))
    let eq = try t.intern(.isaConst(.primitive(.ifol(.eq)), .fn(a, .fn(a, .o)), args: [x, x]))
    let got = try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)], prop: refl), at: [a], into: &t)
    #expect(got == (try t.intern(.ifolAll(a, body: eq))))
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

/// `unconstrainT` states `refl`'s class as a premise: an ordinary one (DESIGN §4.3a 5).
@Test func aClassPremiseIsAnOrdinaryPremise() throws {
    var t = Table()
    let got = try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)],
                                 prop: app(const("Pure.imp"), ofclass(typeA, "IFOL.term"), refl)), at: [.i], into: &t)
    let a = try t.intern(.isaBound(0, .i))
    let eq = try t.intern(.isaConst(.primitive(.ifol(.eq)), memT, args: [a, a]))
    let member = try t.intern(.isaOfClass(.i, ifolTerm))
    #expect(got == (try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(member, eq))))))
}

@Test func aClassFactIsAFormula() throws {
    var t = Table()
    let got = try read(proofFile(frees: [], prop: ofclass(i, "IFOL.term")), into: &t)
    #expect(got == (try t.intern(.isaOfClass(.i, ifolTerm))))
}

/// Nothing is dropped, so a class with axioms reads like any other.
@Test func aClassWithAxiomsReadsLikeAnyClass() throws {
    var t = Table()
    let got = try read(proofFile(tfrees: ["'a"], frees: [("a", typeA)],
                                 prop: app(const("Pure.imp"), ofclass(typeA, "T.withAxioms"), refl)), at: [.i], into: &t)
    guard case let .ifolAll(.i, body) = t[got], case let .folImplies(member, _) = t[body] else {
        Issue.record("\(t[got])")
        return
    }
    #expect(t[member] == .isaOfClass(.i, TypeClass(.ifol, "T.withAxioms")))
    #expect(throws: MalformedExport.undeclaredClass("T.nowhere")) {
        try read(proofFile(frees: [], prop: ofclass(i, "T.nowhere")), into: &t)
    }
}

/// `elim_format`'s `W :: prop` is a formula variable: Pure's `prop` reads as `o` (DESIGN §4.3).
@Test func aMetaLevelPropositionalVariableReadsAsAFormulaVariable() throws {
    var t = Table()
    let got = try read(proofFile(frees: [("a", i), ("A", i), ("W", prop)], prop: app(const("Pure.imp"), memAa, free("W"))), into: &t)
    let mem = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [try t.intern(.isaBound(2, .i)), try t.intern(.isaBound(1, .i))]))
    let body = try t.intern(.folImplies(mem, try t.intern(.isaBound(0, .o))))
    let closed = try [IRType.o, .i, .i].reduce(body) { b, T in try t.intern(.ifolAll(T, body: b)) }
    #expect(got == closed)
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

private func zfBase(_ name: String, at types: [IRType] = []) throws -> (Table, NodeID)? {
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
    var terms = try Terms(decode: d, constants: export.constants, classes: export.classes, file: e, at: types)
    var t = Table()
    let statement = try terms.statement(e.prop, in: &t)
    return (t, statement)
}

@Test func ballDefReadsEtaLongAsAnIff() throws {
    guard case (var t, let got)? = try zfBase("ZF_Base.Ball_def") else { return }
    let P = IRType.fn(.i, .o)
    let x = try t.intern(.isaBound(0, .i)), A = try t.intern(.isaBound(1, .i)), AunderX = try t.intern(.isaBound(2, .i))
    let Px = try t.intern(.isaVarApp(head: try t.intern(.isaBound(1, P)), args: [x]))
    let ball = try t.intern(.isaConst(defined(.zf, "ZF_Base.Ball", .object), .fn(.i, .fn(P, .o)), args: [A, try t.intern(.isaAbs(.i, body: Px))]))
    let mem = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, AunderX]))
    let all = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(mem, Px))))
    let closed = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(P, body: try t.intern(.folIff(ball, all))))))
    #expect(got == closed)
}

@Test func splitDefReadsAtAnInstance() throws {
    guard try zfBase("ZF_Base.split_def", at: [.i]) != nil else {
        Issue.record("split_def does not read at i")
        return
    }
}

@Test func splitDefReadsAsStated() throws {
    let a = IRType.variable("'a")
    guard case let (t, root)? = try zfBase("ZF_Base.split_def", at: [a]) else {
        Issue.record("split_def does not read as stated")
        return
    }
    guard case .ifolAll(.fn(.i, .fn(.i, a)), _) = t[root] else {
        Issue.record("\(t[root])")
        return
    }
}
