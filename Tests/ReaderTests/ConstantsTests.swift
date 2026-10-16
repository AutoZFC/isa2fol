import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func load(_ c: inout Constants, family: Family = .zf, foundation: Bool = false, _ entities: String...) throws {
    var f = Forest()
    let body = try f.parse(Array(entities.joined().utf8))
    try c.load(body, family: family, foundation: foundation, in: f)
}

private let a = IsaType.tfree("'a", sort: [])
private let b = IsaType.tfree("'b", sort: [])
private let iT = IsaType.type("ZF_Base.i", [])
private let oT = IsaType.type("IFOL.o", [])
private func fnT(_ x: IsaType, _ y: IsaType) -> IsaType { .type("fun", [x, y]) }

@Test func aConstantLoadsItsParametersInOrderItsSchemeAndItsTheorysFamily() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: ["'b", "'a"], scheme: fn(tfree("'a"), tfree("'b"))))
    #expect(c["T.k"] == Constants.Declaration(parameters: ["'b", "'a"], scheme: fnT(a, b), family: .zf, foundation: false))
    #expect(c["T.absent"] == nil)
}

@Test func instantiationSubstitutesTypeArgumentsByPosition() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: ["'b", "'a"], scheme: fn(tfree("'a"), tfree("'b"))))
    #expect(try c.instantiate("T.k", [iT, oT]) == fnT(oT, iT))
}

@Test func aGroundConstantInstantiatesWithNoArguments() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: [], scheme: fn(i, o)))
    #expect(try c.instantiate("T.k", []) == fnT(iT, oT))
}

@Test func constantsFromSeveralFilesShareOneTable() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: [], scheme: i))
    try load(&c, constEntity("U.k", parameters: [], scheme: o))
    #expect(try c.instantiate("T.k", []) == iT)
    #expect(try c.instantiate("U.k", []) == oT)
}

@Test func aConstantDeclaredTwiceIsMalformed() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: [], scheme: i))
    #expect(throws: MalformedExport.duplicateConstant("T.k")) {
        try load(&c, constEntity("T.k", parameters: [], scheme: i))
    }
}

@Test func anUndeclaredConstantIsMalformed() {
    #expect(throws: MalformedExport.undeclaredConstant("T.k")) { try Constants().instantiate("T.k", []) }
    #expect(throws: MalformedExport.undeclaredConstant("T.k")) { try Constants().reading("T.k") }
}

@Test func aTypeArgumentCountOtherThanTheParameterCountIsMalformed() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: ["'a"], scheme: fn(tfree("'a"), o)))
    #expect(throws: MalformedExport.typeArgumentCount(constant: "T.k", declared: 1, found: 2)) {
        try c.instantiate("T.k", [iT, iT])
    }
}

@Test func aSchemeWhoseVariablesAreNotExactlyTheParametersIsMalformed() {
    let schemes = [
        ("T.undeclared", ["'a"], fn(tfree("'a"), tfree("'b"))),
        ("T.unused", ["'a", "'b"], fn(tfree("'a"), o)),
        ("T.repeated", ["'a", "'a"], fn(tfree("'a"), o)),
        ("T.schematic", ["'a"], fn(tvar(["'a"]), o)),
        ("T.sorted", ["'a"], fn(tfree("'a", "Foo.bar"), o)),
    ]
    for (name, parameters, scheme) in schemes {
        var c = Constants()
        #expect(throws: MalformedExport.schemeVariables(constant: name)) {
            try load(&c, constEntity(name, parameters: parameters, scheme: scheme))
        }
    }
}

@Test func aFileChildThatIsNotAnEntityIsMalformed() {
    var c = Constants()
    #expect(throws: MalformedExport.notAnEntity(tag: "thm")) { try load(&c, element("thm", [("name", "x")], [])) }
}

@Test func anEntityWithoutItsBodyIsMalformed() {
    var c = Constants()
    #expect(throws: MalformedExport.bodyLength(expected: 2, found: 0)) {
        try load(&c, element("entity", [("name", "T.k")], []))
    }
}

/// How a name is read is ONE function (DESIGN §4.3b 2).
@Test func eachKindOfConstantHasItsReading() throws {
    let c = try testConstants()
    #expect(try c.reading("IFOL.Trueprop") == .erased)
    #expect(try c.reading("IFOL.conj") == .and)
    #expect(try c.reading("Pure.all") == .metaAll)
    #expect(try c.reading("Pure.eq") == .metaEquality)
    #expect(try c.reading("Pure.dummy_pattern") == .hidden)
    #expect(try c.reading("ZF_Base.mem") == .constant(.primitive(.zf(.mem))))
    #expect(try c.reading("IFOL.eq") == .constant(.primitive(.ifol(.eq))))
    #expect(try c.reading("IFOL.iff") == .constant(defined(.ifol, "IFOL.iff", .object)))
    #expect(try c.reading("Pure.prop") == .constant(defined(.pure, "Pure.prop", .meta)))
    #expect(try c.reading("Sum.Inl") == .constant(defined(.zf, "Sum.Inl", .object)))
    #expect(try c.reading("T.claim") == .constant(.declared("T.claim")))
    #expect(throws: DialectGap.leaf("ZF_Base.not_mem")) { try c.reading("ZF_Base.not_mem") }
}

@Test func aDefinitionOfALeafTheDialectListsIsMalformed() throws {
    var c = try testConstants()
    #expect(throws: MalformedExport.definedLeaf("IFOL.conj")) { try c.define("IFOL.conj", by: "IFOL.conj_def") }
    #expect(throws: MalformedExport.definedLeaf("ZF_Base.mem")) { try c.define("ZF_Base.mem", by: "ZF_Base.mem_def") }
}

@Test func aConstantDefinedTwiceOrTwoConstantsByOneAxiomIsMalformed() throws {
    var c = try testConstants()
    #expect(throws: MalformedExport.duplicateDefinition("IFOL.iff")) { try c.define("IFOL.iff", by: "IFOL.iff_again") }
    #expect(throws: MalformedExport.duplicateDefinition("T.f")) { try c.define("T.f", by: "IFOL.iff_def_raw") }
    #expect(c.defined(byAxiom: "IFOL.iff_def_raw") == Defined(.ifol, "IFOL.iff", .object))
}

private func realExport() throws -> Export? {
    let root = "data/zf_export"
    guard FileManager.default.fileExists(atPath: root) else {
        Issue.record("export missing at \(root) — run from the repo root")
        return nil
    }
    return try Export(root: root)
}

@Test func theExportsConstantsReadByTheirTheoriesAndDefinitions() throws {
    guard let e = try realExport() else { return }
    let c = e.constants
    #expect(c["IFOL.eq"] == Constants.Declaration(parameters: ["'a"], scheme: fnT(a, fnT(a, oT)), family: .ifol, foundation: true))
    #expect(try c.instantiate("IFOL.eq", [iT]).irType() == .fn(.i, .fn(.i, .o)))
    #expect(try c.instantiate("ZF_Base.mem", []).irType() == .fn(.i, .fn(.i, .o)))
    #expect(try c.instantiate("Pure.eq", [iT]).irType() == .fn(.i, .fn(.i, .o)))
    #expect(try c.reading("ZF_Base.mem") == .constant(.primitive(.zf(.mem))))
    #expect(try c.reading("IFOL.iff") == .constant(defined(.ifol, "IFOL.iff", .object)))
    #expect(try c.reading("FOL.induct_implies") == .constant(defined(.fol, "FOL.induct_implies", .object)))
    #expect(try c.reading("ZF_Base.Ball") == .constant(defined(.zf, "ZF_Base.Ball", .object)))
    #expect(try c.reading("Language.Const") == .constant(.declared("Language.Const")))
    #expect(try c.reading("Com.loc") == .constant(.declared("Com.loc")))
    #expect(throws: DialectGap.leaf("IFOL.not_equal")) { try c.reading("IFOL.not_equal") }
}

/// FOUNDATION S1: a constant declared over `i`, `o` and `⇒` is at the object level; one whose declared type mentions
/// `prop` or a type variable is at the meta level, whatever its family.
@Test func aDefinedConstantKeepsItsDeclaredLevel() throws {
    let c = try testConstants()
    #expect(try c.reading("ZF_Base.Ball") == .constant(defined(.zf, "ZF_Base.Ball", .object)))
    #expect(try c.reading("ZF_Base.split") == .constant(defined(.zf, "ZF_Base.split", .meta)))
    #expect(try c.reading("IFOL.Not") == .constant(defined(.ifol, "IFOL.Not", .object)))
    #expect(try c.reading("Pure.prop") == .constant(defined(.pure, "Pure.prop", .meta)))
    #expect(c.defined(byAxiom: "ZF_Base.split_def_raw") == Defined(.zf, "ZF_Base.split", .meta))
}
