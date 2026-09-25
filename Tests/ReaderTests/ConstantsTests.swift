import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func load(_ c: inout Constants, _ entities: String...) throws {
    var f = Forest()
    let body = try f.parse(Array(entities.joined().utf8))
    try c.load(body, in: f)
}

private func load(_ c: inout Constants, contentsOf path: String) throws {
    var f = Forest()
    let body = try f.parse(contentsOf: path)
    try c.load(body, in: f)
}

private let a = IsaType.tfree("'a", sort: [])
private let b = IsaType.tfree("'b", sort: [])
private let iT = IsaType.type("ZF_Base.i", [])
private let oT = IsaType.type("IFOL.o", [])
private func fnT(_ x: IsaType, _ y: IsaType) -> IsaType { .type("fun", [x, y]) }

@Test func aConstantLoadsItsParametersInOrderAndItsScheme() throws {
    var c = Constants()
    try load(&c, constEntity("T.k", parameters: ["'b", "'a"], scheme: fn(tfree("'a"), tfree("'b"))))
    #expect(c["T.k"] == Constants.Declaration(parameters: ["'b", "'a"], scheme: fnT(a, b)))
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

private func realConstants(_ theories: String...) throws -> Constants? {
    var c = Constants()
    for t in theories {
        let path = "data/zf_export/\(t)/theory/consts"
        guard FileManager.default.fileExists(atPath: path) else {
            Issue.record("export missing at \(path) — run from the repo root")
            return nil
        }
        try load(&c, contentsOf: path)
    }
    return c
}

@Test func ifolEqAtIIsIToIToO() throws {
    guard let c = try realConstants("IFOL") else { return }
    #expect(c["IFOL.eq"] == Constants.Declaration(parameters: ["'a"], scheme: fnT(a, fnT(a, oT))))
    let T = try c.instantiate("IFOL.eq", [iT])
    #expect(T == fnT(iT, fnT(iT, oT)))
    #expect(try T.irType() == .fn(.i, .fn(.i, .o)))
}

@Test func zfBaseMemIsGround() throws {
    guard let c = try realConstants("IFOL", "ZF.ZF_Base") else { return }
    #expect(c["ZF_Base.mem"] == Constants.Declaration(parameters: [], scheme: fnT(iT, fnT(iT, oT))))
    #expect(try c.instantiate("ZF_Base.mem", []).irType() == .fn(.i, .fn(.i, .o)))
}

@Test func pureEqAtIIsRefusedForItsProp() throws {
    guard let c = try realConstants("Pure") else { return }
    #expect(throws: ReaderRefusal.prop) { try c.instantiate("Pure.eq", [iT]).irType() }
}

@Test func everyExportedConstsFileLoadsIntoOneTable() throws {
    let root = "data/zf_export"
    guard let theories = try? FileManager.default.contentsOfDirectory(atPath: root) else {
        Issue.record("export missing at \(root) — run from the repo root")
        return
    }
    var c = Constants()
    for t in theories where FileManager.default.fileExists(atPath: "\(root)/\(t)/theory/consts") {
        try load(&c, contentsOf: "\(root)/\(t)/theory/consts")
    }
    #expect(c["Pure.eq"] != nil)
    #expect(c["IFOL.eq"] != nil)
    #expect(c["ZF_Base.mem"] != nil)
}
