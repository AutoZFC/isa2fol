import IR
import Testing
@testable import Reader

@Test func aTypeConstructorDecodesWithItsArguments() throws {
    let T = try decodeType(fn(i, o))
    #expect(T == .type("fun", [.type("ZF_Base.i", []), .type("IFOL.o", [])]))
}

@Test func aFreeTypeVariableKeepsItsSort() throws {
    #expect(try decodeType(tfree("'a", "HOL.type", "Foo.bar")) == .tfree("'a", sort: ["HOL.type", "Foo.bar"]))
}

@Test func aSchematicTypeVariableWithOneAtomHasIndexZero() throws {
    #expect(try decodeType(tvar(["'a"])) == .tvar("'a", index: 0, sort: []))
}

@Test func aSchematicTypeVariableKeepsItsIndex() throws {
    #expect(try decodeType(tvar(["'a", "3"], "Foo.bar")) == .tvar("'a", index: 3, sort: ["Foo.bar"]))
}

@Test func anUnknownVariantTagIsMalformed() {
    #expect(throws: MalformedExport.unknownVariant(tag: "3")) { try decodeType(tagged(3, ["x"], [])) }
}

@Test func aTypeBodyOfTwoTreesIsMalformed() {
    #expect(throws: MalformedExport.bodyLength(expected: 1, found: 2)) { try decodeType(i + o) }
}

@Test func anArgumentOutsideANodeIsMalformed() {
    #expect(throws: MalformedExport.notANode(tag: "0")) { try decodeType(tagged(0, ["fun"], [i, o])) }
}

@Test func aSortClassThatIsNotTextIsMalformed() {
    #expect(throws: MalformedExport.notAString) { try decodeType(tfree("'a", i)) }
}

@Test func attributesThatAreNotAVectorAreMalformed() {
    let skipped = element("0", [("1", "ZF_Base.i")], [])
    #expect(throws: MalformedExport.vector(names: ["1"])) { try decodeType(skipped) }
}

@Test func aConstructorWithTwoNamesIsMalformed() {
    #expect(throws: MalformedExport.atoms(["ZF_Base.i", "x"])) { try decodeType(tagged(0, ["ZF_Base.i", "x"], [])) }
}

@Test func aSchematicIndexThatIsNotAnIntegerIsMalformed() {
    #expect(throws: MalformedExport.notAnInt("x")) { try decodeType(tvar(["'a", "x"])) }
}

@Test func iOAndFunConvertToIRType() throws {
    #expect(try decodeType(fn(i, fn(i, o))).irType() == .fn(.i, .fn(.i, .o)))
}

@Test func aFreeTypeVariableIsRefusedByName() {
    #expect(throws: ReaderRefusal.typeVariable("'a")) { try IsaType.tfree("'a", sort: []).irType() }
}

@Test func aSchematicTypeVariableIsRefusedByName() {
    #expect(throws: ReaderRefusal.typeVariable("'b")) { try IsaType.tvar("'b", index: 1, sort: []).irType() }
}

@Test func aTypeVariableAnywhereInAFunctionTypeRefusesTheWholeType() {
    let T = IsaType.type("fun", [.type("ZF_Base.i", []), .type("fun", [.tfree("'a", sort: []), .type("IFOL.o", [])])])
    #expect(throws: ReaderRefusal.typeVariable("'a")) { try T.irType() }
}

@Test func propConvertsToO() throws {
    #expect(try IsaType.type("fun", [.type("prop", []), .type("prop", [])]).irType() == .fn(.o, .o))
}

@Test func anUnsupportedTypeConstructorIsRefusedByName() {
    #expect(throws: ReaderRefusal.typeConstructor("Pure.itself")) {
        try IsaType.type("Pure.itself", [.type("ZF_Base.i", [])]).irType()
    }
}

@Test func aKnownConstructorWithTheWrongArityIsMalformedNotRefused() {
    #expect(throws: MalformedExport.constructorArity("fun", 1)) {
        try IsaType.type("fun", [.type("ZF_Base.i", [])]).irType()
    }
}
