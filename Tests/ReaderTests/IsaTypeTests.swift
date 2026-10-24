import IR
import Testing
@testable import Reader

@Test
func aTypeConstructorDecodesWithItsArguments() throws {
    let T = try decodeType(fn(i, o))
    #expect(T == .type("fun", [.type("ZF_Base.i", []), .type("IFOL.o", [])]))
}

@Test
func aFreeTypeVariableKeepsItsSort() throws {
    #expect(try decodeType(tfree("'a", "HOL.type", "Foo.bar")) == .tfree("'a", sort: ["HOL.type", "Foo.bar"]))
}

@Test
func aSchematicTypeVariableWithOneAtomHasIndexZero() throws {
    #expect(try decodeType(tvar(["'a"])) == .tvar("'a", index: 0, sort: []))
}

@Test
func aSchematicTypeVariableKeepsItsIndex() throws {
    #expect(try decodeType(tvar(["'a", "3"], "Foo.bar")) == .tvar("'a", index: 3, sort: ["Foo.bar"]))
}

@Test
func anUnknownVariantTagIsMalformed() {
    #expect(throws: MalformedExport.unknownVariant(tag: "3")) { try decodeType(tagged(3, ["x"], [])) }
}

@Test
func aTypeBodyOfTwoTreesIsMalformed() {
    #expect(throws: MalformedExport.bodyLength(expected: 1, found: 2)) { try decodeType(i + o) }
}

@Test
func anArgumentOutsideANodeIsMalformed() {
    #expect(throws: MalformedExport.notANode(tag: "0")) { try decodeType(tagged(0, ["fun"], [i, o])) }
}

@Test
func aSortClassThatIsNotTextIsMalformed() {
    #expect(throws: MalformedExport.notAString) { try decodeType(tfree("'a", i)) }
}

@Test
func attributesThatAreNotAVectorAreMalformed() {
    let skipped = element("0", [("1", "ZF_Base.i")], [])
    #expect(throws: MalformedExport.vector(names: ["1"])) { try decodeType(skipped) }
}

@Test
func aConstructorWithTwoNamesIsMalformed() {
    #expect(throws: MalformedExport.atoms(["ZF_Base.i", "x"])) { try decodeType(tagged(0, ["ZF_Base.i", "x"], [])) }
}

@Test
func aSchematicIndexThatIsNotAnIntegerIsMalformed() {
    #expect(throws: MalformedExport.notAnInt("x")) { try decodeType(tvar(["'a", "x"])) }
}

@Test
func iOAndFunConvertToIRType() throws {
    #expect(try decodeType(fn(i, fn(i, o))).irType() == .fn(.i, .fn(.i, .o)))
}

@Test
func aFreeTypeVariableConvertsToATypeVariable() throws {
    #expect(try IsaType.tfree("'a", sort: []).irType() == .variable("'a"))
}

/// `unconstrainT` turns every sort into an `OFCLASS` premise: the export writes none, and one would be lost.
@Test
func aSortedTypeVariableIsMalformed() {
    #expect(throws: MalformedExport.sortedTypeVariable("'a")) { try IsaType.tfree("'a", sort: ["IFOL.term"]).irType() }
}

@Test
func aSchematicTypeVariableIsMalformed() {
    #expect(throws: MalformedExport.schematicVariable("'b")) { try IsaType.tvar("'b", index: 1, sort: []).irType() }
}

@Test
func aTypeVariableInsideAFunctionTypeConverts() throws {
    let T = IsaType.type("fun", [.type("ZF_Base.i", []), .type("fun", [.tfree("'a", sort: []), .type("IFOL.o", [])])])
    #expect(try T.irType() == .fn(.i, .fn(.variable("'a"), .o)))
}

/// `standard_hidden_types` writes every type variable only a proof uses as `dummy`: the export no
/// longer tells them apart, so it converts to ONE variable, which each file's instance reads at `i` (DESIGN
/// "ZF-Constructible's reflection", 4).
@Test
func theHiddenProofTypeConvertsToOneVariable() throws {
    #expect(try IsaType.type("fun", [.type("dummy", []), .type("IFOL.o", [])]).irType() == .fn(.variable("dummy"), .o))
}

@Test
func propConvertsToO() throws {
    #expect(try IsaType.type("fun", [.type("prop", []), .type("prop", [])]).irType() == .fn(.o, .o))
}

@Test
func anUnsupportedTypeConstructorIsRefusedByName() {
    #expect(throws: ReaderRefusal.typeConstructor("Pure.itself")) {
        try IsaType.type("Pure.itself", [.type("ZF_Base.i", [])]).irType()
    }
}

@Test
func aKnownConstructorWithTheWrongArityIsMalformedNotRefused() {
    #expect(throws: MalformedExport.constructorArity("fun", 1)) {
        try IsaType.type("fun", [.type("ZF_Base.i", [])]).irType()
    }
}
