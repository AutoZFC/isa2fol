import IR

@frozen
public enum MalformedExport: Error, Equatable, Sendable {
    case notANode(tag: String)
    case bodyLength(expected: Int, found: Int)
    case notAString
    case unknownVariant(tag: String)
    case vector(names: [String])
    case atoms([String])
    case notAnInt(String)
    case notAnEntity(tag: String)
    case duplicateConstant(String)
    case undeclaredConstant(String)
    case constantsOutsideTheFamilies(theory: String)
    case definedLeaf(String)
    case duplicateDefinition(String)
    case schemeVariables(constant: String)
    case typeArgumentCount(constant: String, declared: Int, found: Int)
    case constructorArity(String, Int)
    case unboundBound(Int)
    case undeclaredFree(String)
    case unexpectedAbstraction(expected: IRType)
    case typeMismatch(expected: IRType, found: IRType?)
    case applicationArity(String, expected: Int, found: Int)
    case freesHeader(header: [String], occurring: [String])
    case notASerial(String)
    case duplicateSerial(Int)
    case unresolvedCitation(theory: String, serial: Int)
    case tfreesHeader([String])
    case instanceArity(expected: Int, found: Int)
    case undeclaredTypeVariable(String)
    case sortedTypeVariable(String)
    case schematicVariable(String)
    case duplicateClass(String)
    case undeclaredClass(String)
    case classesOutsideTheFamilies(theory: String)
    case undefinedClass(String)
    case duplicateAxiom(String)
    case undeclaredAxiom(String)
    case freeHypothesis
    case hiddenOutsideProof(IRType)
    case unboundHypothesis(Int)
    case unproved(statement: NodeID, conclusion: NodeID?)
    case cyclicClosure(String)
    case notADefinition(String)
}

@frozen
public enum DialectGap: Error, Equatable, Sendable {
    case leaf(String)
    case axiom(String)
}
