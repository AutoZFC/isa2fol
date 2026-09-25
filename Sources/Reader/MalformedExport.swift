import IR

@frozen public enum MalformedExport: Error, Equatable, Sendable {
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
}
