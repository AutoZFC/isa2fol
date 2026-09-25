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
}
