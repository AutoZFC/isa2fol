@frozen public enum ReaderRefusal: Error, Equatable, Sendable {
    case typeVariable(String)
    case typeConstructor(String)
    case schematicVariable(String)
    case ofclass(String)
    case betaRedex
    case nameSegment(String)
}
