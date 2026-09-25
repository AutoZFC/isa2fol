@frozen public enum ReaderRefusal: Error, Equatable, Sendable {
    case typeVariable(String)
    case prop
    case typeConstructor(String)
    case schematicVariable(String)
    case ofclass(String)
    case pureInternal(String)
    case betaRedex
    case quantifierOverFunction
}
