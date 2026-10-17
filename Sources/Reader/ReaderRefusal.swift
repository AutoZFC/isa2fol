@frozen
public enum ReaderRefusal: Error, Hashable, Sendable {
    case typeConstructor(String)
    case ofclass(String)
    case betaRedex
    case nameSegment(String)
    case omittedProof
    case oracle(String)
    case letterLeft
}
