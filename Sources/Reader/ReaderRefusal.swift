@frozen public enum ReaderRefusal: Error, Equatable, Sendable {
    case typeVariable(String)
    case prop
    case typeConstructor(String)
}
