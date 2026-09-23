public enum Verdict: Sendable {
    case declared
    case waiting(on: String)          // a constant the Vocabulary lacks
    case refused(String)
}

public struct Entry: Sendable {
    public let predicate: String
    public let arity: Int
    public let source: Source
    public init(predicate: String, arity: Int, source: Source) {
        self.predicate = predicate
        self.arity = arity
        self.source = source
    }
}

/// ⚠ FOUNDATION §3: Isabelle's own Pair stays Kuratowski — "a VALUE inside an
/// assignment, never an assignment". Serving a `.base` entry where a
/// `.translated` one belongs substitutes a different constant under one name.
public enum Source: Sendable {
    case base
    case translated
}

public protocol Vocabulary {
    func entry(_ isabelle: String) -> Entry?
}
