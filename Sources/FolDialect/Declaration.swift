import IR

@frozen public enum DeclarationKind: Equatable, Sendable {
    case claim
    case definition(predicate: String)
}

public struct Declaration: Sendable {
    public let kind: DeclarationKind
    public let name: String
    public let root: NodeID

    public init(kind: DeclarationKind, name: String, root: NodeID) {
        self.kind = kind
        self.name = name
        self.root = root
    }
}
