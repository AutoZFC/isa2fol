import IR

@frozen
public enum DeclarationKind: Equatable, Sendable {
    case claim
    case definition(predicate: String)
    case schema(letters: [String])
}

public struct Declaration: Sendable {
    public init(kind: DeclarationKind, name: String, root: NodeID) {
        self.kind = kind
        self.name = name
        self.root = root
    }

    public let kind: DeclarationKind
    public let name: String
    public let root: NodeID

}
