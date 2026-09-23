/// A VARIABLE. There is no other term: S1 gives the target no function symbols,
/// which is what makes `iota` unrepresentable.
public struct Term: Hashable, Sendable {
    public let name: String
    public init(_ name: String) { self.name = name }
}
