/// A VARIABLE. There is no other term.
///
/// Not an enum, and not an oversight: S1 says the target signature has no
/// function symbols, so a description former, an application or a literal has
/// nowhere to live. This is the type that makes `iota` unrepresentable.
public struct Term: Hashable, Sendable {
    public let name: String
    public init(_ name: String) { self.name = name }
}
