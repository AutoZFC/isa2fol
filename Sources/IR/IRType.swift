public enum IRType: Hashable, Sendable, CustomStringConvertible {
    case i
    case o
    case prop
    indirect case fn(IRType, IRType)

    public var description: String {
        switch self {
        case .i: return "i"
        case .o: return "o"
        case .prop: return "prop"
        case let .fn(a, b): return "(\(a) => \(b))"
        }
    }
}
