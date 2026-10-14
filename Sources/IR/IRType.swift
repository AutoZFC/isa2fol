@frozen public enum IRType: Hashable, Sendable, CustomStringConvertible {
    case i
    case o
    indirect case fn(IRType, IRType)
    case variable(String)

    public var description: String {
        switch self {
        case .i: return "i"
        case .o: return "o"
        case let .fn(a, b): return "(\(a) => \(b))"
        case let .variable(name): return name
        }
    }

    public var domains: [IRType] {
        guard case let .fn(T, rest) = self else { return [] }
        return [T] + rest.domains
    }
}
