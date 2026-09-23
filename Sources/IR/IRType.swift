public enum TypeShape: Hashable, Sendable {
    case i, o, prop, fn
}

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

    public var shape: TypeShape {
        switch self {
        case .i: return .i
        case .o: return .o
        case .prop: return .prop
        case .fn: return .fn
        }
    }

    public var shapes: Set<TypeShape> {
        switch self {
        case .i, .o, .prop:
            return Set<TypeShape>([shape])
        case let .fn(a, b):
            return Set<TypeShape>([.fn]).union(a.shapes).union(b.shapes)
        }
    }
}
