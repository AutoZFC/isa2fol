public enum TypeShape: Hashable, Sendable {
    case obj, prop, meta, fn
}

public enum IRType: Hashable, Sendable {
    case obj
    case prop
    case meta
    indirect case fn(IRType, IRType)

    public var shape: TypeShape {
        switch self {
        case .obj: return .obj
        case .prop: return .prop
        case .meta: return .meta
        case .fn: return .fn
        }
    }

    public var shapes: Set<TypeShape> {
        switch self {
        case .obj, .prop, .meta:
            return Set<TypeShape>([shape])
        case let .fn(a, b):
            return Set<TypeShape>([.fn]).union(a.shapes).union(b.shapes)
        }
    }
}
