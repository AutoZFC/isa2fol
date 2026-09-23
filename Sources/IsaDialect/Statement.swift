/// Ground-ness is a phantom type, not a runtime check: `convert` takes a
/// `Statement<Ground>` and therefore CANNOT be handed a polymorphic one.
public enum Poly: Sendable {}
public enum Ground: Sendable {}

public struct Statement<Stage>: Sendable {
    public let prop: Prop
    public let env: [String: Sort]
    init(prop: Prop, env: [String: Sort]) {
        self.prop = prop
        self.env = env
    }
}

public enum Refusal: Error, Equatable, Sendable {
    case notGround(String)
    case unboundIndex(Int, depth: Int)
    case unknownTag(String)
    case pureInternal(String)
    case metaConjunction
    case notAProp(String)
}
