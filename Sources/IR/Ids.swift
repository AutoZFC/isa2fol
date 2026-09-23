/// ⚠ ONE VALUE PER OP, SO A VALUE *IS* ITS PRODUCER. There is no separate value
/// table and no `results` list; `Op.type` computes what an op yields.
public struct OpID: Hashable, Sendable, CustomStringConvertible {
    public let raw: Int
    public var description: String { "%\(raw)" }
}

public struct RegionID: Hashable, Sendable, CustomStringConvertible {
    public let raw: Int
    public var description: String { "^\(raw)" }
}
