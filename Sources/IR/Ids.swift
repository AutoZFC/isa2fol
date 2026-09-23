public struct ValueID: Hashable, Sendable, CustomStringConvertible {
    public let raw: Int
    public var description: String { "%\(raw)" }
}

public struct OpID: Hashable, Sendable, CustomStringConvertible {
    public let raw: Int
    public var description: String { "op\(raw)" }
}

public struct RegionID: Hashable, Sendable, CustomStringConvertible {
    public let raw: Int
    public var description: String { "^\(raw)" }
}
