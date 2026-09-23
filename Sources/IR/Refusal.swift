public enum IRRefusal: Error, Equatable, Sendable {
    case rewroteADerivation(ValueID)
    case erasedADerivation(OpID)
    case opSurvivedLowering(Op, OpID)
    case typeSurvivedLowering(TypeShape, ValueID)
    case arityMismatch(Op, expected: Int, got: Int)
    case unknownValue(ValueID)
    case fixpointDidNotConverge(pass: String, rounds: Int)
}
