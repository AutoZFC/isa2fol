public enum IRRefusal: Error, Equatable, Sendable {
    case rewroteADerivation(OpID)
    case erasedADerivation(OpID)
    case opSurvivedLowering(Op, OpID)
    case typeSurvivedLowering(TypeShape, OpID)
    case unknownOperand(OpID)
    case fixpointDidNotConverge(pass: String, rounds: Int)
}
