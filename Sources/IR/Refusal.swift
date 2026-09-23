public enum IRRefusal: Error, Equatable, Sendable {
    case opSurvivedLowering(Op, OpID)
    case typeSurvivedLowering(TypeShape, OpID)
    case unknownOperand(OpID)
    case binderSortNotGuardable(IRType)
    case regionHasNoResult(RegionID)
    case fixpointDidNotConverge(pass: String, rounds: Int)
}
