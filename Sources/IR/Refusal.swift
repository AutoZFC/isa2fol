public enum IRRefusal: Error, Equatable, Sendable {
    case opSurvivedLowering(Op, OpID)
    case typeSurvivedLowering(IRType, OpID)
    case unknownOperand(OpID)
    case binderSortNotGuardable(IRType)
    case regionHasNoResult(RegionID)
}
