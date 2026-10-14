import IR

public struct Expand: Pass {
    public let name = "expand"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch p {
        case let .isaConst(.defined(f), T, _):
            return isLogic(f) && !mentionsTypeVariable(T) ? .unbuilt : nil
        case let .use(.isaDefinition(f), types, _):
            return isLogic(f) && !types.contains(where: mentionsTypeVariable) ? .unbuilt : nil
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
             .isaAllElim, .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .use,
             .hyp, .isaGuard, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR,
             .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
             .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
             .folClassicalAbsurd:
            return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] { roots }
}
