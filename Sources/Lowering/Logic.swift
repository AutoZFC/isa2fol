import IR

public struct Logic: Pass {
    public let name = "logic"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch p {
        case let .use(.axiom(a), types, _):
            return isLogic(a.family) && !types.contains(where: mentionsTypeVariable) ? .unbuilt : nil
        case let .isaConst(.primitive(.pure(.eq)), T, _):
            return mentionsTypeVariable(T) ? nil : .unbuilt
        case let .ifolAll(T, _), let .ifolEx(T, _), let .isaAllIntro(T, _), let .isaAllElim(_, T):
            return isObject(T) || mentionsTypeVariable(T) ? nil : .unbuilt
        case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .folImplies, .folAnd, .folOr, .folIff,
             .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .folNot, .folBound, .folPred, .folForall,
             .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
             .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
             .folExistsElim, .folBottomElim, .folClassicalAbsurd:
            return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] { roots }
}
