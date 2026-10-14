import IR

public struct Reify: Pass {
    public let name = "reify"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch p {
        case let .isaConst(kind, T, _):
            switch kind {
            case .primitive(.zf), .primitive(.ifol), .defined(.zf), .declared:
                return mentionsTypeVariable(T) ? nil : .unbuilt
            case .primitive(.pure), .defined(.pure), .defined(.ifol), .defined(.fol):
                return nil
            }
        case let .isaVarApp(head: T, _):
            return mentionsTypeVariable(T) ? nil : .unbuilt
        case let .isaAbs(T, body: U):
            return mentionsTypeVariable(.fn(T, U)) ? nil : .unbuilt
        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaOfClass, .isaAllIntro, .isaAllElim, .folImplies, .folAnd,
             .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .folNot, .folBound, .folPred,
             .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
             .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim,
             .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd:
            return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] { roots }
}
