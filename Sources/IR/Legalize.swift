public func legalize(_ root: NodeID, in t: Table) throws {
    var pending = [root]
    while let id = pending.popLast() {
        switch t[id] {
        case .folBound, .folPred, .folAnd, .folOr, .folImplies, .folIff, .folNot,
             .folBottom, .folForall, .folExists, .use, .hyp, .folAndIntro, .folAndElimL,
             .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folImpliesIntro,
             .folImpliesElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
             .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
             .folExistsElim, .folBottomElim, .folClassicalAbsurd:
            break
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs,
             .isaAllIntro, .isaAllElim:
            throw IRRefusal.sourceKindSurvived(id)
        }
        t[id].forEachChild { c, _ in pending.append(c) }
    }
}
