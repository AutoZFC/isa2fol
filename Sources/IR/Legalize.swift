public func legalize(_ root: NodeID, in t: Table) throws {
    var seen: Set<NodeID> = [], pending = [root]
    while let id = pending.popLast() {
        guard seen.insert(id).inserted else { continue }
        guard Pattern(t[id], in: t).dialects.contains(.fol) else { throw IRRefusal.sourceKindSurvived(id) }
        t[id].forEachChild { c, _ in pending.append(c) }
    }
}

public func misplacedLetters(_ roots: [NodeID], in t: Table) -> Set<Pattern> {
    var seen: Set<Place> = [], misplaced: Set<Pattern> = [], pending = roots.map { Place(id: $0, spine: true) }
    while let at = pending.popLast() {
        guard seen.insert(at).inserted else { continue }
        let n = t[at.id]
        switch n {
        case let .ifolAll(.o, body), let .isaAllIntro(.o, body):
            if !at.spine { misplaced.insert(Pattern(n, in: t)) }
            pending.append(Place(id: body, spine: at.spine))
        case let .folForall(body), let .folForallIntro(body):
            pending.append(Place(id: body, spine: at.spine))
        case let .folImplies(a, b), let .folImpliesIntro(a, b):
            pending += [Place(id: a, spine: false), Place(id: b, spine: at.spine)]
        case let .use(_, _, root):
            pending.append(Place(id: root, spine: true))
        case let .folSchemaInst(p, a):
            if !citesAtItsHead(p, t) { misplaced.insert(Pattern(n, in: t)) }
            pending += [Place(id: p, spine: false), Place(id: a, spine: false)]
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
             .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folAnd, .folOr, .folIff, .folBottom, .folImpliesElim, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
             .folPred, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
             .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallElim, .folExistsIntro,
             .folExistsElim, .folBottomElim, .folClassicalAbsurd:
            n.forEachChild { c, _ in pending.append(Place(id: c, spine: false)) }
        }
    }
    return misplaced
}

private struct Place: Hashable {
    let id: NodeID
    let spine: Bool
}

private func citesAtItsHead(_ p: NodeID, _ t: Table) -> Bool {
    if case .use = t[p] { return true }
    if case let .folSchemaInst(q, _) = t[p] { return citesAtItsHead(q, t) }
    if case let .folForallElim(q, _) = t[p] { return citesAtItsHead(q, t) }
    if case let .folImpliesElim(q, _) = t[p] { return citesAtItsHead(q, t) }
    return false
}
