public func legalize(_ root: NodeID, in t: Table) throws {
    var seen = Set<NodeID>()
    var pending = [root]
    while let id = pending.popLast() {
        guard seen.insert(id).inserted else { continue }
        guard Pattern(t[id], in: t).dialects.contains(.fol) else { throw IRRefusal.sourceKindSurvived(id) }
        t[id].forEachHeldChild { pending.append($0) }
    }
}

public func spineLetters(_ root: NodeID, in t: Table) -> Int {
    var count = 0
    var at = root
    while true {
        if case .ifolAll(let T, let body) = t[at] {
            if letterArity(T) != nil { count += 1 }
            at = body
        } else if case .folLetterAll(_, let body) = t[at] {
            count += 1
            at = body
        } else if case .folForall(let body) = t[at] {
            at = body
        } else if case .folImplies(_, let b) = t[at] {
            at = b
        } else {
            return count
        }
    }
}

public func misplacedLetters(_ roots: [NodeID], in t: Table) -> Set<Pattern> {
    var seen = Set<Place>()
    var misplaced = Set<Pattern>()
    var pending = roots.map { Place(id: $0, spine: true) }
    while let at = pending.popLast() {
        guard seen.insert(at).inserted else { continue }
        let n = t[at.id]
        switch n {
        case .ifolAll(let T, let body), .isaAllIntro(let T, let body):
            if letterArity(T) != nil, !at.spine { misplaced.insert(Pattern(n, in: t)) }
            pending.append(Place(id: body, spine: at.spine && letterArity(T) != nil))

        case .folLetterAll(_, let body), .folLetterIntro(_, let body):
            if !at.spine { misplaced.insert(Pattern(n, in: t)) }
            pending.append(Place(id: body, spine: at.spine))

        case .folForall(let body), .folForallIntro(let body):
            pending.append(Place(id: body, spine: at.spine))

        case .folImplies(let a, let b), .folImpliesIntro(let a, let b):
            pending += [Place(id: a, spine: false), Place(id: b, spine: at.spine)]

        case .use(_, _, let root):
            pending.append(Place(id: root, spine: true))

        case .folSchemaInst(let p, let a):
            if !citesAtItsHead(p, t) { misplaced.insert(Pattern(n, in: t)) }
            pending += [Place(id: p, spine: false), Place(id: a, spine: false)]

        case .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass,
             .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folAnd, .folOr,
             .folIff,
             .folBottom, .folImpliesElim, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound,
             .folPred, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim,
             .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallElim, .folExistsIntro,
             .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd, .folLetter, .folLetterAbs, .value,
             .valueFact, .valueElim:
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
    if case .folSchemaInst(let q, _) = t[p] { return citesAtItsHead(q, t) }
    if case .folForallElim(let q, _) = t[p] { return citesAtItsHead(q, t) }
    if case .folImpliesElim(let q, _) = t[p] { return citesAtItsHead(q, t) }
    return false
}
