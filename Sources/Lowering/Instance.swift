import IR

@frozen
public enum InstanceError: Error, Equatable, Sendable {
    case notAnInstance(NodeID)
    case notAnEquivalence(NodeID)
}

struct Unit {
    enum Kind {
        case term
        case slot
        case applied
    }

    let path: [Int]
    let kind: Kind

}

func units(_ n: NodeID, _ x: Int, _ path: [Int], in t: Table) -> [Unit] {
    switch t[n] {
    case .isaBound(let k, _):
        return k == x ? [Unit(path: path, kind: .term)] : []

    case .isaConst(_, _, let args):
        return args.indices.flatMap { arguments(args[$0], x, path + [$0], in: t) }

    case .isaVarApp(let head, let args):
        let inner = args.indices.flatMap { arguments(args[$0], x, path + [$0], in: t) }
        guard case .isaBound(x, _) = t[head] else { return inner }
        return inner + [Unit(path: path, kind: .applied)]

    case .isaAbs:
        return freeVariables(n, in: t).contains { $0.index == x } ? [Unit(path: path, kind: .slot)] : []

    case .ifolAll, .ifolEx, .isaFree, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive, .isaSymmetric,
         .isaTransitive,
         .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro,
         .isaHidden,
         .isaPropBound, .folImplies, .folAnd, .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim,
         .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists,
         .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim,
         .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
         .folCut,
         .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs, .value,
         .valueFact, .valueElim:
        return []
    }
}

private func arguments(_ n: NodeID, _ x: Int, _ path: [Int], in t: Table) -> [Unit] {
    guard t.type(of: n) == .o else { return units(n, x, path, in: t) }
    return freeVariables(n, in: t).contains { $0.index == x } ? [Unit(path: path, kind: .slot)] : []
}

func argument(at path: [Int], in n: NodeID, _ t: Table) throws -> NodeID {
    var x = n
    for k in path {
        switch t[x] {
        case .isaConst(_, _, let args), .isaVarApp(_, let args): x = args[k]
        default: throw ReifyError.notATerm(x)
        }
    }
    return x
}

func replacing(_ n: NodeID, at path: ArraySlice<Int>, with x: NodeID, in t: inout Table) throws -> NodeID {
    guard let k = path.first else { return x }
    switch t[n] {
    case .isaConst(let c, let T, let args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaConst(c, T, args: replaced))

    case .isaVarApp(let f, let args):
        var replaced = args
        replaced[k] = try replacing(args[k], at: path.dropFirst(), with: x, in: &t)
        return try t.intern(.isaVarApp(head: f, args: replaced))

    default:
        throw ReifyError.notATerm(n)
    }
}

func chained(_ p: NodeID, _ q: NodeID, _ base: Base, _ t: inout Table) throws -> NodeID {
    guard
        case .folIff(let a, let b)? = t.conclusion(of: p).map({ t[$0] }),
        case .folIff(_, let c)? = t.conclusion(of: q).map({ t[$0] })
    else { throw InstanceError.notAnEquivalence(p) }
    return try base.applied(.iffTrans, [a, b, c], [p, q], in: &t)
}
