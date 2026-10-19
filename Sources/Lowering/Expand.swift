import IR

@frozen
public enum ExpandError: Error, Equatable {
    case noDefinition(Node)
    case noReading(Node)
}

public struct Expand: Pass {
    public init() { }

    public let name = "expand"

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .constant?, .citation?, .membership?, .equation?: .rule
        case nil: nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        let rule = try Unfold(definitions, in: &t)
        return try transform(roots, rule, in: &t)
    }
}

private enum Piece {
    case constant
    case citation
    case membership
    case equation
}

func onlyReflexive(_ T: IRType) -> Bool {
    !mentionsTypeVariable(T) && T.domains.contains(where: takesAFunctionOrProposition)
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case .isaConst(.defined(let f, let level), let T, _):
        unfolds(f, level) && !mentionsTypeVariable(T) ? .constant : nil
    case .isaDefinition(let f, let level, let types, _):
        unfolds(f, level) && !types.contains(where: mentionsTypeVariable) ? .citation : nil
    case .isaOfClass(let T):
        mentionsTypeVariable(T) ? nil : .membership
    case .isaCombination(let T, _, _), .isaSymmetric(let T, _), .isaTransitive(let T, _, _):
        onlyReflexive(T) ? .equation : nil
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaAllIntro,
         .isaAllElim, .isaReflexive, .isaAbstract, .isaClassical,
         .isaIffReflection, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd,
         .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .use,
         .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro,
         .folAndElimL, .folAndElimR,
         .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
         .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim,
         .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
        nil
    }
}

private struct Instance: Hashable {
    let defines: Definiendum
    let types: [IRType]
}

private struct Typed: Hashable {
    let constant: Defined
    let type: IRType
}

private struct Unfold: Rule {
    init(_ given: [Definition], in t: inout Table) throws {
        for d in given {
            if case .constant(let c) = d.defines { typed[Typed(constant: c, type: d.type)] = Instance(
                defines: d.defines,
                types: d.axiomTypes,
            ) }
        }
        var unfolded = given
        var changed = true
        while changed {
            for d in unfolded { definitions[Instance(defines: d.defines, types: d.axiomTypes)] = d }
            changed = false
            for k in unfolded.indices {
                let definiens = try transform(unfolded[k].definiens, self, in: &t)
                if definiens != unfolded[k].definiens { (unfolded[k].definiens, changed) = (definiens, true) }
            }
        }
    }

    var start: Anywhere {
        Anywhere()
    }

    func enter(_ c: Anywhere, _: Node, _: Binds, in _: Table) -> Anywhere {
        c
    }

    func after(_ n: Node, was _: NodeID, context _: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case .constant?:
            guard
                case .isaConst(.defined(let c), let T, let args) = n, let k = typed[Typed(constant: c, type: T)],
                let d = definitions[k]
            else {
                throw ExpandError.noDefinition(n)
            }
            return try beta(d.definiens, args, in: &t)

        case .citation?:
            guard
                case .isaDefinition(_, let x, let types, _, let args) = n, let d = definitions[Instance(
                    defines: x,
                    types: types,
                )]
            else {
                throw ExpandError.noDefinition(n)
            }
            return try reflexivity(d, at: args, in: &t)

        case .membership?:
            guard
                case .isaOfClass(let T, let c) = n,
                let d = definitions[Instance(defines: .ofClass(c), types: [T])]
            else {
                throw ExpandError.noDefinition(n)
            }
            return d.definiens

        case .equation?:
            let rebuilt = try t.intern(n)
            guard
                let c = t.conclusion(of: rebuilt), let (_, a, b) = t.sides(ofEquation: c),
                a == b
            else { throw ExpandError.noReading(n) }
            return try t.intern(.isaReflexive(a))

        case nil:
            return nil
        }
    }

    private var definitions = [Instance: Definition]()
    private var typed = [Typed: Instance]()

}

private func reflexivity(_ d: Definition, at args: [NodeID], in t: inout Table) throws -> NodeID {
    let left = Array(d.type.domains.prefix(d.parameters).dropFirst(args.count))
    let given = try args.map { try shift($0, by: left.count, in: &t) }
    let variables = try left.indices.map { k in try t.intern(.isaBound(left.count - 1 - k, left[k])) }
    var proof = try t.intern(.isaReflexive(try beta(d.definiens, given + variables, in: &t)))
    for T in left.reversed() { proof = try t.intern(.isaAllIntro(T, body: proof)) }
    return proof
}
