import IR

@frozen public enum ExpandError: Error, Equatable {
    case noDefinition(Node)
}

public struct Expand: Pass {
    public let name = "expand"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .constant?, .citation?: return .rule
        case nil: return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        let rule = try Unfold(definitions, in: &t)
        return try transform(roots, rule, in: &t)
    }
}

private enum Piece {
    case constant, citation
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .isaConst(.defined(f, level), T, _):
        return unfolds(f, level) && !mentionsTypeVariable(T) ? .constant : nil
    case let .use(.isaDefinition(f, level), types, _):
        return unfolds(f, level) && !types.contains(where: mentionsTypeVariable) ? .citation : nil
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
         .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .folImplies, .folAnd,
         .folOr, .folIff, .folBottom, .folImpliesIntro, .folImpliesElim, .use,
         .hyp, .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR,
         .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
         .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
         .folClassicalAbsurd, .folSchemaInst:
        return nil
    }
}

private struct Instance: Hashable {
    let constant: Defined
    let type: IRType
}

private struct Citation: Hashable {
    let constant: Defined
    let types: [IRType]
}

private struct Unfold: Rule {
    private var definitions: [Instance: Definition] = [:]
    private var citations: [Citation: Instance] = [:]

    init(_ given: [Definition], in t: inout Table) throws {
        for d in given {
            citations[Citation(constant: d.constant, types: d.axiomTypes)] = Instance(constant: d.constant, type: d.type)
        }
        var unfolded = given, changed = true
        while changed {
            for d in unfolded { definitions[Instance(constant: d.constant, type: d.type)] = d }
            changed = false
            for k in unfolded.indices {
                let definiens = try transform(unfolded[k].definiens, self, in: &t)
                if definiens != unfolded[k].definiens { (unfolded[k].definiens, changed) = (definiens, true) }
            }
        }
    }

    var start: Anywhere { Anywhere() }
    func enter(_ c: Anywhere, _ binder: Node, _ binds: Binds, in t: Table) -> Anywhere { c }

    func after(_ n: Node, was id: NodeID, context: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case .constant?:
            guard case let .isaConst(.defined(c), T, args) = n, let d = definitions[Instance(constant: c, type: T)] else {
                throw ExpandError.noDefinition(n)
            }
            return try beta(d.definiens, args, in: &t)
        case .citation?:
            guard case let .use(.isaDefinition(_, c), types, _) = n, let k = citations[Citation(constant: c, types: types)],
                  let d = definitions[k] else {
                throw ExpandError.noDefinition(n)
            }
            return try reflexivity(d, in: &t)
        case nil:
            return nil
        }
    }
}

private func reflexivity(_ d: Definition, in t: inout Table) throws -> NodeID {
    let parameters = Array(d.type.domains.prefix(d.parameters))
    let variables = try parameters.indices.map { k in try t.intern(.isaBound(parameters.count - 1 - k, parameters[k])) }
    var proof = try t.intern(.isaReflexive(try beta(d.definiens, variables, in: &t)))
    for T in parameters.reversed() { proof = try t.intern(.isaAllIntro(T, body: proof)) }
    return proof
}
