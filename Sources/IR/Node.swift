public struct NodeID: Hashable, Sendable, CustomStringConvertible {
    public var description: String {
        "%\(raw)"
    }

    let raw: UInt32
}

@frozen
public enum Namespace: Hashable, Sendable {
    case term
    case hyp
}

public struct Binds: Hashable, Sendable {
    public static let none = Binds(terms: 0, hyps: 0)
    public static let term = Binds(terms: 1, hyps: 0)
    public static let hyp = Binds(terms: 0, hyps: 1)
    public static let termAndHyp = Binds(terms: 1, hyps: 1)

    public let terms: Int
    public let hyps: Int
}

@frozen
public enum Free: Hashable, Sendable {
    case named(String)
    case hidden
}

@frozen
public enum Predicate: Hashable, Sendable {
    case base(String)
    case constant(Constant)

    public var name: String {
        switch self {
        case .base(let name): name
        case .constant(let c): c.name
        }
    }
}

@frozen
public enum Node: Hashable, Sendable {
    // THE READER'S OUTPUT is the next two groups and nothing else (DESIGN §4.3b).
    // Isa only, but at `o` a binder, its intro and its variable are fol-zfc's schema letter — a free the statement is
    // closed over; Pure's `⋀` over a proposition, written in a formula or a proof, is `isaProp*`: lowering replaces the
    // rest.
    case ifolAll(IRType, body: NodeID)
    case ifolEx(IRType, body: NodeID)
    case isaConst(Constant, IRType, args: [NodeID])
    case isaFree(Free, IRType)
    case isaBound(Int, IRType)
    case isaVarApp(head: NodeID, args: [NodeID])
    case isaAbs(IRType, body: NodeID)
    case isaOfClass(IRType, TypeClass)
    case isaAllIntro(IRType, body: NodeID)
    case isaAllElim(NodeID, NodeID)
    case isaReflexive(NodeID)
    case isaSymmetric(IRType, NodeID)
    case isaTransitive(IRType, NodeID, NodeID)
    case isaCombination(IRType, NodeID, NodeID)
    case isaAbstract(IRType, NodeID)
    case isaClassical(NodeID, NodeID)
    case isaIffReflection(NodeID, NodeID, NodeID)
    case isaDefinition(String, of: Definiendum, [IRType], NodeID, args: [NodeID])
    case isaPropAll(body: NodeID)
    case isaPropIntro(body: NodeID)
    case isaPropBound(Int)

    // Both dialects: a construct FOL covers, read as the fol-zfc node itself.
    case folImplies(NodeID, NodeID)
    case folAnd(NodeID, NodeID)
    case folOr(NodeID, NodeID)
    case folIff(NodeID, NodeID)
    case folBottom
    case folImpliesIntro(NodeID, body: NodeID)
    case folImpliesElim(NodeID, NodeID)
    case use(Cited, [IRType], NodeID)
    case hyp(Int, NodeID)
    case folIffIntro(NodeID, NodeID)
    case folIffElimL(NodeID, NodeID)
    case folAndIntro(NodeID, NodeID)
    case folAndElimL(NodeID)
    case folAndElimR(NodeID)
    case folOrIntroL(NodeID, NodeID)
    case folOrIntroR(NodeID, NodeID)
    case folOrElim(NodeID, NodeID, NodeID)
    case folBottomElim(NodeID, NodeID)

    // Isa only, lowering's: a proof before fol cites a variable's guard, which fol writes and resolves; and `∃` at an
    // isa
    // binder, which fol guards.
    case isaGuard(NodeID, NodeID)
    case isaExIntro(NodeID, NodeID)
    case isaExElim(IRType, NodeID, body: NodeID)

    // Fol-zfc only: lowering produces these; the reader never does.
    case folNot(NodeID)
    case folBound(Int)
    case folPred(Predicate, args: [NodeID])
    case folForall(body: NodeID)
    case folExists(body: NodeID)
    case folNotIntro(NodeID, body: NodeID)
    case folNotElim(NodeID, NodeID)
    case folIffElimR(NodeID, NodeID)
    case folForallIntro(body: NodeID)
    case folForallElim(NodeID, NodeID)
    case folExistsIntro(NodeID, NodeID)
    case folExistsElim(NodeID, body: NodeID)
    case folClassicalAbsurd(NodeID, body: NodeID)
    case folSchemaInst(NodeID, NodeID)
    // A base schema's letter with arguments: its binder, its application, its λ instance. Isa's binder at a class type
    // is a class (FOUNDATION S4), never a letter.
    case folLetterAll(Int, body: NodeID)
    case folLetter(head: NodeID, args: [NodeID])
    case folLetterAbs(body: NodeID)

    public var boundVariable: (namespace: Namespace, index: Int, reindexed: (Int) -> Node)? {
        switch self {
        case .isaBound(let k, let T): (.term, k, { .isaBound($0, T) })
        case .hyp(let k, let a): (.hyp, k, { .hyp($0, a) })
        case .folBound(let k): (.term, k, { .folBound($0) })
        case .isaPropBound(let k): (.term, k, { .isaPropBound($0) })
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
             .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .folImplies, .folAnd, .folOr, .folIff, .folNot, .folBottom,
             .folImpliesIntro, .folImpliesElim, .use, .isaGuard, .isaExIntro, .isaExElim, .folPred, .folForall,
             .folExists,
             .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
             .folNotElim,
             .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim,
             .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            nil
        }
    }

    /// ⚠ THE ONLY PLACE THAT SAYS WHICH KINDS BIND, AND WHAT. The traversal, the index engine
    /// and `looseBound` all read it here; a second list would let them disagree.
    public func mapChildren(_ f: (NodeID, Binds) throws -> NodeID) rethrows -> Node {
        switch self {
        case .isaFree, .isaBound, .isaOfClass, .folBottom, .folBound, .isaPropBound:
            self

        case .ifolAll(let T, let b): .ifolAll(T, body: try f(b, .term))

        case .ifolEx(let T, let b): .ifolEx(T, body: try f(b, .term))

        case .isaConst(let n, let T, let xs): .isaConst(n, T, args: try xs.map { try f($0, .none) })

        case .isaVarApp(let h, let xs):
            .isaVarApp(head: try f(h, .none), args: try xs.map { try f($0, .none) })

        case .isaAbs(let T, let b): .isaAbs(T, body: try f(b, .term))

        case .isaAllIntro(let T, let b): .isaAllIntro(T, body: try f(b, .term))

        case .isaAllElim(let p, let x): .isaAllElim(try f(p, .none), try f(x, .none))

        case .isaReflexive(let x): .isaReflexive(try f(x, .none))

        case .isaSymmetric(let T, let p): .isaSymmetric(T, try f(p, .none))

        case .isaTransitive(let T, let p, let q): .isaTransitive(T, try f(p, .none), try f(q, .none))

        case .isaCombination(let T, let p, let q): .isaCombination(T, try f(p, .none), try f(q, .none))

        case .isaAbstract(let T, let p): .isaAbstract(T, try f(p, .none))

        case .isaClassical(let a, let h): .isaClassical(try f(a, .none), try f(h, .none))

        case .isaIffReflection(let a, let b, let h): .isaIffReflection(
                try f(a, .none),
                try f(b, .none),
                try f(h, .none),
            )

        case .isaDefinition(let axiom, let d, let types, let stated, let xs):
            .isaDefinition(axiom, of: d, types, try f(stated, .none), args: try xs.map { try f($0, .none) })

        case .isaPropAll(let b): .isaPropAll(body: try f(b, .term))

        case .isaPropIntro(let b): .isaPropIntro(body: try f(b, .term))

        case .folImplies(let a, let b): .folImplies(try f(a, .none), try f(b, .none))

        case .folAnd(let a, let b): .folAnd(try f(a, .none), try f(b, .none))

        case .folOr(let a, let b): .folOr(try f(a, .none), try f(b, .none))

        case .folIff(let a, let b): .folIff(try f(a, .none), try f(b, .none))

        case .folNot(let a): .folNot(try f(a, .none))

        case .folImpliesIntro(let a, let b): .folImpliesIntro(try f(a, .none), body: try f(b, .hyp))

        case .folImpliesElim(let p, let q): .folImpliesElim(try f(p, .none), try f(q, .none))

        case .use(let n, let types, let root): .use(n, types, try f(root, .none))

        case .hyp(let k, let a): .hyp(k, try f(a, .none))

        case .isaGuard(let x, let g): .isaGuard(try f(x, .none), try f(g, .none))

        case .isaExIntro(let p, let v): .isaExIntro(try f(p, .none), try f(v, .none))

        case .isaExElim(let T, let p, let b): .isaExElim(T, try f(p, .none), body: try f(b, .termAndHyp))

        case .folPred(let n, let xs): .folPred(n, args: try xs.map { try f($0, .none) })

        case .folForall(let b): .folForall(body: try f(b, .term))

        case .folExists(let b): .folExists(body: try f(b, .term))

        case .folAndIntro(let p, let q): .folAndIntro(try f(p, .none), try f(q, .none))

        case .folAndElimL(let p): .folAndElimL(try f(p, .none))

        case .folAndElimR(let p): .folAndElimR(try f(p, .none))

        case .folOrIntroL(let p, let b): .folOrIntroL(try f(p, .none), try f(b, .none))

        case .folOrIntroR(let a, let q): .folOrIntroR(try f(a, .none), try f(q, .none))

        case .folOrElim(let p, let q, let r): .folOrElim(try f(p, .none), try f(q, .none), try f(r, .none))

        case .folNotIntro(let a, let b): .folNotIntro(try f(a, .none), body: try f(b, .hyp))

        case .folNotElim(let p, let q): .folNotElim(try f(p, .none), try f(q, .none))

        case .folIffIntro(let p, let q): .folIffIntro(try f(p, .none), try f(q, .none))

        case .folIffElimL(let p, let q): .folIffElimL(try f(p, .none), try f(q, .none))

        case .folIffElimR(let p, let q): .folIffElimR(try f(p, .none), try f(q, .none))

        case .folForallIntro(let b): .folForallIntro(body: try f(b, .term))

        case .folForallElim(let p, let v): .folForallElim(try f(p, .none), try f(v, .none))

        case .folExistsIntro(let p, let v): .folExistsIntro(try f(p, .none), try f(v, .none))

        case .folExistsElim(let p, let b): .folExistsElim(try f(p, .none), body: try f(b, .termAndHyp))

        case .folBottomElim(let p, let c): .folBottomElim(try f(p, .none), try f(c, .none))

        case .folClassicalAbsurd(let a, let b): .folClassicalAbsurd(try f(a, .none), body: try f(b, .hyp))

        case .folSchemaInst(let p, let a): .folSchemaInst(try f(p, .none), try f(a, .none))

        case .folLetterAll(let k, let b): .folLetterAll(k, body: try f(b, .term))

        case .folLetter(let h, let xs): .folLetter(head: try f(h, .none), args: try xs.map { try f($0, .none) })

        case .folLetterAbs(let b): .folLetterAbs(body: try f(b, .term))
        }
    }

    public func forEachChild(_ f: (NodeID, Binds) throws -> Void) rethrows {
        _ = try mapChildren { c, binds in try f(c, binds)
            return c
        }
    }

}
