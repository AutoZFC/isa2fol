public struct NodeID: Hashable, Sendable, CustomStringConvertible {
    let raw: UInt32
    public var description: String { "%\(raw)" }
}

@frozen public enum Namespace: Hashable, Sendable {
    case term
    case hyp
}

public struct Binds: Hashable, Sendable {
    public let terms: Int
    public let hyps: Int
    public static let none = Binds(terms: 0, hyps: 0)
    public static let term = Binds(terms: 1, hyps: 0)
    public static let hyp = Binds(terms: 0, hyps: 1)
    public static let termAndHyp = Binds(terms: 1, hyps: 1)
}

@frozen public enum Free: Hashable, Sendable {
    case named(String)
    case hidden
}

@frozen public enum Predicate: Hashable, Sendable {
    case base(String)
    case constant(Constant)

    public var name: String {
        switch self {
        case let .base(name): return name
        case let .constant(c): return c.name
        }
    }
}

@frozen public enum Node: Hashable, Sendable {
    // THE READER'S OUTPUT is the next two groups and nothing else (DESIGN §4.3b).
    // Isa only, but at `o` a binder, its intro and its variable are fol-zfc's schema letter — a free the statement is
    // closed over; Pure's `⋀` over a proposition, written in a formula or a proof, is `isaProp*`: lowering replaces the rest.
    case ifolAll(IRType, body: NodeID)
    case ifolEx(IRType, body: NodeID)
    case isaConst(Constant, IRType, args: [NodeID])
    case isaFree(Free, IRType)
    case isaBound(Int, IRType)
    case isaVarApp(head: NodeID, args: [NodeID])
    case isaAbs(IRType, body: NodeID)
    case isaOfClass(IRType, String)
    case isaAllIntro(IRType, body: NodeID)
    case isaAllElim(NodeID, NodeID)
    case isaReflexive(NodeID)
    case isaSymmetric(IRType, NodeID)
    case isaTransitive(IRType, NodeID, NodeID)
    case isaCombination(IRType, NodeID, NodeID)
    case isaAbstract(IRType, NodeID)
    case isaClassical(NodeID, NodeID)
    case isaIffReflection(NodeID, NodeID, NodeID)
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

    // Isa only, lowering's: a proof before fol cites a variable's guard, which fol writes and resolves; and `∃` at an isa
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

    /// ⚠ THE ONLY PLACE THAT SAYS WHICH KINDS BIND, AND WHAT. The traversal, the index engine
    /// and `looseBound` all read it here; a second list would let them disagree.
    public func mapChildren(_ f: (NodeID, Binds) throws -> NodeID) rethrows -> Node {
        switch self {
        case .isaFree, .isaBound, .isaOfClass, .folBottom, .folBound, .isaPropBound:
            return self
        case let .ifolAll(T, b): return .ifolAll(T, body: try f(b, .term))
        case let .ifolEx(T, b): return .ifolEx(T, body: try f(b, .term))
        case let .isaConst(n, T, xs): return .isaConst(n, T, args: try xs.map { try f($0, .none) })
        case let .isaVarApp(h, xs):
            return .isaVarApp(head: try f(h, .none), args: try xs.map { try f($0, .none) })
        case let .isaAbs(T, b): return .isaAbs(T, body: try f(b, .term))
        case let .isaAllIntro(T, b): return .isaAllIntro(T, body: try f(b, .term))
        case let .isaAllElim(p, x): return .isaAllElim(try f(p, .none), try f(x, .none))
        case let .isaReflexive(x): return .isaReflexive(try f(x, .none))
        case let .isaSymmetric(T, p): return .isaSymmetric(T, try f(p, .none))
        case let .isaTransitive(T, p, q): return .isaTransitive(T, try f(p, .none), try f(q, .none))
        case let .isaCombination(T, p, q): return .isaCombination(T, try f(p, .none), try f(q, .none))
        case let .isaAbstract(T, p): return .isaAbstract(T, try f(p, .none))
        case let .isaClassical(a, h): return .isaClassical(try f(a, .none), try f(h, .none))
        case let .isaIffReflection(a, b, h): return .isaIffReflection(try f(a, .none), try f(b, .none), try f(h, .none))
        case let .isaPropAll(b): return .isaPropAll(body: try f(b, .term))
        case let .isaPropIntro(b): return .isaPropIntro(body: try f(b, .term))

        case let .folImplies(a, b): return .folImplies(try f(a, .none), try f(b, .none))
        case let .folAnd(a, b): return .folAnd(try f(a, .none), try f(b, .none))
        case let .folOr(a, b): return .folOr(try f(a, .none), try f(b, .none))
        case let .folIff(a, b): return .folIff(try f(a, .none), try f(b, .none))
        case let .folNot(a): return .folNot(try f(a, .none))
        case let .folImpliesIntro(a, b): return .folImpliesIntro(try f(a, .none), body: try f(b, .hyp))
        case let .folImpliesElim(p, q): return .folImpliesElim(try f(p, .none), try f(q, .none))
        case let .use(n, types, root): return .use(n, types, try f(root, .none))
        case let .hyp(k, a): return .hyp(k, try f(a, .none))
        case let .isaGuard(x, g): return .isaGuard(try f(x, .none), try f(g, .none))
        case let .isaExIntro(p, v): return .isaExIntro(try f(p, .none), try f(v, .none))
        case let .isaExElim(T, p, b): return .isaExElim(T, try f(p, .none), body: try f(b, .termAndHyp))

        case let .folPred(n, xs): return .folPred(n, args: try xs.map { try f($0, .none) })
        case let .folForall(b): return .folForall(body: try f(b, .term))
        case let .folExists(b): return .folExists(body: try f(b, .term))
        case let .folAndIntro(p, q): return .folAndIntro(try f(p, .none), try f(q, .none))
        case let .folAndElimL(p): return .folAndElimL(try f(p, .none))
        case let .folAndElimR(p): return .folAndElimR(try f(p, .none))
        case let .folOrIntroL(p, b): return .folOrIntroL(try f(p, .none), try f(b, .none))
        case let .folOrIntroR(a, q): return .folOrIntroR(try f(a, .none), try f(q, .none))
        case let .folOrElim(p, q, r): return .folOrElim(try f(p, .none), try f(q, .none), try f(r, .none))
        case let .folNotIntro(a, b): return .folNotIntro(try f(a, .none), body: try f(b, .hyp))
        case let .folNotElim(p, q): return .folNotElim(try f(p, .none), try f(q, .none))
        case let .folIffIntro(p, q): return .folIffIntro(try f(p, .none), try f(q, .none))
        case let .folIffElimL(p, q): return .folIffElimL(try f(p, .none), try f(q, .none))
        case let .folIffElimR(p, q): return .folIffElimR(try f(p, .none), try f(q, .none))
        case let .folForallIntro(b): return .folForallIntro(body: try f(b, .term))
        case let .folForallElim(p, v): return .folForallElim(try f(p, .none), try f(v, .none))
        case let .folExistsIntro(p, v): return .folExistsIntro(try f(p, .none), try f(v, .none))
        case let .folExistsElim(p, b): return .folExistsElim(try f(p, .none), body: try f(b, .termAndHyp))
        case let .folBottomElim(p, c): return .folBottomElim(try f(p, .none), try f(c, .none))
        case let .folClassicalAbsurd(a, b): return .folClassicalAbsurd(try f(a, .none), body: try f(b, .hyp))
        case let .folSchemaInst(p, a): return .folSchemaInst(try f(p, .none), try f(a, .none))
        case let .folLetterAll(k, b): return .folLetterAll(k, body: try f(b, .term))
        case let .folLetter(h, xs): return .folLetter(head: try f(h, .none), args: try xs.map { try f($0, .none) })
        case let .folLetterAbs(b): return .folLetterAbs(body: try f(b, .term))
        }
    }

    public func forEachChild(_ f: (NodeID, Binds) throws -> Void) rethrows {
        _ = try mapChildren { c, binds in try f(c, binds); return c }
    }

    public var boundVariable: (namespace: Namespace, index: Int, reindexed: (Int) -> Node)? {
        switch self {
        case let .isaBound(k, T): return (.term, k, { .isaBound($0, T) })
        case let .hyp(k, a): return (.hyp, k, { .hyp($0, a) })
        case let .folBound(k): return (.term, k, { .folBound($0) })
        case let .isaPropBound(k): return (.term, k, { .isaPropBound($0) })
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim,
             .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaPropAll, .isaPropIntro,
             .folImplies, .folAnd, .folOr, .folIff, .folNot, .folBottom, .folImpliesIntro, .folImpliesElim,
             .use, .isaGuard, .isaExIntro, .isaExElim, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR,
             .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
             .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
             .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            return nil
        }
    }
}
