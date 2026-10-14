import IR

public struct Logic: Pass {
    public let name = "logic"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .kernel?, .instance?: return .rule
        case .unbuilt?: return .unbuilt
        case nil: return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, Steps(), in: &t)
    }
}

private enum Piece {
    case kernel(Kernel)
    case instance
    case unbuilt
}

private enum Kernel {
    case equalIntr, equalElim, reflexive, symmetric, transitive
    case identity, conjI, conjunct1, conjunct2, disjI1, disjI2, disjE, falseE, iffReflection, classical
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .use(.axiom(a), types, _):
        guard isLogic(a.family), !types.contains(where: mentionsTypeVariable) else { return nil }
        guard let k = kernel(a, types) else { return .unbuilt }
        return .kernel(k)
    case let .isaConst(.primitive(.pure(.eq)), T, _):
        return mentionsTypeVariable(T) ? nil : .unbuilt
    case let .isaAllElim(_, T):
        return T == .o ? .instance : beyondObjects(T) ? .unbuilt : nil
    case let .ifolAll(T, _), let .ifolEx(T, _), let .isaAllIntro(T, _):
        return T != .o && beyondObjects(T) ? .unbuilt : nil
    case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .folImplies, .folAnd, .folOr, .folIff,
         .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .isaGuard, .folNot, .folBound, .folPred, .folForall,
         .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro,
         .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
         .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst:
        return nil
    }
}

private func beyondObjects(_ T: IRType) -> Bool { !isObject(T) && !mentionsTypeVariable(T) }

private func kernel(_ a: Axiom, _ types: [IRType]) -> Kernel? {
    switch a {
    case .pure(.equalIntr): return .equalIntr
    case .pure(.equalElim): return .equalElim
    case .pure(.reflexive): return types == [.o] ? .reflexive : nil
    case .pure(.symmetric): return types == [.o] ? .symmetric : nil
    case .pure(.transitive): return types == [.o] ? .transitive : nil
    case .pure(.combination), .pure(.abstractRule): return nil
    case .ifol(.impI), .ifol(.mp): return .identity
    case .ifol(.conjI): return .conjI
    case .ifol(.conjunct1): return .conjunct1
    case .ifol(.conjunct2): return .conjunct2
    case .ifol(.disjI1): return .disjI1
    case .ifol(.disjI2): return .disjI2
    case .ifol(.disjE): return .disjE
    case .ifol(.falseE): return .falseE
    case .ifol(.iffReflection): return .iffReflection
    case .ifol(.refl), .ifol(.subst), .ifol(.allI), .ifol(.spec), .ifol(.exI), .ifol(.exE), .ifol(.eqReflection): return nil
    case .fol(.classical): return .classical
    case .zf: return nil
    }
}

private struct Steps: Rule {
    var start: Anywhere { Anywhere() }
    func enter(_ c: Anywhere, _ binder: Node, _ binds: Binds, in t: Table) -> Anywhere { c }

    func after(_ n: Node, context: Anywhere, in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case let .kernel(k)?:
            return try proof(k, in: &t)
        case .instance?:
            let (p, a) = (children(n)[0], children(n)[1])
            if case let .isaAllIntro(_, body) = t[p] { return try instantiate(body, with: a, in: &t) }
            return try t.intern(.folSchemaInst(p, a))
        case .unbuilt?, nil:
            return nil
        }
    }
}

private func proof(_ k: Kernel, in t: inout Table) throws -> NodeID {
    func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, .o)) }
    func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folImplies(a, b)) }
    func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID { try n(.folIff(a, b)) }
    func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID { try n(.folImpliesIntro(a, body: body)) }
    func hyp(_ k: Int, _ a: NodeID) throws -> NodeID { try n(.hyp(k, a)) }
    let letters: Int, body: NodeID
    switch k {
    case .equalIntr:
        let (p, q) = (try v(1), try v(0)), pq = try imp(p, q), qp = try imp(q, p)
        (letters, body) = (2, try assume(pq, try assume(qp, try n(.folIffIntro(try hyp(1, pq), try hyp(0, qp))))))
    case .equalElim:
        let (p, q) = (try v(1), try v(0)), h = try iff(p, q)
        (letters, body) = (2, try assume(h, try assume(p, try n(.folIffElimL(try hyp(1, h), try hyp(0, p))))))
    case .reflexive:
        let p = try v(0), same = try assume(p, try hyp(0, p))
        (letters, body) = (1, try n(.folIffIntro(same, same)))
    case .symmetric:
        let (p, q) = (try v(1), try v(0)), h = try iff(p, q)
        let qp = try assume(q, try n(.folIffElimR(try hyp(1, h), try hyp(0, q))))
        let pq = try assume(p, try n(.folIffElimL(try hyp(1, h), try hyp(0, p))))
        (letters, body) = (2, try assume(h, try n(.folIffIntro(qp, pq))))
    case .transitive:
        let (p, q, r) = (try v(2), try v(1), try v(0)), h1 = try iff(p, q), h2 = try iff(q, r)
        let pr = try assume(p, try n(.folIffElimL(try hyp(1, h2), try n(.folIffElimL(try hyp(2, h1), try hyp(0, p))))))
        let rp = try assume(r, try n(.folIffElimR(try hyp(2, h1), try n(.folIffElimR(try hyp(1, h2), try hyp(0, r))))))
        (letters, body) = (3, try assume(h1, try assume(h2, try n(.folIffIntro(pr, rp)))))
    case .identity:
        let h = try imp(try v(1), try v(0))
        (letters, body) = (2, try assume(h, try hyp(0, h)))
    case .conjI:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(p, try assume(q, try n(.folAndIntro(try hyp(1, p), try hyp(0, q))))))
    case .conjunct1:
        let h = try n(.folAnd(try v(1), try v(0)))
        (letters, body) = (2, try assume(h, try n(.folAndElimL(try hyp(0, h)))))
    case .conjunct2:
        let h = try n(.folAnd(try v(1), try v(0)))
        (letters, body) = (2, try assume(h, try n(.folAndElimR(try hyp(0, h)))))
    case .disjI1:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(p, try n(.folOrIntroL(try hyp(0, p), q))))
    case .disjI2:
        let (p, q) = (try v(1), try v(0))
        (letters, body) = (2, try assume(q, try n(.folOrIntroR(p, try hyp(0, q)))))
    case .disjE:
        let (p, q, r) = (try v(2), try v(1), try v(0))
        let either = try n(.folOr(p, q)), fromP = try imp(p, r), fromQ = try imp(q, r)
        let cases = try n(.folOrElim(try hyp(2, either), try hyp(1, fromP), try hyp(0, fromQ)))
        (letters, body) = (3, try assume(either, try assume(fromP, try assume(fromQ, cases))))
    case .falseE:
        let bottom = try n(.folBottom)
        (letters, body) = (1, try assume(bottom, try n(.folBottomElim(try hyp(0, bottom), try v(0)))))
    case .iffReflection:
        let (p, q) = (try v(1), try v(0)), h = try n(.folAnd(try imp(p, q), try imp(q, p)))
        let (pq, qp) = (try n(.folAndElimL(try hyp(0, h))), try n(.folAndElimR(try hyp(0, h))))
        (letters, body) = (2, try assume(h, try n(.folIffIntro(pq, qp))))
    case .classical:
        let p = try v(0), notP = try n(.folNot(p)), h = try imp(try imp(p, try n(.folBottom)), p)
        let refuted = try assume(p, try n(.folNotElim(try hyp(1, notP), try hyp(0, p))))
        let absurd = try n(.folNotElim(try hyp(0, notP), try n(.folImpliesElim(try hyp(1, h), refuted))))
        (letters, body) = (1, try assume(h, try n(.folClassicalAbsurd(p, body: absurd))))
    }
    var proved = body
    for _ in 0..<letters { proved = try n(.isaAllIntro(.o, body: proved)) }
    return proved
}
