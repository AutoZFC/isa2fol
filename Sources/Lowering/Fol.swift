import IR

@frozen public enum FolError: Error, Equatable {
    case unguardedBinder(NodeID)
    case unboundVariable(NodeID)
    case unboundHypothesis(Int)
    case instanceNotAVariable(NodeID)
    case notItsGuard(NodeID)
}

public struct Fol: Pass {
    public let name = "fol"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .forall?, .exists?, .intro?, .instance?, .guardOf?, .variable?: return .rule
        case .unbuilt?: return .unbuilt
        case .renumber?, nil: return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, FolRule(), in: &t)
    }
}

private enum Piece {
    case forall, exists, intro, instance, guardOf, variable
    case unbuilt
    case renumber
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .ifolAll(T, _): return object(T, .forall)
    case let .ifolEx(T, _): return object(T, .exists)
    case let .isaAllIntro(T, _): return object(T, .intro)
    case let .isaAllElim(_, T): return object(T, .instance)
    case let .isaGuard(T, _): return object(T, .guardOf)
    case let .isaBound(T): return mentionsTypeVariable(T) || p.dialects.contains(.fol) ? nil : T == .i ? .variable : .unbuilt
    case .hyp: return .renumber
    case .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro,
         .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
         .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
         .folClassicalAbsurd, .folSchemaInst:
        return nil
    }
}

private func object(_ T: IRType, _ atI: Piece) -> Piece? {
    T == .i ? atI : isObject(T) ? .unbuilt : nil
}

private enum Entry: Hashable {
    case fix(guarded: Bool)
    case assume
}

private struct FolRule: Rule {
    var start: [Entry] { [] }

    func enter(_ c: [Entry], _ binder: Node, _ binds: Binds, in t: Table) -> [Entry] {
        let guarded: Bool
        switch piece(Pattern(binder, in: t)) {
        case .forall?, .exists?, .intro?: guarded = true
        case .instance?, .guardOf?, .variable?, .unbuilt?, .renumber?, nil: guarded = false
        }
        return c + Array(repeating: .fix(guarded: guarded), count: binds.terms)
            + Array(repeating: .assume, count: binds.hyps)
    }

    func narrow(_ c: [Entry], _ id: NodeID, in t: Table) -> [Entry] {
        var terms = t.looseBound(of: id), hyps = t.looseHyps(of: id), k = c.count
        while k > 0 && (terms > 0 || hyps > 0) {
            k -= 1
            switch c[k] {
            case .fix: terms -= 1
            case .assume: hyps -= 1
            }
        }
        return k == 0 ? c : Array(c[k...])
    }

    func after(_ n: Node, context c: [Entry], in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(n, in: t)) {
        case .forall?:
            return try t.intern(.folForall(body: try t.intern(.folImplies(try guardOfBound0(&t), children(n)[0]))))
        case .exists?:
            return try t.intern(.folExists(body: try t.intern(.folAnd(try guardOfBound0(&t), children(n)[0]))))
        case .intro?:
            return try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(try guardOfBound0(&t), body: children(n)[0]))))
        case .instance?:
            let (p, x) = (children(n)[0], children(n)[1])
            return try t.intern(.folImpliesElim(try t.intern(.folForallElim(p, x)), try discharge(x, c, &t)))
        case .guardOf?:
            let (x, g) = (children(n)[0], children(n)[1])
            let d = try discharge(x, c, &t)
            guard t.conclusion(of: d) == g else { throw FolError.notItsGuard(g) }
            return d
        case .variable?:
            return try t.intern(.folBound(n.boundVariable!.index))
        case .renumber?:
            let h = n.boundVariable!
            let g = try guardsAbove(hypothesis: h.index, in: c)
            return g == 0 ? nil : try t.intern(h.reindexed(h.index + g))
        case .unbuilt?, nil:
            return nil
        }
    }
}

private func guardOfBound0(_ t: inout Table) throws -> NodeID {
    try Typing.guarded(try t.intern(.folBound(0)), in: &t)
}

private func discharge(_ x: NodeID, _ c: [Entry], _ t: inout Table) throws -> NodeID {
    guard case let .folBound(k) = t[x] else { throw FolError.instanceNotAVariable(x) }
    return try t.intern(.hyp(try guardDistance(ofVariable: k, x, in: c), try Typing.guarded(x, in: &t)))
}

private func guardDistance(ofVariable k: Int, _ x: NodeID, in c: [Entry]) throws -> Int {
    var fixes = 0, between = 0
    for e in c.reversed() {
        switch e {
        case let .fix(guarded):
            if fixes == k {
                guard guarded else { throw FolError.unguardedBinder(x) }
                return between
            }
            fixes += 1
            if guarded { between += 1 }
        case .assume:
            between += 1
        }
    }
    throw FolError.unboundVariable(x)
}

private func guardsAbove(hypothesis k: Int, in c: [Entry]) throws -> Int {
    var assumes = 0, guards = 0
    for e in c.reversed() {
        switch e {
        case let .fix(guarded):
            if guarded { guards += 1 }
        case .assume:
            if assumes == k { return guards }
            assumes += 1
        }
    }
    throw FolError.unboundHypothesis(k)
}
