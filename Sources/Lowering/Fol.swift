import IR

@frozen public enum FolError: Error, Equatable {
    case unguardedBinder(NodeID)
    case unboundVariable(NodeID)
    case unboundHypothesis(Int)
    case instanceNotAVariable(NodeID)
    case notItsGuard(NodeID)
    case notGuardedExistential(NodeID)
}

public struct Fol: Pass {
    public let name = "fol"

    public init() {}

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .forall?, .exists?, .intro?, .instance?, .guardOf?, .variable?, .existsIntro?, .existsElim?: return .rule
        case .unbuilt?: return .unbuilt
        case .renumber?, nil: return nil
        }
    }

    public func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, FolRule(), in: &t)
    }
}

private enum Piece {
    case forall(IRType), exists(IRType), intro(IRType)
    case instance, guardOf, variable, existsIntro, existsElim
    case unbuilt
    case renumber
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case let .ifolAll(T, _): return isObject(T) ? .forall(T) : nil
    case let .ifolEx(T, _): return isObject(T) ? .exists(T) : nil
    case let .isaAllIntro(T, _): return isObject(T) ? .intro(T) : nil
    case let .isaAllElim(_, T): return T == .i ? .instance : nil
    case let .isaGuard(T, _): return isObject(T) ? .guardOf : nil
    case let .isaBound(T): return mentionsTypeVariable(T) || T == .o ? nil : isObject(T) ? .variable : .unbuilt
    case let .isaExIntro(_, T): return T == .i ? .existsIntro : nil
    case let .isaExElim(T, _, _): return T == .i ? .existsElim : nil
    case .hyp: return .renumber
    case .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaReflexive, .isaSymmetric, .isaTransitive,
         .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro,
         .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
         .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
         .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        return nil
    }
}

private enum Entry: Hashable {
    case fix(IRType?)
    case assume
    case inserted(guard: Bool)
}

private struct FolRule: Rule {
    var start: [Entry] { [] }

    func enter(_ c: [Entry], _ binder: Node, _ binds: Binds, in t: Table) -> [Entry] {
        switch piece(Pattern(binder, in: t)) {
        case let .intro(T)?: return c + [.fix(T)] + (Reify.guardPredicate(T) == nil ? [] : [.inserted(guard: true)])
        case let .forall(T)?, let .exists(T)?: return c + [.fix(T)]
        case .existsElim?: return c + [.fix(.i), .inserted(guard: false), .inserted(guard: true), .assume]
        case .instance?, .guardOf?, .variable?, .existsIntro?, .unbuilt?, .renumber?, nil:
            return c + Array(repeating: .fix(nil), count: binds.terms) + Array(repeating: .assume, count: binds.hyps)
        }
    }

    func narrow(_ c: [Entry], _ id: NodeID, in t: Table) -> [Entry] {
        var terms = t.looseBound(of: id), hyps = t.looseHyps(of: id), k = c.count
        while k > 0 && (terms > 0 || hyps > 0) {
            k -= 1
            switch c[k] {
            case .fix: terms -= 1
            case .assume: hyps -= 1
            case .inserted: break
            }
        }
        return k == 0 ? c : Array(c[k...])
    }

    func after(_ n: Node, was id: NodeID, context c: [Entry], in t: inout Table) throws -> NodeID? {
        switch piece(Pattern(t[id], in: t)) {
        case let .forall(T)?:
            let body = children(n)[0]
            guard let g = try guardOfBound0(T, &t) else { return try t.intern(.folForall(body: body)) }
            return try t.intern(.folForall(body: try t.intern(.folImplies(g, body))))
        case let .exists(T)?:
            let body = children(n)[0]
            guard let g = try guardOfBound0(T, &t) else { return try t.intern(.folExists(body: body)) }
            return try t.intern(.folExists(body: try t.intern(.folAnd(g, body))))
        case let .intro(T)?:
            let body = children(n)[0]
            guard let g = try guardOfBound0(T, &t) else { return try t.intern(.folForallIntro(body: body)) }
            return try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(g, body: body))))
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
        case .existsIntro?:
            let (q, x) = (children(n)[0], children(n)[1])
            return try t.intern(.folExistsIntro(try t.intern(.folAndIntro(try discharge(x, c, &t), q)), x))
        case .existsElim?:
            guard case let .isaExElim(_, p, body) = n, case let .folExists(both)? = t.conclusion(of: p).map({ t[$0] }),
                  case let .folAnd(g, phi) = t[both] else { throw FolError.notGuardedExistential(id) }
            let opened = try t.intern(.hyp(0, both))
            let split = try t.intern(.folImpliesIntro(g, body: try t.intern(.folImpliesIntro(phi, body: body))))
            let guarded = try t.intern(.folImpliesElim(split, try t.intern(.folAndElimL(opened))))
            return try t.intern(.folExistsElim(p, body: try t.intern(.folImpliesElim(guarded, try t.intern(.folAndElimR(opened))))))
        case .renumber?:
            let h = n.boundVariable!
            let k = try renumbered(hypothesis: h.index, in: c)
            return k == h.index ? nil : try t.intern(h.reindexed(k))
        case .unbuilt?, nil:
            return nil
        }
    }
}

private func guardOfBound0(_ T: IRType, _ t: inout Table) throws -> NodeID? {
    try Reify.guarded(try t.intern(.folBound(0)), T, in: &t)
}

private func discharge(_ x: NodeID, _ c: [Entry], _ t: inout Table) throws -> NodeID {
    guard case let .folBound(k) = t[x] else { throw FolError.instanceNotAVariable(x) }
    var fixes = 0, hyps = 0, guardAt: Int?
    for e in c.reversed() {
        switch e {
        case let .fix(T):
            if fixes == k {
                guard let T, let j = guardAt, let g = try Reify.guarded(x, T, in: &t) else { throw FolError.unguardedBinder(x) }
                return try t.intern(.hyp(j, g))
            }
            fixes += 1
            guardAt = nil
        case .assume, .inserted(guard: false):
            hyps += 1
        case .inserted(guard: true):
            guardAt = hyps
            hyps += 1
        }
    }
    throw FolError.unboundVariable(x)
}

private func renumbered(hypothesis k: Int, in c: [Entry]) throws -> Int {
    var assumes = 0, hyps = 0
    for e in c.reversed() {
        switch e {
        case .fix:
            break
        case .assume:
            if assumes == k { return hyps }
            assumes += 1
            hyps += 1
        case .inserted:
            hyps += 1
        }
    }
    throw FolError.unboundHypothesis(k)
}
