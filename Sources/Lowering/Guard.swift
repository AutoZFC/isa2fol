import IR

@frozen public enum GuardRefusal: Refusal, Equatable {
    case compoundInstantiation(NodeID)
}

@frozen public enum GuardError: Error, Equatable {
    case unguardedBinder(NodeID)
    case unboundVariable(NodeID)
    case unboundHypothesis(Int)
}

public struct Guard: Pass {
    public let name = "guard"

    public init() {}

    public func run(_ roots: [NodeID], in t: inout Table) throws -> [Rewrite] {
        try transform(roots, GuardRule(), in: &t)
    }
}

private enum Entry: Hashable {
    case fix(guarded: Bool)
    case assume
}

private struct GuardRule: Rule {
    var start: [Entry] { [] }

    func enter(_ c: [Entry], _ binder: Node, _ binds: Binds) -> [Entry] {
        c + Array(repeating: .fix(guarded: quantifiesAtI(binder)), count: binds.terms)
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
        if case let .ifolAll(.i, body) = n {
            return try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(try guardOfBound0(&t), body))))
        }
        if case let .ifolEx(.i, body) = n {
            return try t.intern(.ifolEx(.i, body: try t.intern(.folAnd(try guardOfBound0(&t), body))))
        }
        if case let .isaAllIntro(.i, body) = n {
            return try t.intern(.isaAllIntro(.i, body: try t.intern(.folImpliesIntro(try guardOfBound0(&t), body: body))))
        }
        if case let .isaAllElim(p, x) = n, case .ifolAll(.i, _)? = t.conclusion(of: p).map({ t[$0] }) {
            guard case let .isaBound(k, _) = t[x] else { throw GuardRefusal.compoundInstantiation(x) }
            let elim = try t.intern(n)
            let discharge = try t.intern(.hyp(try guardDistance(ofVariable: k, x, in: c), try set(x, &t)))
            return try t.intern(.folImpliesElim(elim, discharge))
        }
        if case let .hyp(k, a) = n {
            let g = try guardsAbove(hypothesis: k, in: c)
            return g == 0 ? nil : try t.intern(.hyp(k + g, a))
        }
        return nil
    }
}

private func set(_ x: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.isaConst("set", .fn(.i, .o), args: [x]))
}

private func guardOfBound0(_ t: inout Table) throws -> NodeID {
    try set(try t.intern(.isaBound(0, .i)), &t)
}

private func guardDistance(ofVariable k: Int, _ x: NodeID, in c: [Entry]) throws -> Int {
    var fixes = 0, between = 0
    for e in c.reversed() {
        switch e {
        case let .fix(guarded):
            if fixes == k {
                guard guarded else { throw GuardError.unguardedBinder(x) }
                return between
            }
            fixes += 1
            if guarded { between += 1 }
        case .assume:
            between += 1
        }
    }
    throw GuardError.unboundVariable(x)
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
    throw GuardError.unboundHypothesis(k)
}

private func quantifiesAtI(_ binder: Node) -> Bool {
    switch binder {
    case let .ifolAll(T, _), let .ifolEx(T, _), let .isaAllIntro(T, _):
        return T == .i
    case .isaConst, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllElim,
         .folImplies, .folAnd, .folOr, .folIff, .folNot, .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp,
         .folBound, .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR,
         .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro, .folIffElimL,
         .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
         .folClassicalAbsurd, .isaFree:
        return false
    }
}
