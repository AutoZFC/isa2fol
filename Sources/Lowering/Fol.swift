import IR

@frozen
public enum FolError: Error, Equatable {
    case unguardedBinder(NodeID)
    case unboundVariable(NodeID)
    case unboundHypothesis(Int)
    case instanceNotAVariable(NodeID)
    case notItsGuard(NodeID)
    case notGuardedExistential(NodeID)
}

public struct Fol: Pass {
    public init(base: Base) {
        self.base = base
    }

    public let name = "fol"

    public func owns(_ p: Pattern) -> Owned? {
        switch piece(p) {
        case .forall?, .exists?, .intro?, .instance?, .guardOf?, .variable?, .existsIntro?, .existsElim?,
             .hidden?: .rule
        case .unbuilt?: .unbuilt
        case .renumber?, nil: nil
        }
    }

    /// ⚠ ONE TRANSFORM OVER EVERY ROOT KEEPS ONE CACHE FOR ALL, A KEY PER NODE AND CONTEXT: it passed 32 GB once Logic
    /// built
    /// the instances at a class type. Per statement the cache lives for one; the outputs are interned, the unit the
    /// same.
    public func run(_ roots: [NodeID], _: [Definition], in t: inout Table) throws -> [NodeID] {
        try roots.map { try transform($0, FolRule(base: base), in: &t) }
    }

    let base: Base
}

private enum Piece {
    case forall(IRType)
    case exists(IRType)
    case intro(IRType)
    case instance
    case guardOf
    case variable
    case existsIntro
    case existsElim
    case hidden(IRType)
    case unbuilt
    case renumber
}

private func piece(_ p: Pattern) -> Piece? {
    switch p {
    case .ifolAll(let T, _): isObject(T) ? .forall(T) : nil
    case .ifolEx(let T, _): isObject(T) ? .exists(T) : nil
    case .isaAllIntro(let T, _): isObject(T) ? .intro(T) : nil
    case .isaAllElim(_, let T): T == .i ? .instance : nil
    case .isaGuard(let T, _): isObject(T) ? .guardOf : nil
    case .isaBound(let T): mentionsTypeVariable(T) || T == .o ? nil : isObject(T) ? .variable : .unbuilt
    case .isaExIntro(_, let T, _): T == .i ? .existsIntro : nil
    case .isaExElim(let T, _, _): T == .i ? .existsElim : nil
    case .isaHidden(let T, _): isObject(T) ? .hidden(T) : nil
    case .hyp: .renumber
    case .isaConst, .isaFree, .isaVarApp, .isaAbs, .isaOfClass, .isaReflexive, .isaSymmetric, .isaTransitive,
         .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro,
         .isaPropBound, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro,
         .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
         .folIffElimL, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
         .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
        nil
    }
}

private enum Entry: Hashable {
    case fix(IRType?)
    case assume
    case inserted(guard: Bool)
}

private struct FolRule: Rule {
    let base: Base

    var start: [Entry] {
        []
    }

    func enter(_ c: [Entry], _ binder: Node, _ binds: Binds, in t: Table) -> [Entry] {
        switch piece(Pattern(binder, in: t)) {
        case .intro(let T)?: c + [.fix(T)] + (guardPredicate(T) == nil ? [] : [.inserted(guard: true)])
        case .forall(let T)?, .exists(let T)?: c + [.fix(T)]
        case .existsElim?: c + [.fix(.i), .inserted(guard: false), .inserted(guard: true), .assume]
        case .hidden(let T)?: c + [.fix(T), .inserted(guard: guardPredicate(T) != nil)]
        case .instance?, .guardOf?, .variable?, .existsIntro?, .unbuilt?, .renumber?, nil:
            c + Array(repeating: .fix(nil), count: binds.terms) + Array(repeating: .assume, count: binds.hyps)
        }
    }

    func narrow(_ c: [Entry], _ id: NodeID, in t: Table) -> [Entry] {
        var terms = t.looseBound(of: id)
        var hyps = t.looseHyps(of: id)
        var k = c.count
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
        case .forall(let T)?:
            return try t.intern(.folForall(body: try guardedBody(T, children(n)[0], in: &t)))

        case .exists(let T)?:
            let body = children(n)[0]
            guard let g = try guardOfBound0(T, &t) else { return try t.intern(.folExists(body: body)) }
            return try t.intern(.folExists(body: try t.intern(.folAnd(g, body))))

        case .intro(let T)?:
            let body = children(n)[0]
            guard let g = try guardOfBound0(T, &t) else { return try t.intern(.folForallIntro(body: body)) }
            return try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(g, body: body))))

        case .instance?:
            let p = children(n)[0]
            let x = children(n)[1]
            return try t.intern(.folImpliesElim(try t.intern(.folForallElim(p, x)), try discharge(x, c, &t)))

        case .guardOf?:
            let x = children(n)[0]
            let g = children(n)[1]
            let d = try discharge(x, c, &t)
            guard t.conclusion(of: d) == g else { throw FolError.notItsGuard(g) }
            return d

        case .variable?:
            return try t.intern(.folBound(n.boundVariable!.index))

        case .existsIntro?:
            let q = children(n)[0]
            let x = children(n)[1]
            guard let g = try guardOfBound0(.i, &t) else { throw FolError.notGuardedExistential(id) }
            let instance = try t.intern(.folSchemaInst(
                try base.cite(.exIntro, in: &t),
                try t.intern(.folLetterAbs(body: try t.intern(.folAnd(g, children(n)[2])))),
            ))
            return try t.intern(.folImpliesElim(
                try t.intern(.folForallElim(instance, x)),
                try t.intern(.folAndIntro(try discharge(x, c, &t), q)),
            ))

        case .existsElim?:
            guard
                case .isaExElim(_, let p, let body) = n,
                case .folExists(let both)? = t.conclusion(of: p).map({ t[$0] }),
                case .folAnd(let g, let phi) = t[both]
            else { throw FolError.notGuardedExistential(id) }
            let opened = try t.intern(.hyp(0, both))
            let split = try t.intern(.folImpliesIntro(g, body: try t.intern(.folImpliesIntro(phi, body: body))))
            let guarded = try t.intern(.folImpliesElim(split, try t.intern(.folAndElimL(opened))))
            return try t.intern(.folExistsElim(
                p,
                body: try t.intern(.folImpliesElim(guarded, try t.intern(.folAndElimR(opened)))),
            ))

        case .hidden(let T)?:
            return try t.intern(.folExistsElim(try base.cite(inhabited(T), in: &t), body: children(n)[0]))

        case .renumber?:
            let h = n.boundVariable!
            let k = try renumbered(hypothesis: h.index, in: c)
            return k == h.index ? nil : try t.intern(h.reindexed(k))

        case .unbuilt?, nil:
            return nil
        }
    }
}

private func inhabited(_ T: IRType) -> BaseStatement {
    T != .i && guardPredicate(T) != nil ? .functionInhabited : .setInhabited
}

private func guardOfBound0(_ T: IRType, _ t: inout Table) throws -> NodeID? {
    try guarded(try t.intern(.folBound(0)), T, in: &t)
}

private func discharge(_ x: NodeID, _ c: [Entry], _ t: inout Table) throws -> NodeID {
    guard case .folBound(let k) = t[x] else { throw FolError.instanceNotAVariable(x) }
    var fixes = 0
    var hyps = 0
    var guardAt: Int?
    for e in c.reversed() {
        switch e {
        case .fix(let T):
            if fixes == k {
                guard
                    let T, let j = guardAt,
                    let g = try guarded(x, T, in: &t)
                else { throw FolError.unguardedBinder(x) }
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
    var assumes = 0
    var hyps = 0
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
