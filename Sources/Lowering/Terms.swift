import IR

@frozen
public enum TermsError: Error, Equatable, Sendable {
    case notItsConstraint(String)
    case noFact(String)
}

func cited(_ r: some Request, _ statement: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.use(.lemma(Lemma(r)), [], statement))
}

struct TermProofs {
    let base: Base

    func existence(_ r: Existence, in t: inout Table) throws -> NodeID {
        var f = Frame()
        for T in r.types { _ = f.fix(T) }
        let outer = f.scope.depth
        var naming = Naming()
        let value = try naming.name(r.term, [], &t)
        let constraints = try naming.chain.stated()
        var witnesses = [Int]()
        var hypotheses = [Int]()
        for (j, piece) in naming.pieces.enumerated() {
            let at = Refs(outer: outer, witnesses: witnesses, frame: f)
            let (w, h) = try f.open(try witness(piece, at, hypotheses, naming.pieces, &t), in: &t)
            let assumed = try f.hypothesis(h, in: &t)
            guard t.conclusion(of: assumed) == constraints[j] else { throw TermsError.notItsConstraint(r.name) }
            witnesses.append(w)
            hypotheses.append(h)
        }
        let r0 = try Refs(outer: outer, witnesses: witnesses, frame: f).node(value, &t)
        var z = Frame(f.scope)
        let zl = z.fix(.i)
        let hz = z.assume(try t.intern(.folPred(
            .base("eq"),
            args: [try z.variable(zl, in: &t), try z.scope.lift(r0, from: f.scope.depth, in: &t)],
        )))
        let term = try z.scope.lift(r.term, from: outer, in: &t)
        let atZ = try equation(try z.variable(zl, in: &t), term, in: &t)
        let closedChain = try closing(
            try named(atom: t[atZ], in: &t),
            try witnesses.map { try z.variable($0, in: &t) },
            try hypotheses.map { try z.hypothesis($0, in: &t) },
            try z.hypothesis(hz, in: &t),
            in: &t,
        )
        let atY = try equation(try t.intern(.isaBound(0, .i)), try shift(term, by: 1, in: &t), in: &t)
        let some = try t.intern(.ifolEx(.i, body: try named(atom: t[atY], in: &t)))
        let everyZ = try z.close(
            try introduced(some, at: [try z.variable(zl, in: &t)], from: closedChain, in: &t),
            in: &t,
        )
        let reflexive = try eliminated(try base.cite(.eqRefl, in: &t), at: [r0], in: &t)
        return try f.close(try t.intern(.folImpliesElim(try t.intern(.isaAllElim(everyZ, r0)), reflexive)), in: &t)
    }

    func uniqueness(_ r: Uniqueness, in t: inout Table) throws -> NodeID {
        var f = Frame()
        var guards = [Int: Int]()
        for (j, T) in r.types.enumerated() {
            let v = f.fix(T)
            if T != .i, let g = try guarded(try f.variable(v, in: &t), T, in: &t) { guards[j] = f.assume(g) }
        }
        let outer = f.scope.depth
        var naming = Naming()
        let v1 = try naming.name(r.term, [], &t)
        let v2 = try naming.name(r.term, [], &t)
        let constraints = try naming.chain.stated()
        let binders = naming.chain.binders
        let m = binders.count / 2
        var witnesses = [Int]()
        var hypotheses = [Int]()
        for k in binders.indices {
            witnesses.append(f.fix(binders[k] == .set ? .i : nil))
            hypotheses.append(f.assume(constraints[k]))
        }
        let at = Refs(outer: outer, witnesses: witnesses, frame: f)
        let guardOf = { (x: NodeID, t: inout Table) throws -> NodeID in
            let atOuter = try shift(x, by: outer - f.scope.depth, in: &t)
            guard case .isaBound(let d, _) = t[atOuter], let g = guards[r.types.count - 1 - d] else {
                throw TermsError.noFact("the guard of \(x)")
            }
            return try f.hypothesis(g, in: &t)
        }
        var agreed = [NodeID]()
        for j in 0..<m {
            agreed.append(try agreement(
                naming.pieces[j],
                naming.pieces[m + j],
                j,
                m,
                at,
                hypotheses,
                naming.pieces,
                agreed,
                guardOf,
                &t,
            ))
        }
        guard case .bound(let k) = v1, case .bound(let k2) = v2, k2 == k + m else { throw TermsError.noFact(r.name) }
        return try f.close(agreed[k], in: &t)
    }

    private func witness(
        _ piece: NamedPiece,
        _ at: Refs,
        _ hypotheses: [Int],
        _ pieces: [NamedPiece],
        _ t: inout Table,
    ) throws -> NodeID {
        switch piece {
        case .setConstant(let c):
            return try setConstantFact(c, .existence, &t)

        case .constantClass(let c, let T, let classes):
            let f = ConstantFact(constant: c, type: T, fact: .classExists)
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try classes.map { try at.node($0, &t) },
                in: &t,
            )

        case .lambdaClass(let lambda):
            let (f, c) = try lambdaFact(try at.lift(lambda, &t), .classExists, in: &t)
            return try instantiated(
                try cited(f, try statement(f, base: base, in: &t), &t),
                at: try c.variables.map { try walked($0, base: base, in: &t) },
                c.types,
                guards: false,
                guardOf: isaGuard,
                in: &t,
            )

        case .tuple(let entries):
            let f = TupleFact(arity: entries.count, fact: .existence)
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try entries.map { try at.node($0, &t) },
                in: &t,
            )

        case .value(tuple: let tau, cls: let C):
            guard
                case .bound(let kc) = C, case .constantClass(let c, let T, let classes) = pieces[kc],
                case .bound(let kt) = tau,
                case .tuple(let entries) = pieces[kt]
            else { throw TermsError.noFact("a value") }
            let f = ConstantFact(constant: c, type: T, fact: .totality)
            let total = try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try (classes + [C]).map { try at.node($0, &t) },
                premises: [try at.frame.hypothesis(hypotheses[kc], in: &t)],
                in: &t,
            )
            return try eliminated(
                total,
                at: try (entries + [tau]).map { try at.node($0, &t) },
                premises: [try at.frame.hypothesis(hypotheses[kt], in: &t)],
                in: &t,
            )

        case .applied(tuple: let tau, function: let fn):
            return try eliminated(
                try base.cite(.applyEX, in: &t),
                at: [try at.lift(fn, &t), try at.node(tau, &t)],
                in: &t,
            )
        }
    }

    private func agreement(
        _ p: NamedPiece,
        _ p2: NamedPiece,
        _ j: Int,
        _ m: Int,
        _ at: Refs,
        _ hypotheses: [Int],
        _ pieces: [NamedPiece],
        _ agreed: [NodeID],
        _ guardOf: (NodeID, inout Table) throws -> NodeID,
        _ t: inout Table,
    ) throws -> NodeID {
        let hyp = { (k: Int, t: inout Table) throws -> NodeID in try at.frame.hypothesis(hypotheses[k], in: &t) }
        let w = try at.node(.bound(j), &t)
        let w2 = try at.node(.bound(j + m), &t)
        let unexpected = TermsError.noFact("two namings of one term differ at binder \(j)")
        switch p {
        case .setConstant(let c):
            guard case .setConstant(c) = p2 else { throw unexpected }
            return try eliminated(
                try setConstantFact(c, .uniqueness, &t),
                at: [w, w2],
                premises: [try hyp(j, &t), try hyp(j + m, &t)],
                in: &t,
            )

        case .constantClass(let c, let T, let classes):
            guard case .constantClass(c, T, let classes2) = p2 else { throw unexpected }
            let f = ConstantFact(constant: c, type: T, fact: .agreement)
            let same = try zip(classes, classes2).map { try classAgreement($0, $1, m, agreed) }
            let args = try (classes + classes2).map { try at.node($0, &t) } + [w, w2]
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: args,
                premises: same + [try hyp(j, &t), try hyp(j + m, &t)],
                in: &t,
            )

        case .lambdaClass(let lambda):
            guard case .lambdaClass(lambda) = p2 else { throw unexpected }
            return try definitionsAgree(try hyp(j, &t), try hyp(j + m, &t), in: at.frame.scope, &t)

        case .tuple(let entries):
            guard case .tuple(let entries2) = p2, entries.count == entries2.count else { throw unexpected }
            let f = TupleFact(arity: entries.count, fact: .uniqueness)
            let equal = try zip(entries, entries2).map { try equality($0, $1, m, at, agreed, &t) }
            let unique = try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try (entries + entries2).map { try at.node($0, &t) },
                premises: equal,
                in: &t,
            )
            return try eliminated(unique, at: [w, w2], premises: [try hyp(j, &t), try hyp(j + m, &t)], in: &t)

        case .value(tuple: let tau, cls: let C):
            guard
                case .value(tuple: let tau2, cls: let C2) = p2, case .bound(let kc) = C, case .constantClass(
                    let c,
                    let T,
                    let classes,
                ) = pieces[kc],
                case .bound(let kt) = tau
            else { throw unexpected }
            let f = ConstantFact(constant: c, type: T, fact: .function)
            let classGuards = try zip(classes, T.domains.filter { $0 != .i }).compactMap { k, D -> NodeID? in
                isFunctionClass(D) ? try lambdaFunction(k, at, hypotheses, pieces, guardOf, &t) : nil
            }
            let function = try eliminated(
                try eliminated(
                    try cited(f, try statement(f, in: &t), &t),
                    at: try classes.map { try at.node($0, &t) },
                    premises: classGuards,
                    in: &t,
                ),
                at: [try at.node(C, &t)],
                premises: [try hyp(kc, &t)],
                in: &t,
            )
            let atC = try eliminated(
                try base.cite(.funcAt, in: &t),
                at: [try at.node(C, &t), try at.node(C2, &t)],
                premises: [function, agreed[kc]],
                in: &t,
            )
            let atTau = try eliminated(
                atC,
                at: [try at.node(tau, &t), try at.node(tau2, &t)],
                premises: [agreed[kt]],
                in: &t,
            )
            return try eliminated(atTau, at: [w, w2], premises: [try hyp(j, &t), try hyp(j + m, &t)], in: &t)

        case .applied(tuple: let tau, function: let fn):
            guard case .applied(tuple: let tau2, function: fn) = p2, case .bound(let kt) = tau else { throw unexpected }
            let F = try at.lift(fn, &t)
            let atF = try eliminated(try base.cite(.applyAt, in: &t), at: [F], premises: [try guardOf(F, &t)], in: &t)
            let atTau = try eliminated(
                atF,
                at: [try at.node(tau, &t), try at.node(tau2, &t)],
                premises: [agreed[kt]],
                in: &t,
            )
            return try eliminated(atTau, at: [w, w2], premises: [try hyp(j, &t), try hyp(j + m, &t)], in: &t)
        }
    }

    private func classAgreement(_ k: Ref, _ k2: Ref, _ m: Int, _ agreed: [NodeID]) throws -> NodeID {
        guard
            case .bound(let a) = k, case .bound(let b) = k2,
            b == a + m
        else { throw TermsError.noFact("a class argument") }
        return agreed[a]
    }

    private func equality(
        _ x: Ref,
        _ x2: Ref,
        _ m: Int,
        _ at: Refs,
        _ agreed: [NodeID],
        _ t: inout Table,
    ) throws -> NodeID {
        if case .bound(let a) = x, case .bound(let b) = x2, b == a + m { return agreed[a] }
        guard
            case .outer(let y) = x, case .outer(let y2) = x2,
            y == y2
        else { throw TermsError.noFact("a tuple's entry") }
        return try eliminated(try base.cite(.eqRefl, in: &t), at: [try at.lift(y, &t)], in: &t)
    }

    private func lambdaFunction(
        _ k: Ref,
        _ at: Refs,
        _ hypotheses: [Int],
        _ pieces: [NamedPiece],
        _ guardOf: (NodeID, inout Table) throws -> NodeID,
        _ t: inout Table,
    ) throws -> NodeID {
        guard
            case .bound(let kk) = k,
            case .lambdaClass(let lambda) = pieces[kk]
        else { throw TermsError.noFact("a function λ") }
        let (f, c) = try lambdaFact(try at.lift(lambda, &t), .function, in: &t)
        let atVariables = try instantiated(
            try cited(f, try statement(f, base: base, in: &t), &t),
            at: try c.variables.map { try walked($0, base: base, in: &t) },
            c.types,
            guards: true,
            guardOf: { x, _, t in try guardOf(x, &t) },
            in: &t,
        )
        return try eliminated(
            atVariables,
            at: [try at.node(k, &t)],
            premises: [try at.frame.hypothesis(hypotheses[kk], in: &t)],
            in: &t,
        )
    }

    private func definitionsAgree(_ d: NodeID, _ d2: NodeID, in s: Scope, _ t: inout Table) throws -> NodeID {
        guard let c = t.conclusion(of: d) else { throw TableError.expectedStep(d) }
        var arity = 0
        var inner = c
        while case .ifolAll(.i, let body) = t[inner] { (arity, inner) = (arity + 1, body) }
        var f = Frame(s)
        let xs = (0..<arity).map { _ in f.fix(.i) }
        let at = try xs.map { try f.variable($0, in: &t) }
        let e = try eliminated(try f.scope.lift(d, from: s.depth, in: &t), at: at, in: &t)
        let e2 = try eliminated(try f.scope.lift(d2, from: s.depth, in: &t), at: at, in: &t)
        return try f.close(try iffThrough(e, e2, base, &t), in: &t)
    }

    private func setConstantFact(_ c: Constant, _ fact: ConstantFact.Fact, _ t: inout Table) throws -> NodeID {
        let existence = fact == .existence
        switch c {
        case .primitive(.zf(.zero)): return try base.cite(existence ? .zfZeroEX : .zfZeroUNIQ, in: &t)

        case .primitive(.zf(.inf)): return try base.cite(existence ? .zfInfEX : .zfInfUNIQ, in: &t)

        case .defined:
            let f = ConstantFact(constant: c, type: .i, fact: fact)
            return try cited(f, try statement(f, in: &t), &t)

        case .primitive(.zf(.mem)), .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)),
             .primitive(.pure),
             .primitive(.ifol), .declared:
            throw TermsError.noFact("\(c.name), a set constant")
        }
    }
}

func iffThrough(_ p: NodeID, _ q: NodeID, _ base: Base, _ t: inout Table) throws -> NodeID {
    guard
        case .folIff(let a, let c)? = t.conclusion(of: p).map({ t[$0] }),
        case .folIff(let b, let c2)? = t.conclusion(of: q).map({ t[$0] }),
        c == c2
    else { throw TableError.principalConnective(p) }
    return try base.applied(.iffTrans, [a, c, b], [p, try base.applied(.iffSymm, [b, c], [q], in: &t)], in: &t)
}

struct Refs {
    let outer: Int
    let witnesses: [Int]
    let frame: Frame

    func node(_ r: Ref, _ t: inout Table) throws -> NodeID {
        switch r {
        case .outer(let x): try lift(x, &t)
        case .bound(let k): try frame.variable(witnesses[k], in: &t)
        }
    }

    func lift(_ x: NodeID, _ t: inout Table) throws -> NodeID {
        try frame.scope.lift(x, from: outer, in: &t)
    }
}
