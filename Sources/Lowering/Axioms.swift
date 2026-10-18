import IR

@frozen
public enum AxiomError: Error, Equatable, Sendable {
    case notMine(String)
    case noReading(NodeID)
    case misread(NodeID)
}

struct AxiomFact: Request {
    let axiom: Axiom.ZF
    let stated: NodeID
    let statement: NodeID

    var name: String {
        axiom.rawValue + "_AXIOM"
    }
}

func axiomCited(_ n: Node, was id: NodeID, in t: inout Table) throws -> NodeID {
    guard
        case .use(.axiom(.zf(let a)), _, let stated) = t[id],
        case .use(_, _, let statement) = n
    else { throw AxiomError.notMine("\(id)") }
    return try cited(AxiomFact(axiom: a, stated: stated, statement: statement), statement, &t)
}

extension Axiom.ZF {
    var inNBG: BaseStatement? {
        switch self {
        case .extension: .zfExtensionNBG
        case .unionIff: .zfUnionIffNBG
        case .powIff: .zfPowIffNBG
        case .replacement: .zfReplacementNBG
        case .foundation: .zfFoundationNBG
        case .infinity: .zfInfinityNBG
        case .choice: nil
        }
    }

    var members: String? {
        switch self {
        case .infinity: "upair.succ_iff"
        case .extension, .unionIff, .powIff, .replacement, .foundation, .choice: nil
        }
    }
}

public struct AxiomProver: Prover {
    public init(base: Base) {
        self.base = base
    }

    public let name = "axioms"

    public func owns(_ l: Lemma) -> Owned? {
        l.request is AxiomFact ? .rule : nil
    }

    public func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        _ theorems: [String: NodeID],
        in t: inout Table,
    ) throws -> Proved {
        guard let r = l.request as? AxiomFact, let words = r.axiom.inNBG else { throw AxiomError.notMine(l.name) }
        var members: (name: String, root: NodeID)?
        if let name = r.axiom.members {
            guard let root = theorems[name] else { return .cites(name) }
            members = (name, root)
        }
        let reading = AxiomReading(base: base, definitions: definitions, members: members)
        var slots = [LambdaFact]()
        let read = try reading.target(r.stated, Scope(), &slots, &t)
        let equivalence = try Replacement(base: base) { phi, l, w, s, t in try reading.hole(phi, l, w, s, &t) }
            .proof(r.stated, r.statement, read, in: Scope(), &t)
        let premises = try slots.map { try Lowering.statement($0, base: base, in: &t) }
        var root = read
        for premise in premises.reversed() { root = try t.intern(.folImplies(premise, root)) }
        var held = try t.intern(.use(.base(words.rawValue), [], root))
        for (f, premise) in zip(slots, premises) {
            held = try t.intern(.folImpliesElim(held, try cited(f, premise, &t)))
        }
        let proof = try t.intern(.folIffElimR(equivalence, held))
        guard t.conclusion(of: proof) == statement else { throw AxiomError.misread(statement) }
        return .proof(proof)
    }

    public func defines(_: Defined) -> Owned? {
        nil
    }

    public func define(_ c: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        throw AxiomError.notMine(c.name)
    }

    let base: Base
}

private struct Application {
    let constant: Constant
    let type: IRType
    let args: [NodeID]
}

private struct AxiomReading {
    let base: Base
    let definitions: [Definition]
    let members: (name: String, root: NodeID)?

    var graphs: GraphProofs {
        GraphProofs(base: base, definitions: definitions)
    }

    func target(_ phi: NodeID, _ s: Scope, _ slots: inout [LambdaFact], _ t: inout Table) throws -> NodeID {
        if let (_, d, args) = predicate(phi, t) {
            return try target(try beta(d.definiens, args, in: &t), s, &slots, &t)
        }
        if let (x, a) = try primitive(phi, t) {
            for lambda in classes(a) {
                let (f, _) = try lambdaFact(lambda, .classExists, in: &t)
                if !slots.contains(f) { slots.append(f) }
            }
            return try primitiveWords(x, a, &t)
        }
        if let (a, other) = try function(phi, t) { return try functionWords(a, other, &t) }
        switch t[phi] {
        case .folAnd(let a, let b):
            return try t.intern(.folAnd(try target(a, s, &slots, &t), try target(b, s, &slots, &t)))

        case .folOr(let a, let b):
            return try t.intern(.folOr(try target(a, s, &slots, &t), try target(b, s, &slots, &t)))

        case .folImplies(let a, let b):
            return try t.intern(.folImplies(try target(a, s, &slots, &t), try target(b, s, &slots, &t)))

        case .folIff(let a, let b):
            return try t.intern(.folIff(try target(a, s, &slots, &t), try target(b, s, &slots, &t)))

        case .folNot(let a):
            return try t.intern(.folNot(try target(a, s, &slots, &t)))

        case .ifolAll(let T, let body):
            var inner = s
            _ = inner.fix(T)
            return try t.intern(.ifolAll(T, body: try target(body, inner, &slots, &t)))

        case .ifolEx(let T, let body):
            var inner = s
            _ = inner.fix(T)
            return try t.intern(.ifolEx(T, body: try target(body, inner, &slots, &t)))

        case .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folBottom, .folImpliesIntro,
             .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .isaGuard, .isaExIntro, .isaExElim, .folBound,
             .folPred, .folForall, .folExists, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
             .folOrElim, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro,
             .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
             .folLetterAbs:
            return try walked(formula: phi, in: &t)
        }
    }

    func hole(_ phi: NodeID, _ l: NodeID, _ w: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID? {
        if let (c, d, args) = predicate(phi, t) {
            let stated = try pointwiseDefinition(c, d, in: &t)
            let unfolding = try Lowering.unfolding(
                c,
                stated: stated,
                statement: try walked(formula: stated, in: &t),
                at: args,
                base: base,
                in: &t,
            )
            let (left, unfolded) = try sides(unfolding, t)
            guard left == l else { throw AxiomError.misread(phi) }
            let body = try beta(d.definiens, args, in: &t)
            var slots = [LambdaFact]()
            guard try target(body, s, &slots, &t) == w else { throw AxiomError.misread(phi) }
            let inner = try Replacement(base: base) { phi, l, w, s, t in try hole(phi, l, w, s, &t) }
                .proof(body, unfolded, w, in: s, &t)
            return try base.applied(.iffTrans, [l, unfolded, w], [unfolding, inner], in: &t)
        }
        if let (x, a) = try primitive(phi, t) {
            guard try primitiveWords(x, a, &t) == w else { throw AxiomError.misread(phi) }
            return try primitiveProof(a, l, w, s, &t)
        }
        if let (a, other) = try function(phi, t) {
            guard try functionWords(a, other, &t) == w else { throw AxiomError.misread(phi) }
            return try functionProof(a, l, w, s, &t)
        }
        return nil
    }

    private func predicate(_ phi: NodeID, _ t: Table) -> (Defined, Definition, [NodeID])? {
        guard
            case .isaConst(.defined(let c), let T, let args) = t[phi], result(T) == .o, !unfolds(c.family, c.level),
            args.count == T.domains.count,
            let d = definitions.first(where: { $0.defines == .constant(c) })
        else { return nil }
        return (c, d, args)
    }

    private func primitive(_ phi: NodeID, _ t: Table) throws -> (NodeID, Application)? {
        guard
            case .isaConst(.primitive(.zf(.mem)), _, let atom) = t[phi], atom.count == 2,
            case .isaConst(let c, let T, let args) = t[atom[1]], isPrimitiveFunction(c)
        else { return nil }
        guard
            case .isaBound = t[atom[0]], args.indices.allSatisfy({ k in
                T.domains[k] == .i ? isBound(args[k], t) : isAbs(args[k], t)
            })
        else { throw AxiomError.noReading(phi) }
        return (atom[0], Application(constant: c, type: T, args: args))
    }

    private func function(_ phi: NodeID, _ t: Table) throws -> (Application, NodeID)? {
        guard
            case .isaConst(.primitive(.zf(.mem)), _, let atom) = t[phi], atom.count == 2,
            case .isaConst(.defined(let f), let T, let args) = t[atom[0]], result(T) == .i, !T.domains.isEmpty
        else { return nil }
        guard members != nil, T.domains.allSatisfy({ $0 == .i }), args.allSatisfy({ isBound($0, t) }) else {
            throw AxiomError.noReading(phi)
        }
        return (Application(constant: .defined(f), type: T, args: args), atom[1])
    }

    private func sets(_ a: Application) -> [NodeID] {
        a.args.indices.filter { a.type.domains[$0] == .i }.map { a.args[$0] }
    }

    private func classes(_ a: Application) -> [NodeID] {
        a.args.indices.filter { a.type.domains[$0] != .i }.map { a.args[$0] }
    }

    private func primitiveWords(_ x: NodeID, _ a: Application, _ t: inout Table) throws -> NodeID {
        var chain = Chain()
        var ks = [Ref]()
        for lambda in classes(a) {
            let K = chain.bind(.cls)
            chain.constrain(
                K,
                try classDefinition(try chain.here(.outer(lambda), in: &t), K: try chain.here(K, in: &t), in: &t),
            )
            ks.append(K)
        }
        let u = chain.bind(.set)
        chain.constrain(u, try related(
            a.constant,
            sets: try sets(a).map { try chain.here(.outer($0), in: &t) },
            classes: try ks.map { try chain.here($0, in: &t) },
            value: try chain.here(u, in: &t),
            &t,
        ))
        return try chain.formula(try chain.predicate(.base("elem"), [.outer(x), u], in: &t), in: &t)
    }

    private func related(
        _ c: Constant,
        sets: [NodeID],
        classes: [NodeID],
        value: NodeID,
        _ t: inout Table,
    ) throws -> NodeID {
        let definition = try graphs.definitionCited(c, &t)
        guard case .use(_, _, var at) = t[definition] else { throw AxiomError.noReading(value) }
        for x in [value] + classes {
            guard case .folForall(let body) = t[at] else { throw AxiomError.noReading(at) }
            at = try instantiate(body, with: x, in: &t)
        }
        guard case .folIff(_, let held) = t[at] else { throw AxiomError.noReading(at) }
        at = held
        for x in [value, value] {
            guard case .ifolAll(.i, let body) = t[at] else { throw AxiomError.noReading(at) }
            at = try instantiate(body, with: x, in: &t)
        }
        guard case .folIff(_, var entries) = t[at] else { throw AxiomError.noReading(at) }
        for x in sets {
            guard case .ifolEx(.i, let body) = t[entries] else { throw AxiomError.noReading(entries) }
            entries = try instantiate(body, with: x, in: &t)
        }
        guard case .folAnd(_, let body) = t[entries] else { throw AxiomError.noReading(entries) }
        return body
    }

    private func primitiveProof(
        _ a: Application,
        _ l: NodeID,
        _ w: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let k = classes(a).count
        let at = AtTuple(
            base: base,
            graphs: graphs,
            constant: a.constant,
            type: a.type,
            sets: try sets(a).map { try level($0, s, t) },
            name: a.constant.name,
        )
        var fw = Frame(s)
        let hl = fw.assume(l)
        let o = try fw.open(chain: .hypothesis(hl), Array(repeating: .cls, count: k) + [.cls, .set, .set], in: &t)
        let ks = Array(o.witnesses[..<k])
        let hks = try o.constraints[..<k].map { try fw.have(try fw.proof($0, in: &t), in: &t) }
        let hc = try fw.have(try fw.proof(o.constraints[k], in: &t), in: &t)
        let ht = try fw.have(try fw.proof(o.constraints[k + 1], in: &t), in: &t)
        let r = o.witnesses[k + 2]
        let member = try at.converted(o.witnesses[k], ks, hc, o.witnesses[k + 1], ht, value: r, &fw, &t)
        let related = try t.intern(.folIffElimL(member, try fw.proof(o.constraints[k + 2], in: &t)))
        let forward = try fw.close(
            try closing(
                try fw.scope.lift(w, from: s.depth, in: &t),
                try (ks + [r]).map { try fw.variable($0, in: &t) },
                try hks.map { try fw.hypothesis($0, in: &t) } + [related],
                try fw.proof(o.core, in: &t),
                in: &t,
            ),
            in: &t,
        )

        var bw = Frame(s)
        let hw = bw.assume(w)
        let ob = try bw.open(chain: .hypothesis(hw), Array(repeating: .cls, count: k) + [.set], in: &t)
        let bks = Array(ob.witnesses[..<k])
        let bhks = try ob.constraints[..<k].map { try bw.have(try bw.proof($0, in: &t), in: &t) }
        let hb = try bw.have(try bw.proof(ob.constraints[k], in: &t), in: &t)
        let u = ob.witnesses[k]
        let (c, hc2) = try bw.open(try at.classExists(bks, bw, &t), in: &t)
        let (tw, ht2) = try bw.open(try at.tupleExists(bw, &t), in: &t)
        let member2 = try at.converted(c, bks, hc2, tw, ht2, value: u, &bw, &t)
        let valued = try t.intern(.folIffElimR(member2, try bw.hypothesis(hb, in: &t)))
        let backward = try bw.close(
            try closing(
                try bw.scope.lift(l, from: s.depth, in: &t),
                try (bks + [c, tw, u]).map { try bw.variable($0, in: &t) },
                try (bhks + [hc2, ht2]).map { try bw.hypothesis($0, in: &t) } + [valued],
                try bw.proof(ob.core, in: &t),
                in: &t,
            ),
            in: &t,
        )
        return try t.intern(.folIffIntro(forward, backward))
    }

    private func functionWords(_ a: Application, _ other: NodeID, _ t: inout Table) throws -> NodeID {
        var chain = Chain()
        let v = chain.bind(.set)
        let z = try t.intern(.isaBound(0, .i))
        let psi = try membership(
            z: z,
            args: try a.args.map { try shift(try chain.here(.outer($0), in: &t), by: 1, in: &t) },
            &t,
        ).psi
        let into = try t.intern(.folPred(.base("elem"), args: [z, try t.intern(.isaBound(1, .i))]))
        chain.constrain(v, try t.intern(.ifolAll(.i, body: try t.intern(.folIff(into, psi)))))
        let core = try walked(
            formula: try t.intern(.isaConst(
                .primitive(.zf(.mem)),
                .fn(.i, .fn(.i, .o)),
                args: [try chain.here(v, in: &t), try chain.here(.outer(other), in: &t)],
            )),
            in: &t,
        )
        return try chain.formula(core, in: &t)
    }

    private func membership(z: NodeID, args: [NodeID], _ t: inout Table) throws -> (named: NodeID, psi: NodeID) {
        guard let members else { throw AxiomError.noReading(z) }
        var at = members.root
        for x in [z] + args {
            guard case .ifolAll(.i, let body) = t[at] else { throw AxiomError.noReading(at) }
            at = try instantiate(body, with: x, in: &t)
        }
        guard case .folAnd(let into, _) = t[at], case .folImplies(let named, let psi) = t[into] else {
            throw AxiomError.noReading(at)
        }
        return (named, psi)
    }

    private func functionProof(
        _ a: Application,
        _ l: NodeID,
        _ w: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        let ys = try a.args.map { try level($0, s, t) }
        let at = AtTuple(
            base: base,
            graphs: graphs,
            constant: a.constant,
            type: a.type,
            sets: ys,
            name: a.constant.name,
        )
        let named = Members(application: a, arguments: ys, theorem: members, base: base)

        var fw = Frame(s)
        let hl = fw.assume(l)
        let o = try fw.open(chain: .hypothesis(hl), [.cls, .set, .set], in: &t)
        let value = try o.constraints.map { try fw.have(try fw.proof($0, in: &t), in: &t) }
        let every = try named.members(Array(o.witnesses), value, fw, &t)
        let forward = try fw.close(
            try closing(
                try fw.scope.lift(w, from: s.depth, in: &t),
                [try fw.variable(o.witnesses[2], in: &t)],
                [every],
                try fw.proof(o.core, in: &t),
                in: &t,
            ),
            in: &t,
        )

        var bw = Frame(s)
        let hw = bw.assume(w)
        let ob = try bw.open(chain: .hypothesis(hw), [.set], in: &t)
        let v = ob.witnesses[0]
        let hall = try bw.have(try bw.proof(ob.constraints[0], in: &t), in: &t)
        let (c, hc) = try bw.open(try at.classExists([], bw, &t), in: &t)
        let (tw, ht) = try bw.open(try at.tupleExists(bw, &t), in: &t)
        let total = ConstantFact(constant: a.constant, type: a.type, fact: .totality)
        let atC = try eliminated(
            try cited(total, try statement(total, in: &t), &t),
            at: [try bw.variable(c, in: &t)],
            premises: [try bw.hypothesis(hc, in: &t)],
            in: &t,
        )
        let (v0, hv0) = try bw.open(
            try eliminated(
                atC,
                at: try (ys + [tw]).map { try bw.variable($0, in: &t) },
                premises: [try bw.hypothesis(ht, in: &t)],
                in: &t,
            ),
            in: &t,
        )
        let hall0 = try bw.have(try named.members([c, tw, v0], [hc, ht, hv0], bw, &t), in: &t)
        var fz = Frame(bw.scope)
        let z = fz.fix(.i)
        let x = try fz.variable(z, in: &t)
        let at0 = try t.intern(.isaAllElim(try fz.hypothesis(hall0, in: &t), x))
        let atV = try t.intern(.isaAllElim(try fz.hypothesis(hall, in: &t), x))
        let (in0, psi) = try sides(at0, t)
        let inV = try sides(atV, t).left
        let flipped = try base.applied(.iffSymm, [inV, psi], [atV], in: &t)
        let agree = try fz.close(try base.applied(.iffTrans, [in0, psi, inV], [at0, flipped], in: &t), in: &t)
        let ext = try eliminated(
            try base.cite(.extensionality, in: &t),
            at: [try bw.variable(v0, in: &t), try bw.variable(v, in: &t)],
            in: &t,
        )
        let heq = try bw.have(try t.intern(.folIffElimR(ext, agree)), in: &t)
        let lifted = try bw.scope.lift(w, from: s.depth, in: &t)
        guard case .ifolEx(.i, let chained) = t[lifted] else { throw AxiomError.misread(w) }
        let atV0 = try instantiate(chained, with: try bw.variable(v0, in: &t), in: &t)
        guard case .folAnd(_, let atS) = t[atV0] else { throw AxiomError.misread(w) }
        let core = try bw.proof(ob.core, in: &t)
        guard let atV1 = t.conclusion(of: core) else { throw TableError.expectedStep(core) }
        let moved = try Replacement(base: base) { phi, l, r, sc, t in
            guard case .folPred = t[phi] else { return nil }
            return try congruent(l, r, base, { _, _, t in
                try base.claimed(
                    .eqSymm,
                    [try sc.variable(v0, in: &t), try sc.variable(v, in: &t)],
                    [try sc.hypothesis(heq, in: &t)],
                    in: &t,
                )
            }, &t)
        }.proof(atV1, atV1, atS, in: bw.scope, &t)
        let backward = try bw.close(
            try closing(
                try bw.scope.lift(l, from: s.depth, in: &t),
                try [c, tw, v0].map { try bw.variable($0, in: &t) },
                try [hc, ht, hv0].map { try bw.hypothesis($0, in: &t) },
                try t.intern(.folIffElimL(moved, core)),
                in: &t,
            ),
            in: &t,
        )
        return try t.intern(.folIffIntro(forward, backward))
    }

    private func level(_ x: NodeID, _ s: Scope, _ t: Table) throws -> Int {
        guard case .isaBound(let k, .i) = t[x] else { throw AxiomError.noReading(x) }
        return s.depth - 1 - k
    }
}

private func isPrimitiveFunction(_ c: Constant) -> Bool {
    switch c {
    case .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)): true
    case .primitive(.zf(.mem)), .primitive(.zf(.zero)), .primitive(.zf(.inf)), .primitive(.pure), .primitive(.ifol),
         .defined, .declared:
        false
    }
}

private func isBound(_ x: NodeID, _ t: Table) -> Bool {
    if case .isaBound = t[x] { true } else { false }
}

private func isAbs(_ x: NodeID, _ t: Table) -> Bool {
    if case .isaAbs = t[x] { true } else { false }
}

private struct Members {
    let application: Application
    let arguments: [Int]
    let theorem: (name: String, root: NodeID)?
    let base: Base

    func members(_ named: [Int], _ hs: [Int], _ f: Frame, _ t: inout Table) throws -> NodeID {
        var fz = Frame(f.scope)
        let z = fz.fix(.i)
        let th = try instance(z, fz, &t)
        guard
            case .folAnd(let into, _)? = t.conclusion(of: th).map({ t[$0] }),
            case .folImplies(let naming, let psi) = t[into]
        else { throw AxiomError.misread(th) }
        let element = try t.intern(.folPred(
            .base("elem"),
            args: [try fz.variable(z, in: &t), try fz.variable(named[2], in: &t)],
        ))

        var fa = Frame(fz.scope)
        let hz = fa.assume(element)
        let witnessed = try closing(
            naming,
            try named.map { try fa.variable($0, in: &t) },
            try hs.map { try fa.hypothesis($0, in: &t) },
            try fa.hypothesis(hz, in: &t),
            in: &t,
        )
        let into1 = try fa.close(try t.intern(.folImpliesElim(try t.intern(.folAndElimL(th)), witnessed)), in: &t)

        var fb = Frame(fz.scope)
        let hp = fb.assume(psi)
        let hn = try fb.have(try t.intern(.folImpliesElim(
            try t.intern(.folAndElimR(th)),
            try fb.hypothesis(hp, in: &t),
        )), in: &t)
        let o = try fb.open(chain: .hypothesis(hn), [.cls, .set, .set], in: &t)
        let other = try o.constraints.map { try fb.have(try fb.proof($0, in: &t), in: &t) }
        let equal = try same(named, hs, Array(o.witnesses), other, fb, &t)
        let flipped = try base.claimed(
            .eqSymm,
            [try fb.variable(named[2], in: &t), try fb.variable(o.witnesses[2], in: &t)],
            [equal],
            in: &t,
        )
        let inOther = try fb.proof(o.core, in: &t)
        guard let atOther = t.conclusion(of: inOther) else { throw TableError.expectedStep(inOther) }
        // ⚠ A FORMULA BUILT AT ONE FRAME IS LIFTED BEFORE A DEEPER ONE READS IT: `element` names `z` and `v` by index,
        // and
        // read under the three binders `fb` opened it names `v2` and `τ2` — the congruence's premise mismatches.
        let moved = try congruent(
            atOther,
            try fb.scope.lift(element, from: fz.scope.depth, in: &t),
            base,
            { _, _, _ in flipped },
            &t,
        )
        let back = try fb.close(try t.intern(.folIffElimL(moved, inOther)), in: &t)
        return try fz.close(try t.intern(.folIffIntro(into1, back)), in: &t)
    }

    private func instance(_ z: Int, _ f: Frame, _ t: inout Table) throws -> NodeID {
        guard let theorem else { throw AxiomError.noReading(try f.variable(z, in: &t)) }
        return try eliminated(
            try t.intern(.use(.theorem(theorem.name), [], theorem.root)),
            at: try ([z] + arguments).map { try f.variable($0, in: &t) },
            in: &t,
        )
    }

    private func same(
        _ one: [Int],
        _ hs: [Int],
        _ two: [Int],
        _ hs2: [Int],
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let term = try t.intern(.isaConst(
            application.constant,
            application.type,
            args: try arguments.map { try f.variable($0, in: &t) },
        ))
        let c = try closed(term, in: &t)
        let u = try uniqueness(of: term, in: &t)
        var p = try instantiated(
            try cited(u, try statement(u, in: &t), &t),
            at: c.variables,
            c.types,
            guards: true,
            guardOf: isaGuard,
            in: &t,
        )
        for (x, h) in zip(one + two, hs + hs2) {
            p = try eliminated(p, at: [try f.variable(x, in: &t)], premises: [try f.hypothesis(h, in: &t)], in: &t)
        }
        return p
    }
}
