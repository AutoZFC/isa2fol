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

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> AxiomFact {
        AxiomFact(axiom: axiom, stated: try f(stated), statement: try f(statement))
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
        _ theorems: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved {
        guard let r = l.request as? AxiomFact else { throw AxiomError.notMine(l.name) }
        switch r.axiom {
        case .choice: return try chosen(r, statement, theorems, in: &t)
        case .extension, .unionIff, .powIff, .replacement, .foundation, .infinity: break
        }
        guard let words = r.axiom.inNBG else { throw AxiomError.notMine(l.name) }
        var members: (name: String, root: NodeID)?
        if let name = r.axiom.members {
            guard let named = theorems[name] else { return .cites(name) }
            members = (name, named.statement)
        }
        let reading = AxiomReading(base: base, definitions: definitions, members: members)
        if try reading.unbuilt(r.stated, &t) { return .unbuilt }
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

    /// ⚠ AN ISA PROOF, LOWERED BY LOGIC'S WALK: written in Logic's form, its instances at λs and its values would be a
    /// second copy of Logic's rules.
    private func chosen(
        _ r: AxiomFact,
        _ statement: NodeID,
        _ theorems: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved {
        let name = "func.lam_type"
        guard let lamType = theorems[name] else { return .cites(name) }
        guard
            case .ifolAll(.i, let a) = t[r.stated], case .ifolAll(.i, let aA) = t[a],
            case .ifolAll(let F, let aAB) = t[aA], case .folImplies(let member, let rest) = t[aAB],
            case .folImplies(let nonempty, let goal) = t[rest]
        else { throw AxiomError.misread(r.stated) }
        let function = try t.intern(.use(.base(BaseStatement.choiceFunction.rawValue), [], try choiceStatement(F, &t)))
        guard let some = t.conclusion(of: function), case .ifolEx(F, let chooses) = t[some] else {
            throw AxiomError.misread(function)
        }
        let bound = { (k: Int, T: IRType, t: inout Table) throws -> NodeID in try t.intern(.isaBound(k, T)) }
        let applied = { (f: NodeID, x: NodeID, t: inout Table) throws -> NodeID in
            try t.intern(.isaVarApp(head: f, args: [x]))
        }
        let x = try bound(0, .i, &t)
        let atX = try applied(try bound(2, F, &t), x, &t)
        let inA = try t.intern(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [x, try bound(3, .i, &t)]))
        let nonemptyAtX = try t.intern(.folImpliesElim(
            try t.intern(.isaAllElim(try t.intern(.hyp(2, try shift(nonempty, by: 2, in: &t))), x)),
            try t.intern(.hyp(0, inA)),
        ))
        let chosenAtX = try t.intern(.folImpliesElim(
            try t.intern(.isaAllElim(try t.intern(.hyp(1, try shift(chooses, by: 1, in: &t))), atX)),
            nonemptyAtX,
        ))
        let premise = try t.intern(.isaAllIntro(.i, body: try t.intern(.folImpliesIntro(inA, body: chosenAtX))))
        let composed = try t.intern(.isaAbs(.i, body: try applied(
            try bound(1, F, &t),
            try applied(try bound(2, F, &t), try bound(0, .i, &t), &t),
            &t,
        )))
        var built = try t.intern(.use(.theorem(name), [], lamType.stated))
        for y in [try bound(2, .i, &t), composed, try etaLong(try bound(1, F, &t), in: &t)] {
            built = try t.intern(.isaAllElim(built, y))
        }
        built = try t.intern(.folImpliesElim(built, premise))
        let shifted = try shift(goal, by: 1, in: &t)
        guard
            let membership = t.conclusion(of: built),
            case .isaConst(.primitive(.zf(.mem)), _, let xs) = t[membership], xs.count == 2,
            case .ifolEx(.i, let witnessed) = t[shifted]
        else { throw AxiomError.misread(built) }
        var proof = try t.intern(.isaExElim(F, function, body: try t.intern(.isaExIntro(
            built,
            xs[0],
            body: witnessed,
        ))))
        proof = try t.intern(.folImpliesIntro(nonempty, body: proof))
        proof = try t.intern(.folImpliesIntro(member, body: proof))
        for T in [F, .i, .i] { proof = try t.intern(.isaAllIntro(T, body: proof)) }
        var memo = Memo()
        let lowered = try Logic(base: base).run(
            [r.stated, proof],
            citing: [lamType.stated: lamType.statement],
            sharing: &memo,
            in: &t,
        )
        guard lowered[0] == statement, t.conclusion(of: lowered[1]) == statement else {
            throw AxiomError.misread(statement)
        }
        return .proof(lowered[1])
    }
}

private func choiceStatement(_ T: IRType, _ t: inout Table) throws -> NodeID {
    let mem = { (x: NodeID, y: NodeID, t: inout Table) throws -> NodeID in
        try t.intern(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [x, y]))
    }
    let s = try t.intern(.isaBound(0, .i))
    let member = try t.intern(.ifolEx(
        .i,
        body: try mem(try t.intern(.isaBound(0, .i)), try t.intern(.isaBound(1, .i)), &t),
    ))
    let chosen = try mem(try t.intern(.isaVarApp(head: try t.intern(.isaBound(1, T)), args: [s])), s, &t)
    return try t.intern(.ifolEx(T, body: try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(member, chosen))))))
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
        if Reify().names(Pattern(t[phi], in: t)) {
            var naming = Naming()
            let core = try naming.atom(t[phi], in: &t)
            return try words(naming.chain, core, &t)
        }
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
             .folExistsElim, .folCut, .folBottomElim, .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter,
             .folLetterAbs, .isaValue, .isaValueFact:
            return try formula(phi, .statement, in: &t)
        }
    }

    func hole(_ phi: NodeID, _ l: NodeID, _ w: NodeID, _ s: Scope, _ t: inout Table) throws -> NodeID? {
        if let (c, d, args) = predicate(phi, t) {
            let stated = try pointwiseDefinition(c, d, in: &t)
            let unfolding = try Lowering.unfolding(
                c,
                stated: stated,
                statement: try formula(stated, .statement, in: &t),
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
            return try primitiveProof(x, a, l, w, s, &t)
        }
        if let (a, other) = try function(phi, t) {
            guard try functionWords(a, other, &t) == w else { throw AxiomError.misread(phi) }
            return try functionProof(a, other, l, w, s, &t)
        }
        if Reify().names(Pattern(t[phi], in: t)) { return try piecesProof(phi, l, w, s, &t) }
        return nil
    }

    /// Whether reading `phi` meets what the reading does not have: an atom naming more than set constants and tuples
    /// outside a primitive's and a function's reading.
    func unbuilt(_ phi: NodeID, _ t: inout Table) throws -> Bool {
        if let (_, d, args) = predicate(phi, t) { return try unbuilt(try beta(d.definiens, args, in: &t), &t) }
        if try primitive(phi, t) != nil || (try function(phi, t)) != nil { return false }
        if Reify().names(Pattern(t[phi], in: t)) {
            var naming = Naming()
            _ = try naming.atom(t[phi], in: &t)
            return naming.pieces.contains { piece in
                switch piece {
                case .setConstant, .tuple: false
                case .constantClass, .lambdaClass, .value, .applied, .truthSet: true
                }
            }
        }
        var found = false
        for c in children(t[phi]) where !found && t.type(of: c) == .o {
            found = try unbuilt(c, &t)
        }
        return found
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
        return try words(chain, try chain.predicate(.base("elem"), [.outer(x), u], in: &t), &t)
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

    /// `x ∈ c(…)` named, against NBG's words for it: forward the naming's pieces opened by their existence and the
    /// naming instantiated there; back the naming's pieces fixed, their value the words' by UNIQ.
    private func primitiveProof(
        _ element: NodeID,
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
        var ks = [Int]()
        var hks = [Int]()
        for lambda in classes(a) {
            let (K, hK) = try fw.open(try classExists(try fw.scope.lift(lambda, from: s.depth, in: &t), &t), in: &t)
            ks.append(K)
            hks.append(hK)
        }
        let (c, hc) = try fw.open(try at.classExists(ks, fw, &t), in: &t)
        let (tw, ht) = try fw.open(try at.tupleExists(fw, &t), in: &t)
        let total = ConstantFact(constant: a.constant, type: a.type, fact: .totality)
        let guards = try zip(zip(ks, hks), zip(classes(a), a.type.domains.filter { $0 != .i })).compactMap {
            k, lambda -> NodeID? in
            guard isFunctionClass(lambda.1) else { return nil }
            let at = try fw.scope.lift(lambda.0, from: s.depth, in: &t)
            let fact = try functionFact(at, mode: .statement, base, &t)
            let K = try fw.variable(k.0, in: &t)
            return try t.intern(.folImpliesElim(try t.intern(.folForallElim(fact, K)), try fw.hypothesis(k.1, in: &t)))
        }
        let (r, hr) = try fw.open(
            try eliminated(
                try eliminated(
                    try eliminated(
                        try cited(total, try statement(total, in: &t), &t),
                        at: try ks.map { try fw.variable($0, in: &t) },
                        premises: guards,
                        in: &t,
                    ),
                    at: [try fw.variable(c, in: &t)],
                    premises: [try fw.hypothesis(hc, in: &t)],
                    in: &t,
                ),
                at: try (at.sets + [tw]).map { try fw.variable($0, in: &t) },
                premises: [try fw.hypothesis(ht, in: &t)],
                in: &t,
            ),
            in: &t,
        )
        let member = try at.converted(c, ks, hc, tw, ht, value: r, &fw, &t)
        let related = try t.intern(.folIffElimL(member, try fw.hypothesis(hr, in: &t)))
        var core = try fw.hypothesis(hl, in: &t)
        for (v, h) in zip(ks + [c, tw, r], hks + [hc, ht, hr]) {
            core = try eliminated(
                core,
                at: [try fw.variable(v, in: &t)],
                premises: [try fw.hypothesis(h, in: &t)],
                in: &t,
            )
        }
        let forward = try fw.close(
            try closing(
                try fw.scope.lift(w, from: s.depth, in: &t),
                try (ks + [r]).map { try fw.variable($0, in: &t) },
                try hks.map { try fw.hypothesis($0, in: &t) } + [related],
                core,
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
        let inU = try bw.have(try bw.proof(ob.core, in: &t), in: &t)
        let u = ob.witnesses[k]
        let (c2, hc2) = try bw.open(try at.classExists(bks, bw, &t), in: &t)
        let (tw2, ht2) = try bw.open(try at.tupleExists(bw, &t), in: &t)
        let member2 = try at.converted(c2, bks, hc2, tw2, ht2, value: u, &bw, &t)
        let valued = try bw.have(try t.intern(.folIffElimR(member2, try bw.hypothesis(hb, in: &t))), in: &t)
        var rest = try bw.scope.lift(l, from: s.depth, in: &t)
        var restScope = bw.scope
        var named = [Int]()
        var assumed = [Int]()
        for _ in 0..<(k + 3) {
            let (v, h) = try peel(&rest, &restScope, &bw, &t)
            named.append(v)
            assumed.append(h)
        }
        let term = try t.intern(.isaConst(
            a.constant,
            a.type,
            args: try a.args.map { try bw.scope.lift($0, from: s.depth, in: &t) },
        ))
        let equal = try unique(term, (bks + [c2, tw2, u], bhks + [hc2, ht2, valued]), (named, assumed), bw, &t)
        let x = try bw.scope.lift(element, from: s.depth, in: &t)
        let moved = try eliminated(
            try base.cite(.congElemR, in: &t),
            at: [x, try bw.variable(u, in: &t), try bw.variable(named[k + 2], in: &t)],
            premises: [equal],
            in: &t,
        )
        let backward = try bw.close(try t.intern(.folIffElimL(moved, try bw.hypothesis(inU, in: &t))), in: &t)
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
        let core = try atomWords(
            try membership(try chain.here(v, in: &t), try chain.here(.outer(other), in: &t), &t),
            &t,
        )
        return try words(chain, core, &t)
    }

    private func membership(_ x: NodeID, _ y: NodeID, _ t: inout Table) throws -> NodeID {
        try t.intern(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [x, y]))
    }

    /// An atom in NBG's words: its terms' pieces each existential.
    private func atomWords(_ atom: NodeID, _ t: inout Table) throws -> NodeID {
        var naming = Naming()
        let core = try naming.atom(t[atom], in: &t)
        return try words(naming.chain, core, &t)
    }

    /// `x ∈ y` at `s`, its named form proved from its words (`toNamed`) or back.
    private func membershipMoved(_ p: NodeID, _ x: NodeID, _ y: NodeID, toNamed: Bool, _ s: Scope, _ t: inout Table)
        throws -> NodeID
    {
        let atom = try membership(x, y, &t)
        let named = try formula(atom, .statement, in: &t)
        let said = try atomWords(atom, &t)
        if named == said { return p }
        let iff = try piecesProof(atom, named, said, s, &t)
        return try t.intern(toNamed ? .folIffElimR(iff, p) : .folIffElimL(iff, p))
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

    /// `f(y⃗) ∈ w` named, against NBG's words, `∃v. (∀z. z ∈ v ↔ ψ) ∧ v ∈ w`: forward the naming's pieces opened by
    /// their existence, `v` their value; back the naming's pieces fixed, its value `v` by extensionality.
    private func functionProof(
        _ a: Application,
        _ other: NodeID,
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
        let total = ConstantFact(constant: a.constant, type: a.type, fact: .totality)
        let opened = { (f: inout Frame, t: inout Table) throws -> [(Int, Int)] in
            let (c, hc) = try f.open(try at.classExists([], f, &t), in: &t)
            let (tw, ht) = try f.open(try at.tupleExists(f, &t), in: &t)
            let atC = try eliminated(
                try cited(total, try statement(total, in: &t), &t),
                at: [try f.variable(c, in: &t)],
                premises: [try f.hypothesis(hc, in: &t)],
                in: &t,
            )
            let (v, hv) = try f.open(
                try eliminated(
                    atC,
                    at: try (ys + [tw]).map { try f.variable($0, in: &t) },
                    premises: [try f.hypothesis(ht, in: &t)],
                    in: &t,
                ),
                in: &t,
            )
            return [(c, hc), (tw, ht), (v, hv)]
        }

        var fw = Frame(s)
        let hl = fw.assume(l)
        let pieces = try opened(&fw, &t)
        var core = try fw.hypothesis(hl, in: &t)
        for (v, h) in pieces {
            core = try eliminated(
                core,
                at: [try fw.variable(v, in: &t)],
                premises: [try fw.hypothesis(h, in: &t)],
                in: &t,
            )
        }
        let every = try named.members(pieces.map(\.0), pieces.map(\.1), fw, &t)
        let otherHere = try fw.scope.lift(other, from: s.depth, in: &t)
        let said = try membershipMoved(
            core,
            try fw.variable(pieces[2].0, in: &t),
            otherHere,
            toNamed: false,
            fw.scope,
            &t,
        )
        let forward = try fw.close(
            try closing(
                try fw.scope.lift(w, from: s.depth, in: &t),
                [try fw.variable(pieces[2].0, in: &t)],
                [every],
                said,
                in: &t,
            ),
            in: &t,
        )

        var bw = Frame(s)
        let hw = bw.assume(w)
        let ob = try bw.open(chain: .hypothesis(hw), [.set], in: &t)
        let v = ob.witnesses[0]
        let hall = try bw.have(try bw.proof(ob.constraints[0], in: &t), in: &t)
        let inV = try bw.have(try bw.proof(ob.core, in: &t), in: &t)
        var rest = try bw.scope.lift(l, from: s.depth, in: &t)
        var restScope = bw.scope
        var fixed = [(Int, Int)]()
        for _ in 0..<3 { fixed.append(try peel(&rest, &restScope, &bw, &t)) }
        let r = fixed[2].0
        let hall0 = try bw.have(try named.members(fixed.map(\.0), fixed.map(\.1), bw, &t), in: &t)
        var fz = Frame(bw.scope)
        let z = fz.fix(.i)
        let x = try fz.variable(z, in: &t)
        let at0 = try t.intern(.isaAllElim(try fz.hypothesis(hall0, in: &t), x))
        let atV = try t.intern(.isaAllElim(try fz.hypothesis(hall, in: &t), x))
        let (in0, psi) = try sides(at0, t)
        let inv = try sides(atV, t).left
        let flipped = try base.applied(.iffSymm, [inv, psi], [atV], in: &t)
        let agree = try fz.close(try base.applied(.iffTrans, [in0, psi, inv], [at0, flipped], in: &t), in: &t)
        let ext = try eliminated(
            try base.cite(.extensionality, in: &t),
            at: [try bw.variable(r, in: &t), try bw.variable(v, in: &t)],
            in: &t,
        )
        let equal = try base.claimed(
            .eqSymm,
            [try bw.variable(r, in: &t), try bw.variable(v, in: &t)],
            [try t.intern(.folIffElimR(ext, agree))],
            in: &t,
        )
        let otherBack = try bw.scope.lift(other, from: s.depth, in: &t)
        let inNamed = try membershipMoved(
            try bw.hypothesis(inV, in: &t),
            try bw.variable(v, in: &t),
            otherBack,
            toNamed: true,
            bw.scope,
            &t,
        )
        guard let from = t.conclusion(of: inNamed) else { throw TableError.expectedStep(inNamed) }
        let target = try lifted(rest, from: restScope, to: bw.scope, in: &t)
        let vv = try bw.variable(v, in: &t)
        let rv = try bw.variable(r, in: &t)
        let level = bw.scope.depth
        let moved = try Carry { q, wanted, sc, t in
            guard let have = t.conclusion(of: q) else { throw TableError.expectedStep(q) }
            let iff = try congruent(have, wanted, base, { a, b, t in
                guard try sc.lift(vv, from: level, in: &t) == a, try sc.lift(rv, from: level, in: &t) == b else {
                    throw AxiomError.misread(w)
                }
                return try lifted(equal, terms: sc.depth - level, hyps: sc.hyps - bw.scope.hyps, in: &t)
            }, &t)
            return try t.intern(.folIffElimL(iff, q))
        }.proof(inNamed, from: from, to: target, in: bw.scope, &t)
        let backward = try bw.close(moved, in: &t)
        return try t.intern(.folIffIntro(forward, backward))
    }

    /// An atom's naming `∀v. c(v) → …` against NBG's words `∃v. c(v) ∧ …`, its pieces set constants and tuples: each
    /// piece's value opened by its EX one way, met by its UNIQ the other.
    private func piecesProof(
        _ phi: NodeID,
        _ l: NodeID,
        _ w: NodeID,
        _ s: Scope,
        _ t: inout Table,
    ) throws -> NodeID {
        var naming = Naming()
        _ = try naming.atom(t[phi], in: &t)
        let pieces = naming.pieces
        var fw = Frame(s)
        let hl = fw.assume(l)
        var opened = [(Int, Int)]()
        for piece in pieces {
            let witnesses = opened.map(\.0)
            let frame = fw
            let at = { (r: Ref, t: inout Table) throws -> NodeID in try entry(r, witnesses, frame, s, &t) }
            opened.append(try fw.open(try existence(piece, phi, at, &t), in: &t))
        }
        var core = try fw.hypothesis(hl, in: &t)
        for (v, h) in opened {
            core = try eliminated(
                core,
                at: [try fw.variable(v, in: &t)],
                premises: [try fw.hypothesis(h, in: &t)],
                in: &t,
            )
        }
        let forward = try fw.close(
            try closing(
                try fw.scope.lift(w, from: s.depth, in: &t),
                try opened.map { try fw.variable($0.0, in: &t) },
                try opened.map { try fw.hypothesis($0.1, in: &t) },
                core,
                in: &t,
            ),
            in: &t,
        )

        var bw = Frame(s)
        let hw = bw.assume(w)
        let o = try bw.open(chain: .hypothesis(hw), pieces.map { _ in .set }, in: &t)
        let facts = try o.constraints.map { try bw.have(try bw.proof($0, in: &t), in: &t) }
        let held = try bw.have(try bw.proof(o.core, in: &t), in: &t)
        var rest = try bw.scope.lift(l, from: s.depth, in: &t)
        var restScope = bw.scope
        var fixed = [(Int, Int)]()
        for _ in pieces { fixed.append(try peel(&rest, &restScope, &bw, &t)) }
        var equal = [(NodeID, NodeID, NodeID)]()
        for (j, piece) in pieces.enumerated() {
            let v = try bw.variable(o.witnesses[j], in: &t)
            let v2 = try bw.variable(fixed[j].0, in: &t)
            let ends = [try bw.hypothesis(facts[j], in: &t), try bw.hypothesis(fixed[j].1, in: &t)]
            let p: NodeID
            switch piece {
            case .setConstant(let c):
                p = try eliminated(try setConstantUniqueness(c, &t), at: [v, v2], premises: ends, in: &t)

            case .tuple(let refs):
                let frame = bw
                let words = try refs.map { try entry($0, o.witnesses, frame, s, &t) }
                let named = try refs.map { try entry($0, fixed.map(\.0), frame, s, &t) }
                let same = try refs.indices.map { k -> NodeID in
                    if case .bound(let m) = refs[k] { return equal[m].2 }
                    return try eliminated(try base.cite(.eqRefl, in: &t), at: [words[k]], in: &t)
                }
                let f = TupleFact(arity: refs.count, fact: .uniqueness)
                let unique = try eliminated(
                    try cited(f, try Lowering.statement(f, in: &t), &t),
                    at: words + named,
                    premises: same,
                    in: &t,
                )
                p = try eliminated(unique, at: [v, v2], premises: ends, in: &t)

            case .constantClass, .lambdaClass, .value, .applied, .truthSet:
                throw AxiomError.noReading(phi)
            }
            equal.append((v, v2, p))
        }
        let have = try bw.hypothesis(held, in: &t)
        guard let from = t.conclusion(of: have) else { throw TableError.expectedStep(have) }
        let target = try lifted(rest, from: restScope, to: bw.scope, in: &t)
        let moved = try congruent(from, target, base, { a, b, _ in
            guard let (_, _, p) = equal.first(where: { $0.0 == a && $0.1 == b }) else { throw AxiomError.misread(phi) }
            return p
        }, &t)
        let backward = try bw.close(try t.intern(.folIffElimL(moved, have)), in: &t)
        return try t.intern(.folIffIntro(forward, backward))
    }

    /// A piece's EX, its entries `at` the opened values: `∃v. c(v)` for a set constant, `∃τ. tuple(x⃗, τ)` for a tuple.
    private func existence(
        _ piece: NamedPiece,
        _ phi: NodeID,
        _ at: (Ref, inout Table) throws -> NodeID,
        _ t: inout Table,
    ) throws -> NodeID {
        switch piece {
        case .setConstant(let c):
            return try setConstantExistence(c, base, &t)

        case .tuple(let refs):
            let f = TupleFact(arity: refs.count, fact: .existence)
            return try eliminated(
                try cited(f, try Lowering.statement(f, in: &t), &t),
                at: try refs.map { try at($0, &t) },
                in: &t,
            )

        case .constantClass, .lambdaClass, .value, .applied, .truthSet:
            throw AxiomError.noReading(phi)
        }
    }

    /// A tuple's entry in `f`: an earlier piece's value among `values`, or a variable of the atom at `s`.
    private func entry(_ r: Ref, _ values: [Int], _ f: Frame, _ s: Scope, _ t: inout Table) throws -> NodeID {
        switch r {
        case .bound(let k): try f.variable(values[k], in: &t)
        case .outer(let x): try f.scope.lift(x, from: s.depth, in: &t)
        }
    }

    private func setConstantUniqueness(_ c: Constant, _ t: inout Table) throws -> NodeID {
        switch c {
        case .primitive(.zf(.zero)): return try base.cite(.zfZeroUNIQ, in: &t)

        case .primitive(.zf(.inf)): return try base.cite(.zfInfUNIQ, in: &t)

        case .defined:
            let f = ConstantFact(constant: c, type: .i, fact: .uniqueness)
            return try cited(f, try Lowering.statement(f, in: &t), &t)

        case .primitive(.zf(.mem)), .primitive(.zf(.pow)), .primitive(.zf(.union)), .primitive(.zf(.primReplace)),
             .primitive(.pure), .primitive(.ifol):
            throw AxiomError.noReading(try t.intern(.isaConst(c, .i, args: [])))
        }
    }

    /// CLASS ⟨λ⟩ at the λ's free variables: `∃K. def(λ, K)`.
    private func classExists(_ lambda: NodeID, _ t: inout Table) throws -> NodeID {
        let (f, c) = try lambdaFact(lambda, .classExists, in: &t)
        return try instantiated(
            try cited(f, try Lowering.statement(f, base: base, in: &t), &t),
            at: try c.variables.map { try formula($0, .statement, in: &t) },
            c.types,
            guards: false,
            guardOf: isaGuard,
            in: &t,
        )
    }

    /// `eq(v, v′)`: UNIQ ⟨term⟩ at two sets of its pieces, each its constraints' hypotheses.
    private func unique(
        _ term: NodeID,
        _ one: ([Int], [Int]),
        _ two: ([Int], [Int]),
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let c = try closed(term, in: &t)
        let u = try uniqueness(of: term, in: &t)
        var p = try instantiated(
            try cited(u, try Lowering.statement(u, in: &t), &t),
            at: c.variables,
            c.types,
            guards: true,
            guardOf: isaGuard,
            in: &t,
        )
        for (x, h) in zip(one.0 + two.0, one.1 + two.1) {
            p = try eliminated(p, at: [try f.variable(x, in: &t)], premises: [try f.hypothesis(h, in: &t)], in: &t)
        }
        return p
    }

    /// The next binder of `rest`, a universal naming at `scope`, fixed in `f` and its constraint assumed.
    private func peel(_ rest: inout NodeID, _ scope: inout Scope, _ f: inout Frame, _ t: inout Table) throws
        -> (Int, Int)
    {
        let here = try lifted(rest, from: scope, to: f.scope, in: &t)
        let body: NodeID
        let set: Bool
        switch t[here] {
        case .ifolAll(.i, let b): (body, set) = (b, true)
        case .folForall(let b): (body, set) = (b, false)
        default: throw AxiomError.misread(here)
        }
        let v = f.fix(set ? .i : nil)
        guard case .folImplies(let c, let after) = t[body] else { throw AxiomError.misread(here) }
        let h = f.assume(c)
        rest = after
        scope = f.scope
        return (v, h)
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
         .defined:
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

    /// `∀z. z ∈ r ↔ ψ(z)` at the naming's pieces `named`, `r` their value: the members theorem's naming proved there
    /// by UNIQ one way, instantiated there the other.
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
        var fn = Frame(fa.scope)
        var rest = naming
        var restScope = fz.scope
        var fixed = [Int]()
        var assumed = [Int]()
        for _ in 0..<3 {
            let here = try lifted(rest, from: restScope, to: fn.scope, in: &t)
            let body: NodeID
            let set: Bool
            switch t[here] {
            case .ifolAll(.i, let b): (body, set) = (b, true)
            case .folForall(let b): (body, set) = (b, false)
            default: throw AxiomError.misread(here)
            }
            fixed.append(fn.fix(set ? .i : nil))
            guard case .folImplies(let c, let after) = t[body] else { throw AxiomError.misread(here) }
            assumed.append(fn.assume(c))
            rest = after
            restScope = fn.scope
        }
        let equal = try same(named, hs, fixed, assumed, fn, &t)
        let moved = try eliminated(
            try base.cite(.congElemR, in: &t),
            at: [try fn.variable(z, in: &t), try fn.variable(named[2], in: &t), try fn.variable(fixed[2], in: &t)],
            premises: [equal],
            in: &t,
        )
        let proved = try fn.close(try t.intern(.folIffElimL(moved, try fn.hypothesis(hz, in: &t))), in: &t)
        let left = try t.intern(.folAndElimL(try lifted(th, from: fz.scope, to: fa.scope, in: &t)))
        let into1 = try fa.close(try t.intern(.folImpliesElim(left, proved)), in: &t)

        var fb = Frame(fz.scope)
        let hp = fb.assume(psi)
        var back = try t.intern(.folImpliesElim(
            try t.intern(.folAndElimR(try lifted(th, from: fz.scope, to: fb.scope, in: &t))),
            try fb.hypothesis(hp, in: &t),
        ))
        for (x, h) in zip(named, hs) {
            back = try eliminated(
                back,
                at: [try fb.variable(x, in: &t)],
                premises: [try fb.hypothesis(h, in: &t)],
                in: &t,
            )
        }
        return try fz.close(try t.intern(.folIffIntro(into1, try fb.close(back, in: &t))), in: &t)
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

/// NBG's words for a chain: each binder existential, its constraint conjoined — base's vocabulary, never S1's naming.
private func words(_ chain: Chain, _ core: NodeID, _ t: inout Table) throws -> NodeID {
    let constraints = try chain.stated()
    var body = core
    for k in chain.binders.indices.reversed() {
        let both = try t.intern(.folAnd(constraints[k], body))
        body = try t.intern(chain.binders[k] == .set ? .ifolEx(.i, body: both) : .folExists(body: both))
    }
    return body
}
