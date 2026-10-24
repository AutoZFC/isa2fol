import IR

@frozen
public enum LetterError: Error, Equatable, Sendable {
    case notALetter(IRType)
    case notAnInstance(NodeID)
}

/// The lift of the letter bound at index 0, of type `T`: for every bundle `A⃗` of its class arguments, a class `U` of
/// the records `a ++ [τ]` at which it holds, `τ` the tuple of its set arguments, each class argument `A`'s section at
/// `a` — a class-taking constant's lift, the letter's atom where the constant's class stood (FOUNDATION S4, §3).
func letterLift(_ T: IRType, in t: inout Table) throws -> NodeID {
    guard let n = letterArity(T), n > 0 else { throw LetterError.notALetter(T) }
    let domains = T.domains
    let classes = domains.filter { $0 != .i }
    var s = Scope()
    let letter = s.fix(nil)
    let p = s.fix(.i)
    let p1 = s.fix(.i)
    let outer = s
    let As = classes.map { _ in s.fix(nil) }
    let U = s.fix(nil)
    let a = s.fix(.i)
    let atA = s
    let Ks = classes.map { s.fix($0) }
    let atK = s
    let ys = domains.filter { $0 == .i }.map { _ in s.fix(.i) }
    let tau = s.fix(.i)
    let atTau = s
    var k = 0
    var y = 0
    let args = try domains.map { D -> NodeID in
        if D == .i {
            defer { y += 1 }
            return try atTau.variable(ys[y], in: &t)
        }
        defer { k += 1 }
        return try atTau.variable(Ks[k], in: &t)
    }
    let atom = try t.intern(.folLetter(head: try atTau.variable(letter, in: &t), args: args))
    var inB = atTau
    let b = inB.fix(.i)
    let member = try t.intern(.ifolEx(.i, body: try t.intern(.folAnd(
        try pred("snoc", [a, p, tau, b], at: inB, &t),
        try pred("elem", [b, U], at: inB, &t),
    ))))
    var body = try t.intern(.folImplies(
        try tuple(try ys.map { try atTau.variable($0, in: &t) }, try atTau.variable(tau, in: &t), in: &t),
        try t.intern(.folIff(atom, member)),
    ))
    for _ in 0...ys.count { body = try t.intern(.ifolAll(.i, body: body)) }
    for j in classes.indices.reversed() {
        let section = try approximation(
            Ks[j],
            As[j],
            record: a,
            p,
            p1,
            function: isFunctionClass(classes[j]),
            in: atK,
            &t,
        )
        body = try t.intern(.folImplies(section, body))
    }
    for _ in Ks { body = try t.intern(.folForall(body: body)) }
    body = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(try pred("tuple", [a, p], at: atA, &t), body))))
    body = try t.intern(.folExists(body: body))
    for _ in As { body = try t.intern(.folForall(body: body)) }
    body = try t.intern(.folImplies(try pred("nsucc", [p, p1], at: outer, &t), body))
    return try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: body))))
}

/// The letter's lift at `x`, a letter variable or its λ instance.
func lift(at x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
    try instantiate(try letterLift(T, in: &t), with: x, in: &t)
}

/// `x` as a letter's instance: its λ instance as it stands, a letter variable's η, `\b⃗. x(b⃗)`.
func letterInstance(_ x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
    if case .folLetterAbs = t[x] { return x }
    guard let n = letterArity(T), n > 0 else { throw LetterError.notALetter(T) }
    let k: Int
    if case .isaBound(let j, _) = t[x] {
        k = j
    } else if case .folBound(let j) = t[x] {
        k = j
    } else {
        throw LetterError.notAnInstance(x)
    }
    let args = try (0..<n).map { try t.intern(.folBound(n - 1 - $0)) }
    var instance = try t.intern(.folLetter(head: try t.intern(.folBound(k + n)), args: args))
    for _ in 0..<n { instance = try t.intern(.folLetterAbs(body: instance)) }
    return instance
}

/// The letter's λ, `λx⃗. φ`, as its instance: `\b⃗. φ`'s formula, at a proof's site holding the values of the terms
/// free of `x⃗`.
func letterAbstraction(_ lambda: NodeID, _ T: IRType, mode: Mode? = nil, in t: inout Table) throws -> NodeID {
    guard let n = letterArity(T), n > 0 else { throw LetterError.notALetter(T) }
    var body = lambda
    for _ in 0..<n {
        guard case .isaAbs(_, let b) = t[body] else { throw LetterError.notAnInstance(lambda) }
        body = b
    }
    var instance = try formula(body, mode ?? .proof(n), in: &t)
    for _ in 0..<n { instance = try t.intern(.folLetterAbs(body: instance)) }
    return instance
}

/// The letter bound at `k` if `lambda` is its η, `λx⃗. P(x⃗)`, each argument the η of its own variable.
func etaLetter(_ lambda: NodeID, _ T: IRType, in t: Table) -> Int? {
    guard let n = letterArity(T), n > 0 else { return nil }
    var body = lambda
    for _ in 0..<n {
        guard case .isaAbs(_, let b) = t[body] else { return nil }
        body = b
    }
    guard
        case .isaVarApp(let h, let args) = t[body], case .isaBound(let j, let U) = t[h], U == T, j >= n,
        args.count == n
    else { return nil }
    for (m, x) in args.enumerated() where eta(x, n - 1 - m, t) == false { return nil }
    return j - n
}

/// `x` is the variable bound at `k`, η-long: `K`, or `λz⃗. K(z⃗)`.
private func eta(_ x: NodeID, _ k: Int, _ t: Table) -> Bool {
    var body = x
    var m = 0
    while case .isaAbs(_, let b) = t[body] { (body, m) = (b, m + 1) }
    if m == 0 {
        if case .isaBound(k, _) = t[x] { return true }
        return false
    }
    guard case .isaVarApp(let h, let args) = t[body], case .isaBound(k + m, _) = t[h], args.count == m else {
        return false
    }
    return args.enumerated().allSatisfy { j, a in
        if case .isaBound(m - 1 - j, _) = t[a] { true } else { false }
    }
}

/// `LIFT ⟨λ⟩` at a proof's site, `λ` holding its fixed terms' values: the lift of its skeleton, cited at them.
func liftFact(_ lambda: NodeID, _: IRType, in t: inout Table) throws -> NodeID {
    let s = try skeleton(lambda, { x, d, t in isValued(x, t) && Mode.proof(0).deeper(d).valued(x, in: t) }, in: &t)
    let (f, c) = try lambdaFact(s.formula, .lift, in: &t)
    let at = try c.variables.map { x -> NodeID in
        guard case .isaBound(let k, _) = t[x], k >= s.width else { return try formula(x, .proof(0), in: &t) }
        return try valueNode(s.params[k - s.width], in: &t)
    }
    return try instantiated(try cited(f, try liftStatement(f, in: &t), &t), at: at, c.types, guards: true, guardOf: {
        x, U, t in try letterGuard(x, U, in: &t)
    }, in: &t)
}

/// A letter's guard at `x`, a letter variable or a λ at its type: the citer's own lift at its own letter, the λ's
/// `LIFT ⟨λ⟩` at any other; any other type's guard as `isaGuard` gives it.
func letterGuard(_ x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
    guard let n = letterArity(T), n > 0, case .isaAbs = t[x] else { return try isaGuard(x, T, &t) }
    if let k = etaLetter(x, T, in: t) { return try isaGuard(try t.intern(.isaBound(k, T)), T, &t) }
    return try liftFact(x, T, in: &t)
}

/// A letter's instance at `x`, a letter variable or a λ at its type.
func instanceAt(_ x: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
    guard case .isaAbs = t[x] else { return try letterInstance(x, T, in: &t) }
    if let k = etaLetter(x, T, in: t) { return try letterInstance(try t.intern(.isaBound(k, T)), T, in: &t) }
    return try letterAbstraction(x, T, in: &t)
}

/// `∀K⃗ y⃗. A(K⃗, y⃗) ↔ φ(K⃗, y⃗)`: the letter bound at `k` defined by its λ, `φ` the body as the λ's instance holds it.
func letterDefinition(_ k: Int, _ lambda: NodeID, _ T: IRType, in t: inout Table) throws -> NodeID {
    guard let n = letterArity(T), n > 0 else { throw LetterError.notALetter(T) }
    let ds = T.domains
    let args = try ds.indices.map { j in try t.intern(ds[j] == .i ? .isaBound(n - 1 - j, .i) : .folBound(n - 1 - j)) }
    var body = try shift(try letterAbstraction(lambda, T, in: &t), by: n, in: &t)
    for a in args {
        guard case .folLetterAbs(let b) = t[body] else { throw LetterError.notAnInstance(lambda) }
        body = try instantiate(b, with: a, in: &t)
    }
    var definition = try t.intern(.folIff(
        try t.intern(.folLetter(head: try t.intern(.folBound(k + n)), args: args)),
        body,
    ))
    for D in ds.reversed() { definition = try t.intern(D == .i
            ? .ifolAll(.i, body: definition)
            : .folForall(
                body: definition
            )) }
    return definition
}

/// `BETA_<fp>_L`: a cited formula's S1 form at its letters against its form at the λs of `instances` holding their
/// values, premised on each such letter's definition — Lambda's β, a letter for the class variable. `instances` pairs
/// a letter's position in `types` with its λ, both at the lemma's root.
struct LetterInstantiation: Request {
    struct Instance: Hashable {
        let position: Int
        let lambda: NodeID
    }

    let formula: NodeID
    let instances: [Instance]
    let types: [IRType]
    let name: String

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> LetterInstantiation {
        LetterInstantiation(
            formula: try f(formula),
            instances: try instances.map { Instance(position: $0.position, lambda: try f($0.lambda)) },
            types: types,
            name: name,
        )
    }

    /// The letter's loose index at the lemma's root.
    func index(_ i: Instance) -> Int {
        types.count - 1 - i.position
    }

    func reduced(_ psi: NodeID, _ t: inout Table) throws -> NodeID {
        var x = psi
        for i in instances { x = try instantiate(try abstractIndex(x, index(i), in: &t), with: i.lambda, in: &t) }
        return x
    }
}

func statement(_ m: LetterInstantiation, in t: inout Table) throws -> NodeID {
    let named = try formula(m.formula, .statement, in: &t)
    let valued = try formula(try m.reduced(m.formula, &t), .proof(0), in: &t)
    let crossing = try ordered(try values(in: valued, &t), &t)
    var body = try fixing(crossing, in: try t.intern(.folImplies(named, valued)), by: .premise, in: &t)
    for i in m.instances.reversed() {
        body = try t.intern(.folImplies(try letterDefinition(m.index(i), i.lambda, m.types[i.position], in: &t), body))
    }
    return try universal(m.types, guards: true, body, in: &t)
}

/// A letter's congruence at one argument, `x = y → (A(…x…) ↔ A(…y…))`, a set's or a class's: its lift read twice at
/// one tuple, each class argument through its section at the empty record.
struct LetterFact: Request {
    let type: IRType
    let position: Int

    var name: String {
        let code = type.domains.map { D in D == .i ? "s" : (result(D) == .i ? "f" : "p") + String(D.domains.count) }
        return "LETTER_CONG_\(code.joined())_\(position)"
    }

    func remapped(_: (NodeID) throws -> NodeID) rethrows -> LetterFact {
        self
    }
}

func statement(_ f: LetterFact, in t: inout Table) throws -> NodeID {
    let ds = f.type.domains
    let n = ds.count
    let variable = { (D: IRType, k: Int, t: inout Table) throws -> NodeID in
        try t.intern(D == .i ? .isaBound(k, .i) : .folBound(k))
    }
    let zs = try ds.indices.map { try variable(ds[$0], n - $0, &t) }
    let w = try variable(ds[f.position], 0, &t)
    var ws = zs
    ws[f.position] = w
    let head = try t.intern(.folBound(n + 1))
    var body = try t.intern(.folImplies(
        try t.intern(.folPred(.base("eq"), args: [zs[f.position], w])),
        try t.intern(.folIff(
            try t.intern(.folLetter(head: head, args: zs)),
            try t.intern(.folLetter(head: head, args: ws)),
        )),
    ))
    for D in [ds[f.position]] + ds.reversed() {
        body = try t.intern(D == .i ? .ifolAll(.i, body: body) : .folForall(body: body))
    }
    return try universal([f.type], guards: true, body, in: &t)
}

extension ClassProofs {
    /// `LIFT ⟨λ⟩`: `c_LIFT`'s construction at the λ's body over its set parameters, its class parameters the bundles'
    /// sections at the record, the λ's sets the records' context; the body at `y⃗` read as its class `C` at `⟨y⃗⟩` by
    /// `CLASS` and `ARGS` of that λ.
    func instanceLift(_ f: LambdaFact, _ t: inout Table) throws -> NodeID {
        guard let T = t.type(of: f.lambda), let n = letterArity(T), n > 0 else { throw ClassError.unexpected(f.name) }
        let ds = T.domains
        let classes = Array(ds.prefix { $0 != .i })
        guard ds.dropFirst(classes.count).allSatisfy({ $0 == .i }) else { throw ClassError.unexpected(f.name) }
        var top = Frame()
        var roles = [Role]()
        var context = [Int]()
        var guards = [Int: Int]()
        for U in f.types {
            let v = try top.fixClosure(U, in: &t)
            if U == .i {
                roles.append(.entry(context.count))
                context.append(v)
                continue
            }
            roles.append(.fixed(v))
            if U != .o, letterArity(U) == nil, let g = try guarded(try top.variable(v, in: &t), U, in: &t) {
                guards[v] = top.assume(g)
            }
        }
        let root = top.scope
        let c = context.count
        let p = top.fix(.i)
        let p1 = top.fix(.i)
        let hn = top.assume(try pred("nsucc", [p, p1], at: top.scope, &t))
        let As = classes.map { _ in top.fix(nil) }
        var g = try Comprehension(base: base, top: top, in: &t)
        _ = try g.numeral(c + 4, &t)
        let sections = classes.indices.map { g.classParameter(
            As[$0],
            function: isFunctionClass(classes[$0]),
            record: c + 2,
            index: c,
            next: c + 1,
        ) }
        var open = f.lambda
        for _ in classes {
            guard case .isaAbs(_, let b) = t[open] else { throw ClassError.unexpected(f.name) }
            open = b
        }
        let raw = try classBody(open, raw: true, in: &t)
        let W = try g.build(.body(raw), roles + sections.map { .section($0) } + [.entry(c + 3)], c + 4, &t)
        let rekey = RekeyFact(width: 1, context: c)
        let at = try eliminated(
            try cited(rekey, try statement(rekey, in: &t), &t),
            at: try (context + [p, p1]).map { try g.top.variable($0, in: &t) },
            premises: [try g.top.hypothesis(hn, in: &t)],
            in: &t,
        )
        let (U, hU) = try g.top.open(try eliminated(at, at: [try g.top.variable(W.cls, in: &t)], in: &t), in: &t)
        let reading = g.reading
        var M = Frame(g.top.scope)
        let a = M.fix(.i)
        let ht = M.assume(try pred("tuple", [a, p], at: M.scope, &t))
        let Ks = classes.map { M.fix($0) }
        var env = Env()
        for j in classes.indices {
            let section = try approximation(
                Ks[j],
                As[j],
                record: a,
                p,
                p1,
                function: isFunctionClass(classes[j]),
                in: M.scope,
                &t,
            )
            env.sections[sections[j]] = M.assume(section)
        }
        let lambda = try beta(
            try lifted(f.lambda, from: root, to: M.scope, in: &t),
            try Ks.map { try M.variable($0, in: &t) },
            in: &t,
        )
        let atLambda = M.scope
        let (C, hC) = try M.open(try classExistence(lambda, .statement, base, &t), in: &t)
        var E = Frame(M.scope)
        let ys = (0..<(n - classes.count)).map { _ in E.fix(.i) }
        let tau = E.fix(.i)
        let htau = E.assume(try tuple(try ys.map { try E.variable($0, in: &t) }, try E.variable(tau, in: &t), in: &t))
        let rho = try reading.record(context + [p, p1, a, tau], in: &E, &t)
        let graph = try t.intern(.isaAllElim(try E.hypothesis(hC, in: &t), try E.variable(tau, in: &t)))
        let exact = try reading.read(try sides(graph, t).right, W, E, rho, env, &t)
        let keyed = try records(rho, W.cls, reading, E, &t)
        let moved = try rekeyed(hU, a, ht, [tau], U, p, p1, E, &t)
        let back = try base.applied(.iffSymm, [try sides(exact, t).left, try sides(exact, t).right], [exact], in: &t)
        let inC = try chained(try chained(try chained(graph, back, &t), keyed, &t), moved, &t)
        let frame = E
        let guardOf = { (x: NodeID, V: IRType, t: inout Table) throws -> NodeID in
            for (v, h) in guards where try frame.variable(v, in: &t) == x { return try frame.hypothesis(h, in: &t) }
            return try isaGuard(x, V, &t)
        }
        let closure = try closed(try lifted(lambda, from: atLambda, to: E.scope, in: &t), in: &t)
        let request = Arguments(
            lambda: closure.term,
            types: closure.types,
            name: "ARGS_" + fingerprint(closure.term, t),
        )
        var args = try instantiated(
            try cited(request, try statement(request, base: base, in: &t), &t),
            at: closure.variables,
            closure.types,
            guards: true,
            guardOf: guardOf,
            in: &t,
        )
        args = try t.intern(.folImpliesElim(
            try t.intern(.folForallElim(args, try E.variable(C, in: &t))),
            try E.hypothesis(hC, in: &t),
        ))
        for y in ys { args = try t.intern(.isaAllElim(args, try E.variable(y, in: &t))) }
        let (named, phi) = try sides(args, t)
        let atTau = try atTuple(named, ys, tau, htau, C, E, &t)
        let body = try base.applied(.iffSymm, [named, phi], [args], in: &t)
        let lifted = try chained(try chained(body, atTau, &t), inC, &t)
        let each = try M.close(try E.close(lifted, in: &t), in: &t)
        return try g.top.close(try t.intern(.folExistsIntro(each, try g.top.variable(U, in: &t))), in: &t)
    }

    func letterCongruence(_ f: LetterFact, _ t: inout Table) throws -> NodeID {
        let ds = f.type.domains
        guard ds.allSatisfy({ $0 == .i || result($0) == .o }) else { throw ClassError.unexpected(f.name) }
        var top = Frame()
        let letter = try top.fixClosure(f.type, in: &t)
        guard let lift = top.lifts[letter] else { throw ClassError.unexpected(f.name) }
        let zs = ds.map { top.fix($0 == .i ? .i : nil) }
        let w = top.fix(ds[f.position] == .i ? .i : nil)
        let he = top.assume(try pred("eq", [zs[f.position], w], at: top.scope, &t))
        var g = try Comprehension(base: base, top: top, in: &t)
        let n1 = try g.numeral(1, &t)
        let reading = g.reading
        guard let empty = reading.empty else { throw ClassError.unexpected(f.name) }
        let n0 = empty.variable
        var bundles = [Int: Built]()
        for j in ds.indices where ds[j] != .i {
            let d = g.top.scope.depth
            let member = try t.intern(.folPred(
                .base("elem"),
                args: [try t.intern(.isaBound(0, .i)), try t.intern(.folBound(d - zs[j]))],
            ))
            bundles[j] = try g.build(member, (0..<d).map { Role.fixed($0) } + [.entry(0)], 1, &t)
        }
        var approximations = [(cls: Int, at: Int, alike: Int?)]()
        for j in ds.indices where ds[j] != .i {
            guard let A = bundles[j] else { throw ClassError.unexpected(f.name) }
            let at = try g.top.have(try sectioned(zs[j], A, empty, n0, n1, reading, g.top, &t), in: &t)
            guard j == f.position else {
                approximations.append((A.cls, at, nil))
                continue
            }
            let alike = try sectionedAlike(zs[j], w, he, try g.top.hypothesis(at, in: &t), g.top, &t)
            approximations.append((A.cls, at, try g.top.have(alike, in: &t)))
        }
        var p = try eliminated(
            try g.top.hypothesis(lift, in: &t),
            at: [try g.top.variable(n0, in: &t), try g.top.variable(n1, in: &t)],
            premises: [try g.top.hypothesis(try reading.numerals.successor(0), in: &t)],
            in: &t,
        )
        p = try eliminated(p, at: try approximations.map { try g.top.variable($0.cls, in: &t) }, in: &t)
        let (_, hU) = try g.top.open(p, in: &t)
        let sets = ds.indices.filter { ds[$0] == .i }
        let xs = try sets.map { try g.top.variable(zs[$0], in: &t) }
        let existence = TupleFact(arity: sets.count, fact: .existence)
        let (tau, ht) = try g.top.open(
            try eliminated(try cited(existence, try statement(existence, in: &t), &t), at: xs, in: &t),
            in: &t,
        )
        let read = { (args: [Int], tupled: NodeID, swapped: Bool, t: inout Table) throws -> NodeID in
            var q = try t.intern(.isaAllElim(try g.top.hypothesis(hU, in: &t), try g.top.variable(n0, in: &t)))
            q = try t.intern(.folImpliesElim(q, try g.top.proof(empty.tuple, in: &t)))
            let classes = try ds.indices.filter { ds[$0] != .i }.map { try g.top.variable(args[$0], in: &t) }
            let sections = try approximations.map { a -> NodeID in
                try g.top.hypothesis(swapped ? a.alike ?? a.at : a.at, in: &t)
            }
            q = try eliminated(q, at: classes, premises: sections, in: &t)
            let ys = try sets.map { try g.top.variable(args[$0], in: &t) }
            return try eliminated(q, at: ys + [try g.top.variable(tau, in: &t)], premises: [tupled], in: &t)
        }
        var ws = zs
        ws[f.position] = w
        let before = try read(zs, try g.top.hypothesis(ht, in: &t), false, &t)
        let afterTuple: NodeID
        if ds[f.position] == .i {
            let ys = try sets.map { try g.top.variable(ws[$0], in: &t) }
            let congruence = TupleFact(arity: sets.count, fact: .congruence)
            let equalities = try sets.map { j -> NodeID in
                if j == f.position { return try g.top.hypothesis(he, in: &t) }
                return try base.claimed(.eqRefl, [try g.top.variable(zs[j], in: &t)], [], in: &t)
            }
            let here = try sets.map { try g.top.variable(zs[$0], in: &t) }
            let moved = try eliminated(
                try cited(congruence, try statement(congruence, in: &t), &t),
                at: here + ys,
                premises: equalities,
                in: &t,
            )
            afterTuple = try eliminated(
                moved,
                at: [try g.top.variable(tau, in: &t)],
                premises: [try g.top.hypothesis(ht, in: &t)],
                in: &t,
            )
        } else {
            afterTuple = try g.top.hypothesis(ht, in: &t)
        }
        let after = try read(ws, afterTuple, true, &t)
        let a = try sides(before, t).left
        let m = try sides(before, t).right
        let b = try sides(after, t).left
        let back = try base.applied(.iffSymm, [b, m], [after], in: &t)
        return try g.top.close(try base.applied(.iffTrans, [a, m, b], [before, back], in: &t), in: &t)
    }

    /// `(∀τ′. ⟦τ′ = ⟨y⃗⟩⟧ → τ′ ∈ C) ↔ τ ∈ C`, `ht` the hypothesis `⟦τ = ⟨y⃗⟩⟧`: the tuple's uniqueness.
    private func atTuple(
        _ named: NodeID,
        _ ys: [Int],
        _ tau: Int,
        _ ht: Int,
        _ C: Int,
        _ f: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var forward = Frame(f.scope)
        let hn = forward.assume(named)
        let there = try t.intern(.folImpliesElim(
            try t.intern(.isaAllElim(try forward.hypothesis(hn, in: &t), try forward.variable(tau, in: &t))),
            try forward.hypothesis(ht, in: &t),
        ))
        var backward = Frame(f.scope)
        let hm = backward.assume(try pred("elem", [tau, C], at: backward.scope, &t))
        let other = backward.fix(.i)
        let ho = backward.assume(try tuple(
            try ys.map { try backward.variable($0, in: &t) },
            try backward.variable(other, in: &t),
            in: &t,
        ))
        let entries = try ys.map { try backward.variable($0, in: &t) }
        let uniq = TupleFact(arity: ys.count, fact: .uniqueness)
        let same = try eliminated(
            try eliminated(
                try cited(uniq, try statement(uniq, in: &t), &t),
                at: entries + entries,
                premises: try entries.map { try eliminated(try base.cite(.eqRefl, in: &t), at: [$0], in: &t) },
                in: &t,
            ),
            at: [try backward.variable(tau, in: &t), try backward.variable(other, in: &t)],
            premises: [try backward.hypothesis(ht, in: &t), try backward.hypothesis(ho, in: &t)],
            in: &t,
        )
        let moved = try eliminated(
            try base.cite(.congElemL, in: &t),
            at: try [tau, other, C].map { try backward.variable($0, in: &t) },
            premises: [same],
            in: &t,
        )
        let member = try t.intern(.folIffElimL(moved, try backward.hypothesis(hm, in: &t)))
        return try t.intern(.folIffIntro(
            try forward.close(there, in: &t),
            try backward.close(member, in: &t),
        ))
    }

    /// `K ≈∅ A`, `A` the class of the records on 1 whose entry is in `K`: `∀u. u ∈ K ↔ ∃b. snoc(∅, 0, u, b) ∧ b ∈ A`.
    private func sectioned(
        _ K: Int,
        _ A: Built,
        _ empty: Record,
        _ n0: Int,
        _ n1: Int,
        _ reading: Reading,
        _ top: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var e = Frame(top.scope)
        let u = e.fix(.i)
        let member = try pred("elem", [u, K], at: e.scope, &t)
        let bound = try approximation(K, A.cls, record: empty.variable, n0, n1, function: false, in: top.scope, &t)
        guard case .ifolAll(.i, let each) = t[bound], case .folIff(_, let some) = t[each] else {
            throw ClassError.unexpected("a section")
        }
        var forward = Frame(e.scope)
        let hu = forward.assume(member)
        let at = try [empty.variable, n0, u].map { try forward.variable($0, in: &t) }
        let (b, hb) = try forward.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
        let rho = try reading.extend(empty, value: u, record: b, snoc: .hypothesis(hb), needs: [], in: &forward, &t)
        let exact = try reading.read(
            try lifted(member, from: e.scope, to: forward.scope, in: &t),
            A,
            forward,
            rho,
            Env(),
            &t,
        )
        let inA = try t.intern(.folIffElimR(exact, try forward.hypothesis(hu, in: &t)))
        let someThere = try lifted(some, from: e.scope, to: forward.scope, in: &t)
        guard case .ifolEx(.i, let shape) = t[someThere] else { throw ClassError.unexpected("a section") }
        let witnessed = try t.intern(.isaExIntro(
            try t.intern(.folAndIntro(try forward.hypothesis(hb, in: &t), inA)),
            try forward.variable(b, in: &t),
            body: shape,
        ))
        var backward = Frame(e.scope)
        let hs = backward.assume(try lifted(some, from: e.scope, to: backward.scope, in: &t))
        let (b2, hb2) = try backward.open(try backward.hypothesis(hs, in: &t), in: &t)
        let rho2 = try reading.extend(
            empty,
            value: u,
            record: b2,
            snoc: .left(.hypothesis(hb2)),
            needs: [],
            in: &backward,
            &t,
        )
        let exact2 = try reading.read(
            try lifted(member, from: e.scope, to: backward.scope, in: &t),
            A,
            backward,
            rho2,
            Env(),
            &t,
        )
        let inK = try t.intern(.folIffElimL(exact2, try backward.proof(.right(.hypothesis(hb2)), in: &t)))
        let iff = try t.intern(.folIffIntro(
            try forward.close(witnessed, in: &t),
            try backward.close(inK, in: &t),
        ))
        return try e.close(iff, in: &t)
    }

    /// `K′ ≈∅ A` from `K ≈∅ A` and `eq(K, K′)`.
    private func sectionedAlike(
        _ K: Int,
        _ K2: Int,
        _ he: Int,
        _ at: NodeID,
        _ top: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        var e = Frame(top.scope)
        let u = e.fix(.i)
        let x = try e.variable(u, in: &t)
        let same = try base.claimed(
            .congElemR,
            [x, try e.variable(K, in: &t), try e.variable(K2, in: &t)],
            [try e.hypothesis(he, in: &t)],
            in: &t,
        )
        let old = try t.intern(.isaAllElim(try lifted(at, from: top.scope, to: e.scope, in: &t), x))
        let l = try sides(same, t).right
        let k = try sides(same, t).left
        let r = try sides(old, t).right
        let back = try base.applied(.iffSymm, [k, l], [same], in: &t)
        return try e.close(try base.applied(.iffTrans, [l, k, r], [back, old], in: &t), in: &t)
    }
}
