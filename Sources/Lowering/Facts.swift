import IR

struct Closed: Hashable {
    let term: NodeID
    let variables: [NodeID]
    let types: [IRType]
}

/// ⚠ A PROPOSITION VARIABLE CLOSES AS A LETTER OF THE LEMMA, AT ITS TOP (S4): left out, a truth-set variable dangles in
/// the statement silently; closed as a `∀`, the table refuses its citation (`propositionAsTerm`).
func closed(_ a: NodeID, in t: inout Table) throws -> Closed {
    let all = freeVariables(a, in: t)
    let frees = all.filter { $0.type == .o } + all.filter { $0.type != .o }
    var term = try transform(a, Lettered(), in: &t)
    for (j, v) in frees.enumerated() { term = try abstractIndex(term, v.index + j, in: &t) }
    return Closed(term: term, variables: try frees.map { try t.intern($0.variable) }, types: frees.map(\.type))
}

func freeVariables(_ x: NodeID, in t: Table) -> [(index: Int, type: IRType, variable: Node)] {
    var found = [(index: Int, type: IRType, variable: Node)]()
    func walk(_ n: NodeID, _ d: Int) {
        guard t.looseBound(of: n) > d else { return }
        switch t[n] {
        case .isaBound(let k, let T):
            if !found.contains(where: { $0.index == k - d }) { found.append((k - d, T, .isaBound(k - d, T))) }
        case .isaPropBound(let k):
            if !found.contains(where: { $0.index == k - d }) { found.append((k - d, .o, .isaPropBound(k - d))) }
        default:
            t[n].forEachChild { c, binds in walk(c, d + binds.terms) }
        }
    }
    walk(x, 0)
    return found
}

private struct Lettered: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard case .isaPropBound(let k) = t[id], k >= depth.terms else { return nil }
        return try t.intern(.isaBound(k, .o))
    }
}

struct Existence: Request {
    let term: NodeID
    let types: [IRType]
    let name: String
}

/// ⚠ A NAMING IS NEVER CLOSED AGAIN AROUND ITS OWN VALUE: `exists_intro` abstracts every occurrence of its witness, so
/// `⟦r = a⟧` closed at `r` concludes `eq(r, r)`. UNIQ takes both namings open, as its consumers hold them.
struct Uniqueness: Request {
    let term: NodeID
    let types: [IRType]
    let name: String
}

struct ConstantFact: Request {
    enum Fact: Hashable, Sendable {
        case existence
        case uniqueness
        case classExists
        case agreement
        case totality
        case function
        case lift
    }

    let constant: Constant
    let type: IRType
    let fact: Fact

    var name: String {
        switch fact {
        case .lift: constant.name + "_LIFT"
        case .existence: constant.name + "_EX"
        case .uniqueness: constant.name + "_UNIQ"
        case .classExists: constant.name + "_CLASS"
        case .agreement: constant.name + "_AGREE"
        case .totality: constant.name + "_TOTAL"
        case .function: constant.name + "_FUNC"
        }
    }
}

struct Unfolding: Request {
    let constant: Defined
    let statement: NodeID

    var name: String {
        constant.name + "_UNFOLD"
    }
}

struct LambdaFact: Request {
    enum Fact: Hashable, Sendable {
        case classExists
        case function
        case arguments
    }

    let lambda: NodeID
    let types: [IRType]
    let fact: Fact
    let name: String

}

struct RekeyFact: Request {
    let width: Int

    var name: String {
        "REKEY_\(width)"
    }
}

struct TupleFact: Request {
    enum Fact: Hashable, Sendable {
        case existence
        case uniqueness
        case injectivity
    }

    let arity: Int
    let fact: Fact

    var name: String {
        switch fact {
        case .existence: "TUPLE_EX_\(arity)"
        case .uniqueness: "TUPLE_UNIQ_\(arity)"
        case .injectivity: "TUPLE_INJ_\(arity)"
        }
    }
}

public func kind(of lemma: Lemma) -> String {
    switch lemma.request {
    case let f as ConstantFact: "constant \(f.fact)"
    case is Unfolding: "constant unfolding"
    case let f as LambdaFact: "λ \(f.fact)"
    case let f as TupleFact: "tuple \(f.fact)"
    case is RekeyFact: "rekey"
    case is Existence: "term existence"
    case is Uniqueness: "term uniqueness"
    default: "\(type(of: lemma.request))"
    }
}

func existence(of a: NodeID, in t: inout Table) throws -> Existence {
    let c = try closed(a, in: &t)
    return Existence(term: c.term, types: c.types, name: "EX_" + fingerprint(c.term, t))
}

func uniqueness(of a: NodeID, in t: inout Table) throws -> Uniqueness {
    let c = try closed(a, in: &t)
    return Uniqueness(term: c.term, types: c.types, name: "UNIQ_" + fingerprint(c.term, t))
}

func lambdaFact(_ lambda: NodeID, _ fact: LambdaFact.Fact, in t: inout Table) throws -> (LambdaFact, Closed) {
    let c = try closed(lambda, in: &t)
    let prefix =
        switch fact {
        case .classExists: "CLASS_"
        case .function: "FUNC_"
        case .arguments: "LAMBDA_"
        }
    return (LambdaFact(lambda: c.term, types: c.types, fact: fact, name: prefix + fingerprint(c.term, t)), c)
}

func universal(_ types: [IRType], guards: Bool, _ body: NodeID, in t: inout Table) throws -> NodeID {
    var root = body
    for T in types.reversed() {
        if T == .i || T == .o {
            root = try t.intern(.ifolAll(T, body: root))
            continue
        }
        if guards, let g = try guarded(try t.intern(.isaBound(0, T)), T, in: &t) { root = try t.intern(.folImplies(
            g,
            root,
        )) }
        root = try t.intern(.folForall(body: root))
    }
    return root
}

func instantiated(
    _ lemma: NodeID,
    at xs: [NodeID],
    _ types: [IRType],
    guards: Bool,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID,
    in t: inout Table,
) throws -> NodeID {
    var p = lemma
    for (x, T) in zip(xs, types) {
        if T == .i || T == .o {
            p = try t.intern(T == .i ? .isaAllElim(p, x) : .folSchemaInst(p, x))
            continue
        }
        p = try t.intern(.folForallElim(p, x))
        if guards, guardPredicate(T) != nil { p = try t.intern(.folImpliesElim(p, try guardOf(x, T, &t))) }
    }
    return p
}

func isaGuard(_ x: NodeID, _ T: IRType, _ t: inout Table) throws -> NodeID {
    guard let g = try guarded(x, T, in: &t) else { throw ReifyError.notATerm(x) }
    return try t.intern(.isaGuard(x, g))
}

func statement(_ r: Existence, in t: inout Table) throws -> NodeID {
    let valued = try equation(try t.intern(.isaBound(0, .i)), try shift(r.term, by: 1, in: &t), in: &t)
    return try universal(
        r.types,
        guards: false,
        try t.intern(.ifolEx(.i, body: try named(atom: t[valued], in: &t))),
        in: &t,
    )
}

func statement(_ r: Uniqueness, in t: inout Table) throws -> NodeID {
    var naming = Naming()
    let v = try naming.name(r.term, [], &t)
    let v2 = try naming.name(r.term, [], &t)
    let core = try naming.chain.predicate(.base("eq"), [v, v2], in: &t)
    return try universal(r.types, guards: true, try naming.chain.premises(core, in: &t), in: &t)
}

private func classParameters(_ T: IRType, under inner: Int, in t: inout Table) throws -> [NodeID] {
    let classes = T.domains.filter { $0 != .i }
    return try classes.indices.map { try t.intern(.isaBound(inner + classes.count - 1 - $0, classes[$0])) }
}

func agreement(_ C: NodeID, _ C2: NodeID, function: Bool, in t: inout Table) throws -> NodeID {
    let c = try shift(C, by: function ? 2 : 1, in: &t)
    let c2 = try shift(C2, by: function ? 2 : 1, in: &t)
    let x = try t.intern(.isaBound(function ? 1 : 0, .i))
    let r = try t.intern(.isaBound(0, .i))
    let atom = { (k: NodeID, t: inout Table) throws -> NodeID in
        try t.intern(.folPred(.base(function ? "pmem" : "elem"), args: function ? [x, r, k] : [x, k]))
    }
    var body = try t.intern(.folIff(try atom(c, &t), try atom(c2, &t)))
    for _ in 0..<(function ? 2 : 1) { body = try t.intern(.ifolAll(.i, body: body)) }
    return body
}

func isFunctionClass(_ T: IRType) -> Bool {
    result(T) == .i
}

func statement(_ f: ConstantFact, in t: inout Table) throws -> NodeID {
    let classes = f.type.domains.filter { $0 != .i }
    let k = classes.count
    let m = f.type.domains.count - k
    let named = { (C: NodeID, ps: [NodeID], t: inout Table) throws -> NodeID in
        try t.intern(.folPred(.constant(f.constant), args: [C] + ps))
    }
    let foralls = { (n: Int, body: NodeID, t: inout Table) throws -> NodeID in
        var root = body
        for _ in 0..<n { root = try t.intern(.folForall(body: root)) }
        return root
    }
    switch f.fact {
    case .existence:
        return try t.intern(.ifolEx(
            .i,
            body: try t.intern(.folPred(.constant(f.constant), args: [try t.intern(.isaBound(0, .i))])),
        ))

    case .uniqueness:
        let v = try t.intern(.isaBound(1, .i))
        let w = try t.intern(.isaBound(0, .i))
        let cv = try t.intern(.folPred(.constant(f.constant), args: [v]))
        let cw = try t.intern(.folPred(.constant(f.constant), args: [w]))
        let body = try t.intern(.folImplies(
            cv,
            try t.intern(.folImplies(cw, try t.intern(.folPred(.base("eq"), args: [v, w])))),
        ))
        return try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: body))))

    case .classExists:
        // ⚠ A SET CONSTANT'S CLASS IS A SET, `∃ᵢS`: its witness is one, and `exists_intro` keeps an isa witness
        // `isaBound`
        // under a fol binder, so `∃S` would differ from the proof's conclusion by ID.
        if f.type == .i {
            let v = try t.intern(.isaBound(0, .i))
            let member = try t.intern(.folPred(.base("elem"), args: [v, try t.intern(.isaBound(1, .i))]))
            let exact = try t.intern(.folIff(member, try t.intern(.folPred(.constant(f.constant), args: [v]))))
            return try t.intern(.ifolEx(.i, body: try t.intern(.ifolAll(.i, body: exact))))
        }
        let ps = try classParameters(f.type, under: 1, in: &t)
        return try foralls(k, try t.intern(.folExists(body: try named(try t.intern(.folBound(0)), ps, &t))), &t)

    case .agreement:
        let ps = try classParameters(f.type, under: k + 2, in: &t)
        let ps2 = try classParameters(f.type, under: 2, in: &t)
        let C = try t.intern(.folBound(1))
        let C2 = try t.intern(.folBound(0))
        var body = try agreement(C, C2, function: isFunctionClass(f.type), in: &t)
        body = try t.intern(.folImplies(try named(C2, ps2, &t), body))
        body = try t.intern(.folImplies(try named(C, ps, &t), body))
        for j in (0..<k).reversed() {
            body = try t.intern(.folImplies(
                try agreement(ps[j], ps2[j], function: isFunctionClass(classes[j]), in: &t),
                body,
            ))
        }
        return try foralls(2 * k + 2, body, &t)

    case .totality:
        let tau = try t.intern(.isaBound(0, .i))
        let xs = try (0..<m).map { try t.intern(.isaBound(m - $0, .i)) }
        let value = try t.intern(.folPred(
            .base("pmem"),
            args: [
                try t.intern(.isaBound(1, .i)),
                try t.intern(.isaBound(0, .i)),
                try t.intern(.folBound(m + 2)),
            ],
        ))
        var body = try t.intern(.folImplies(try tuple(xs, tau, in: &t), try t.intern(.ifolEx(.i, body: value))))
        for _ in 0...m { body = try t.intern(.ifolAll(.i, body: body)) }
        body = try t.intern(.folImplies(
            try named(try t.intern(.folBound(0)), try classParameters(f.type, under: 1, in: &t), &t),
            body,
        ))
        return try foralls(k + 1, body, &t)

    case .lift:
        return try lift(f, in: &t)

    case .function:
        let C = try t.intern(.folBound(0))
        let ps = try classParameters(f.type, under: 1, in: &t)
        var body = try t.intern(.folImplies(try named(C, ps, &t), try t.intern(.folPred(.base("function"), args: [C]))))
        body = try t.intern(.folForall(body: body))
        let outer = try classParameters(f.type, under: 0, in: &t)
        for j in (0..<k).reversed() where isFunctionClass(classes[j]) {
            if let g = try guarded(outer[j], classes[j], in: &t) { body = try t.intern(.folImplies(g, body)) }
        }
        return try foralls(k, body, &t)
    }
}

func statement(_ f: LambdaFact, base: Base, in t: inout Table) throws -> NodeID {
    switch f.fact {
    case .classExists:
        let K = try t.intern(.folBound(0))
        let def = try classDefinition(try shift(f.lambda, by: 1, in: &t), K: K, in: &t)
        return try universal(f.types, guards: false, try t.intern(.folExists(body: def)), in: &t)

    case .function:
        let K = try t.intern(.folBound(0))
        let def = try classDefinition(try shift(f.lambda, by: 1, in: &t), K: K, in: &t)
        let body = try t.intern(.folForall(body: try t.intern(.folImplies(
            def,
            try t.intern(.folPred(.base("function"), args: [K])),
        ))))
        return try universal(f.types, guards: true, body, in: &t)

    case .arguments:
        let at = try atArguments(try shift(f.lambda, by: 1, in: &t), try t.intern(.folBound(0)), base: base, in: &t)
        return try universal(f.types, guards: true, try t.intern(.folExists(body: at)), in: &t)
    }
}

func statement(_ f: TupleFact, in t: inout Table) throws -> NodeID {
    let n = f.arity
    switch f.fact {
    case .existence:
        let xs = try (0..<n).map { try t.intern(.isaBound(n - $0, .i)) }
        var body = try t.intern(.ifolEx(.i, body: try tuple(xs, try t.intern(.isaBound(0, .i)), in: &t)))
        for _ in 0..<n { body = try t.intern(.ifolAll(.i, body: body)) }
        return body

    case .uniqueness:
        let xs = try (0..<n).map { try t.intern(.isaBound(2 * n + 1 - $0, .i)) }
        let ys = try (0..<n).map { try t.intern(.isaBound(n + 1 - $0, .i)) }
        let tau = try t.intern(.isaBound(1, .i))
        let tau2 = try t.intern(.isaBound(0, .i))
        var body = try t.intern(.folImplies(
            try tuple(xs, tau, in: &t),
            try t.intern(.folImplies(
                try tuple(ys, tau2, in: &t),
                try t.intern(.folPred(
                    .base("eq"),
                    args: [tau, tau2],
                )),
            )),
        ))
        body = try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: body))))
        for j in (0..<n).reversed() {
            let x = try shift(xs[j], by: -2, in: &t)
            let y = try shift(ys[j], by: -2, in: &t)
            body = try t.intern(.folImplies(try t.intern(.folPred(.base("eq"), args: [x, y])), body))
        }
        for _ in 0..<(2 * n) { body = try t.intern(.ifolAll(.i, body: body)) }
        return body

    case .injectivity:
        let xs = try (0..<n).map { try t.intern(.isaBound(2 * n - $0, .i)) }
        let ys = try (0..<n).map { try t.intern(.isaBound(n - $0, .i)) }
        let tau = try t.intern(.isaBound(0, .i))
        var equal = try t.intern(.folPred(.base("eq"), args: [xs[n - 1], ys[n - 1]]))
        for j in (0..<(n - 1)).reversed() {
            equal = try t.intern(.folAnd(try t.intern(.folPred(.base("eq"), args: [xs[j], ys[j]])), equal))
        }
        var body = try t.intern(.folImplies(
            try tuple(xs, tau, in: &t),
            try t.intern(.folImplies(try tuple(ys, tau, in: &t), equal)),
        ))
        for _ in 0..<(2 * n + 1) { body = try t.intern(.ifolAll(.i, body: body)) }
        return body
    }
}

func pred(_ name: String, _ levels: [Int], at s: Scope, _ t: inout Table) throws -> NodeID {
    try t.intern(.folPred(.base(name), args: try levels.map { try s.variable($0, in: &t) }))
}

func approximation(
    _ X: Int,
    _ A: Int,
    record a: Int,
    _ p: Int,
    _ p1: Int,
    function: Bool,
    in s: Scope,
    _ t: inout Table,
) throws -> NodeID {
    var each = s
    let values = (0..<(function ? 2 : 1)).map { _ in each.fix(.i) }
    var inner = each
    let b = inner.fix(.i)
    var rest: NodeID
    if function {
        var deeper = inner
        let b2 = deeper.fix(.i)
        let second = try t.intern(.folAnd(
            try pred("snoc", [b, p1, values[1], b2], at: deeper, &t),
            try pred("elem", [b2, A], at: deeper, &t),
        ))
        rest = try t.intern(.ifolEx(.i, body: second))
    } else {
        rest = try pred("elem", [b, A], at: inner, &t)
    }
    let first = try t.intern(.folAnd(try pred("snoc", [a, p, values[0], b], at: inner, &t), rest))
    let left = try pred(function ? "pmem" : "elem", values + [X], at: each, &t)
    var body = try t.intern(.folIff(left, try t.intern(.ifolEx(.i, body: first))))
    for _ in values { body = try t.intern(.ifolAll(.i, body: body)) }
    return body
}

private func lift(_ f: ConstantFact, in t: inout Table) throws -> NodeID {
    let classes = f.type.domains.filter { $0 != .i }
    var s = Scope()
    let p = s.fix(.i)
    let p1 = s.fix(.i)
    let outer = s
    let As = classes.map { _ in s.fix(nil) }
    let U = s.fix(nil)
    let a = s.fix(.i)
    let atA = s
    let Ks = classes.map { s.fix($0) }
    let atK = s
    let C = s.fix(nil)
    let named = try t.intern(.folPred(.constant(f.constant), args: try ([C] + Ks).map { try s.variable($0, in: &t) }))
    var body = try t.intern(.folImplies(
        named,
        try approximation(C, U, record: a, p, p1, function: isFunctionClass(f.type), in: s, &t),
    ))
    body = try t.intern(.folForall(body: body))
    for j in classes.indices.reversed() {
        let premise = try approximation(
            Ks[j],
            As[j],
            record: a,
            p,
            p1,
            function: isFunctionClass(classes[j]),
            in: atK,
            &t,
        )
        body = try t.intern(.folImplies(premise, body))
    }
    for _ in Ks { body = try t.intern(.folForall(body: body)) }
    body = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(try pred("tuple", [a, p], at: atA, &t), body))))
    body = try t.intern(.folExists(body: body))
    for _ in As { body = try t.intern(.folForall(body: body)) }
    body = try t.intern(.folImplies(try pred("nsucc", [p, p1], at: outer, &t), body))
    return try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: body))))
}

func statement(_ f: RekeyFact, in t: inout Table) throws -> NodeID {
    let m = f.width
    var s = Scope()
    let p = s.fix(.i)
    let p1 = s.fix(.i)
    let outer = s
    let W = s.fix(nil)
    let U = s.fix(nil)
    let a = s.fix(.i)
    let atA = s
    let values = (0..<m).map { _ in s.fix(.i) }
    let records = (0..<m).map { _ in s.fix(.i) }
    var inner = s
    let rho = inner.fix(.i)
    let entries = try ([p, p1, a] + values).map { try inner.variable($0, in: &t) }
    let some = try t.intern(.ifolEx(
        .i,
        body: try t.intern(.folAnd(
            try tuple(entries, try inner.variable(rho, in: &t), in: &t),
            try pred("elem", [rho, W], at: inner, &t),
        )),
    ))
    var body = try t.intern(.folIff(try pred("elem", [records[m - 1], U], at: s, &t), some))
    for j in (0..<m).reversed() {
        body = try t.intern(.folImplies(
            try pred("snoc", [j == 0 ? a : records[j - 1], j == 0 ? p : p1, values[j], records[j]], at: s, &t),
            body,
        ))
    }
    for _ in 0..<(2 * m) { body = try t.intern(.ifolAll(.i, body: body)) }
    body = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(try pred("tuple", [a, p], at: atA, &t), body))))
    body = try t.intern(.folForall(body: try t.intern(.folExists(body: body))))
    body = try t.intern(.folImplies(try pred("nsucc", [p, p1], at: outer, &t), body))
    return try t.intern(.ifolAll(.i, body: try t.intern(.ifolAll(.i, body: body))))
}
