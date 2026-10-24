import IR

@frozen
public enum ValuesError: Error, Equatable, Sendable {
    case escapes(NodeID)
    case notAValue(NodeID)
}

/// What a proof holds for a term at its root: the term's value if it is one, else the term.
func value(of x: NodeID, in t: inout Table) throws -> NodeID {
    guard isValued(x, t) else { return x }
    return try valueNode(x, in: &t)
}

/// ⚠ A VALUE HOLDS A PROPOSITION VARIABLE AS ITS TRUTH, `holds(E)`, NEVER AS THE VARIABLE: a lemma's letter is
/// instantiated at the truth, and a value holding the variable would differ from it by ID.
func valueNode(_ x: NodeID, in t: inout Table) throws -> NodeID {
    try t.intern(.value(try transform(x, TruthRead(), in: &t)))
}

/// A value's truths read back as the proposition variables they stand for: its term as Isabelle holds it.
private struct TruthUnread: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard
            case .folPred(.base("holds"), let xs) = t[id], xs.count == 1, case .folBound(let k) = t[xs[0]],
            k >= depth.terms
        else { return nil }
        return try t.intern(.isaPropBound(k))
    }
}

private struct TruthRead: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms { return id }
        guard case .isaPropBound(let k) = t[id], k >= depth.terms else { return nil }
        return try holds(try t.intern(.folBound(k)), in: &t)
    }
}

struct At: Hashable {
    let node: NodeID
    let depth: Int
}

func isVariable(_ x: NodeID, _ t: Table) -> Bool {
    switch t[x] {
    case .isaBound, .folBound, .value: true
    default: false
    }
}

func isValued(_ x: NodeID, _ t: Table) -> Bool {
    switch t[x] {
    case .isaConst, .isaVarApp: t.type(of: x) == .i
    case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
         .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition,
         .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies, .folAnd, .folOr, .folIff, .folBottom,
         .folImpliesIntro, .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL, .folAndIntro, .folAndElimL,
         .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folBottomElim, .isaGuard, .isaExIntro, .isaExElim,
         .folNot, .folBound, .folPred, .folForall, .folExists, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro,
         .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folClassicalAbsurd, .folSchemaInst, .folLetterAll,
         .folLetter, .folLetterAbs, .folLetterIntro, .value, .valueFact, .valueElim:
        false
    }
}

func fact(of v: NodeID, in t: inout Table) throws -> NodeID {
    try t.intern(.valueFact(v, try valueEquation(v, in: &t)))
}

/// A formula with each maximal term `abstracting` picks replaced by a variable beyond the formula's own, `params` the
/// terms picked, as they stand at the formula's root, in order.
struct Skeleton {
    let formula: NodeID
    let params: [NodeID]
    let width: Int
}

func skeleton(_ x: NodeID, _ picks: @escaping (NodeID, Int, Table) -> Bool, in t: inout Table) throws -> Skeleton {
    let width = t.looseBound(of: x)
    var found = Abstracting(width: width, picks: picks)
    let formula = try found.run(x, in: &t)
    return Skeleton(formula: formula, params: found.params, width: width)
}

private struct Abstracting {
    let width: Int
    let picks: (NodeID, Int, Table) -> Bool
    var params = [NodeID]()
    var position = [NodeID: Int]()

    mutating func run(_ x: NodeID, in t: inout Table) throws -> NodeID {
        var cache = [At: NodeID]()
        return try walk(x, 0, &cache, &t)
    }

    private mutating func walk(_ x: NodeID, _ d: Int, _ cache: inout [At: NodeID], _ t: inout Table) throws -> NodeID {
        if let done = cache[At(node: x, depth: d)] { return done }
        let result: NodeID
        if picks(x, d, t) {
            let normal = try shift(x, by: -d, in: &t)
            let j: Int
            if let k = position[normal] {
                j = k
            } else {
                j = params.count
                position[normal] = j
                params.append(normal)
            }
            result = try t.intern(.isaBound(d + width + j, .i))
        } else {
            var me = self
            let rebuilt = try t[x].mapChildren { c, binds in try me.walk(c, d + binds.terms, &cache, &t) }
            self = me
            result = try t.intern(rebuilt)
        }
        cache[At(node: x, depth: d)] = result
        return result
    }
}

/// EX of a value's term over its skeleton — its arguments, and each fixed term inside its λs, variables — instantiated
/// at their values: `∃r. ⟦r = t⟧`, `t`'s arguments valued.
func existence(
    ofValue v: NodeID,
    base _: Base,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    in t: inout Table,
) throws -> NodeID {
    guard case .value(let held) = t[v] else { throw ValuesError.notAValue(v) }
    let term = try transform(held, TruthUnread(), in: &t)
    let s = try skeleton(
        term,
        { x, d, t in (x != term || d > 0) && isValued(x, t) && Mode.proof(d).valued(x, in: t) },
        in: &t,
    )
    let c = try closed(s.formula, in: &t)
    let r = Existence(term: c.term, types: c.types, name: "EX_" + fingerprint(c.term, t))
    let at = try c.variables.map { x -> NodeID in
        guard case .isaBound(let k, _) = t[x], k >= s.width else { return try formula(x, .proof(0), in: &t) }
        return try valueNode(s.params[k - s.width], in: &t)
    }
    return try instantiated(
        try cited(r, try statement(r, in: &t), &t),
        at: at,
        c.types,
        guards: true,
        guardOf: guardOf,
        in: &t,
    )
}

/// The values `body` holds whose innermost variable is its binder at index 0 — or, with `closed`, those holding no
/// variable — each after the values its fact holds.
func scoped(_ body: NodeID, closed: Bool, below k: Int = 1, in t: inout Table) throws -> [NodeID] {
    var found = [NodeID]()
    var met = Set<NodeID>()
    var seen = Set<At>()
    func belongs(_ v: NodeID, _ t: Table) -> Bool {
        let lowest = lowestLoose(v, in: t)
        return closed ? lowest == Int.max : lowest < k
    }
    func add(_ v: NodeID, _ t: inout Table) throws {
        guard belongs(v, t), !met.contains(v) else { return }
        for w in try values(in: try valueEquation(v, in: &t), &t) where w != v { try add(w, &t) }
        if met.insert(v).inserted { found.append(v) }
    }
    var work = [(body, 0)]
    var roots = [NodeID]()
    while let (n, d) = work.popLast() {
        guard t.looseBound(of: n) > d, seen.insert(At(node: n, depth: d)).inserted else { continue }
        if case .value = t[n] {
            roots.append(try shift(n, by: -d, in: &t))
            continue
        }
        t[n].forEachChild { c, binds in work.append((c, d + binds.terms)) }
    }
    if closed { roots += try closedValues(body, &t) }
    for v in roots { try add(v, &t) }
    return found
}

private func closedValues(_ body: NodeID, _ t: inout Table) throws -> [NodeID] {
    var found = [NodeID]()
    var seen = Set<NodeID>()
    var work = [body]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .value = t[n] {
            if t.looseBound(of: n) == 0 { found.append(n) }
            continue
        }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

/// The values a formula holds, each as it stands at the formula's root.
func values(in formula: NodeID, _ t: inout Table) throws -> [NodeID] {
    var found = [NodeID]()
    var met = Set<NodeID>()
    var seen = Set<At>()
    var work = [(formula, 0)]
    while let (n, d) = work.popLast() {
        guard seen.insert(At(node: n, depth: d)).inserted else { continue }
        if case .value = t[n] {
            let normal = try shift(n, by: -d, in: &t)
            if met.insert(normal).inserted { found.append(normal) }
            continue
        }
        t[n].forEachChild { c, binds in work.append((c, d + binds.terms)) }
    }
    return found
}

enum Fixing {
    case existence(Base)
    case premise
}

/// `body` under one binder per value of `ordered`, outermost first, each value its variable and its fact its
/// hypothesis: `exists_elim` over its EX in a proof, `∀v. fact → …` in a statement, `fix` and `assume` in a lemma's
/// proof.
func fixing(
    _ ordered: [NodeID],
    in body: NodeID,
    by how: Fixing,
    guardOf: (NodeID, IRType, inout Table) throws -> NodeID = isaGuard,
    in t: inout Table,
) throws -> NodeID {
    let k = ordered.count
    guard k > 0 else { return body }
    let index = Dictionary(uniqueKeysWithValues: ordered.enumerated().map { ($1, $0) })
    let closed = Set(ordered.filter { t.looseBound(of: $0) == 0 })
    let holding = closed.isEmpty ? [] : containing(closed, in: body, t)
    var result = try transform(body, Rebind(index: index, count: k, holding: holding), in: &t)
    for j in (0..<k).reversed() {
        let v = ordered[j]
        switch how {
        case .existence(let base):
            let existence = try existence(ofValue: v, base: base, guardOf: guardOf, in: &t)
            let premise = try transform(
                existence,
                Rebind(index: index, count: j, holding: closed.isEmpty ? [] : containing(closed, in: existence, t)),
                in: &t,
            )
            result = try t.intern(.isaExElim(.i, premise, body: result))

        case .premise:
            let fact = try valueEquation(v, in: &t)
            let stated = try transform(
                fact,
                Rebind(index: index, count: j + 1, holding: closed.isEmpty ? [] : containing(closed, in: fact, t)),
                in: &t,
            )
            if t.conclusion(of: result) == nil {
                result = try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(stated, result))))
            } else {
                result = try t.intern(.isaAllIntro(.i, body: try t.intern(.folImpliesIntro(stated, body: result))))
            }
        }
    }
    return result
}

/// ⚠ ONLY AT A STATEMENT'S PROOF'S TOP, WHERE EVERY USE LIES BELOW ITS BINDER: a value fixed by name in two branches
/// has a step they share written above both, where neither name is bound.
func naming(_ ordered: [NodeID], in body: NodeID, base: Base, in t: inout Table) throws -> NodeID {
    var result = body
    for v in ordered.reversed() {
        result = try t.intern(.valueElim(v, try existence(ofValue: v, base: base, in: &t), body: result))
    }
    return result
}

/// The nodes under `root` holding one of the closed `values`: a closed subtree holds no other variable to reindex, so
/// the
/// rebinding walks only these.
private func containing(_ values: Set<NodeID>, in root: NodeID, _ t: Table) -> Set<NodeID> {
    var holds = [NodeID: Bool]()
    func visit(_ n: NodeID) -> Bool {
        if let known = holds[n] { return known }
        if values.contains(n) {
            holds[n] = true
            return true
        }
        var found = false
        t[n].forEachChild { c, _ in if visit(c) { found = true } }
        holds[n] = found
        return found
    }
    _ = visit(root)
    return Set(holds.filter(\.value).keys)
}

/// ⚠ A VALUE'S VARIABLE IS COUNTED FROM THE INSERTED BINDERS' END: the j-th of k, outermost first, is `k - 1 - j` below
/// them, and its fact the hypothesis as far.
private struct Rebind: Rule {
    let index: [NodeID: Int]
    let count: Int
    let holding: Set<NodeID>

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms, t.looseHyps(of: id) <= depth.hyps, !holding.contains(id) { return id }
        switch t[id] {
        case .value:
            let normal = try shift(id, by: -depth.terms, in: &t)
            if let j = index[normal], j < count { return try t.intern(.isaBound(depth.terms + count - 1 - j, .i)) }
            return try shift(id, by: count, in: &t)

        case .isaBound(let k, let T) where k >= depth.terms:
            return try t.intern(.isaBound(k + count, T))

        case .folBound(let k) where k >= depth.terms:
            return try t.intern(.folBound(k + count))

        case .isaPropBound(let k) where k >= depth.terms:
            return try t.intern(.isaPropBound(k + count))

        default:
            return nil
        }
    }

    func after(_ n: Node, was _: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        switch n {
        case .hyp(let h, let a) where h >= depth.hyps:
            return try t.intern(.hyp(h + count, a))

        case .valueFact(let v, let a):
            guard case .isaBound(let k, _) = t[v], k >= depth.terms, k < depth.terms + count else { return nil }
            return try t.intern(.hyp(depth.hyps + (k - depth.terms), a))

        default:
            return nil
        }
    }
}

/// `x`, built at a scope `terms` variables and `hyps` hypotheses shallower, at the deeper one.
func lifted(_ x: NodeID, terms: Int, hyps: Int, in t: inout Table) throws -> NodeID {
    if terms == 0, hyps == 0 { return x }
    return try transform(x, Lifting(terms: terms, hyps: hyps), in: &t)
}

func lifted(_ x: NodeID, from s: Scope, to inner: Scope, in t: inout Table) throws -> NodeID {
    try lifted(x, terms: inner.depth - s.depth, hyps: inner.hyps - s.hyps, in: &t)
}

private struct Lifting: Rule {
    let terms: Int
    let hyps: Int

    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        if t.looseBound(of: id) <= depth.terms, t.looseHyps(of: id) <= depth.hyps { return id }
        if let v = t[id].boundVariable, v.namespace == .term {
            return v.index >= depth.terms ? try t.intern(v.reindexed(v.index + terms)) : id
        }
        return nil
    }

    func after(_ n: Node, was _: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .hyp(let h, let a) = n, h >= depth.hyps else { return nil }
        return try t.intern(.hyp(h + hyps, a))
    }
}
