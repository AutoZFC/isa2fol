public struct Depth: Hashable, Sendable {
    public init(terms: Int = 0, hyps: Int = 0) {
        self.terms = terms
        self.hyps = hyps
    }

    public var terms: Int
    public var hyps: Int

}

public protocol Rule {
    associatedtype Context: Hashable = Depth

    var start: Context { get }

    func enter(_ c: Context, _ binder: Node, _ binds: Binds, in t: Table) -> Context
    func narrow(_ c: Context, _ id: NodeID, in t: Table) -> Context
    func before(_ id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
    func after(_ n: Node, was id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
}

extension Rule {
    public func narrow(_ c: Context, _: NodeID, in _: Table) -> Context {
        c
    }

    public func before(_: NodeID, context _: Context, in _: inout Table) throws -> NodeID? {
        nil
    }

    public func after(_: Node, was _: NodeID, context _: Context, in _: inout Table) throws -> NodeID? {
        nil
    }
}

extension Rule where Context == Depth {
    public var start: Depth {
        Depth()
    }

    public func enter(_ c: Depth, _: Node, _ binds: Binds, in _: Table) -> Depth {
        Depth(terms: c.terms + binds.terms, hyps: c.hyps + binds.hyps)
    }
}

private struct Visit<Context: Hashable>: Hashable {
    let id: NodeID
    let context: Context
}

/// The forms at a pass's walk of the nodes its run's units share, each where a unit enters what it shares: the first
/// unit to meet one at the walk's start lowers it, and the rest read its form.
public struct Memo: Sendable {
    public init() {
        shared = []
    }

    /// Over the roots of each unit of a run: a node two of them reach, met by one at its root or below a node no other
    /// reaches, is shared.
    init(_ units: [[NodeID]], in t: Table) {
        var last = [Int32](repeating: -1, count: t.count)
        var twice = [Bool](repeating: false, count: t.count)
        for (u, roots) in units.enumerated() {
            let unit = Int32(u)
            var work = roots
            while let id = work.popLast() {
                let k = Int(id.raw)
                let seen = last[k]
                guard seen != unit else { continue }
                last[k] = unit
                if twice[k] { continue }
                if seen >= 0 { twice[k] = true }
                t[id].forEachChild { c, _ in work.append(c) }
            }
        }
        var entered = [Bool](repeating: false, count: t.count)
        for (u, roots) in units.enumerated() {
            let unit = Int32(units.count + u)
            var work = roots
            while let id = work.popLast() {
                let k = Int(id.raw)
                guard last[k] != unit else { continue }
                last[k] = unit
                if twice[k] {
                    entered[k] = true
                    continue
                }
                t[id].forEachChild { c, _ in work.append(c) }
            }
        }
        shared = entered
    }

    private(set) var recorded = [(node: NodeID, form: NodeID)]()

    func shares(_ id: NodeID) -> Bool {
        let k = Int(id.raw)
        return k < shared.count && shared[k]
    }

    func form(of id: NodeID) -> NodeID? {
        forms[id]
    }

    mutating func record(_ id: NodeID, _ form: NodeID) {
        forms[id] = form
        recorded.append((id, form))
    }

    /// The forms recorded since the last import, at their IDs in the table that imported them.
    mutating func settle(_ moved: [NodeID]) {
        for (r, m) in zip(recorded, moved) { forms[r.node] = m }
        recorded = []
    }

    private let shared: [Bool]
    private var forms = [NodeID: NodeID]()
}

public func transform(_ roots: [NodeID], _ rule: some Rule, in t: inout Table) throws -> [NodeID] {
    var memo = Memo()
    return try transform(roots, rule, sharing: &memo, in: &t)
}

public func transform<R: Rule>(_ roots: [NodeID], _ rule: R, sharing memo: inout Memo, in t: inout Table) throws
    -> [NodeID]
{
    var cache = [Visit<R.Context>: NodeID]()
    return try roots.map { try visit($0, rule.start, rule, &cache, &memo, &t) }
}

public func transform(_ root: NodeID, _ rule: some Rule, in t: inout Table) throws -> NodeID {
    try transform([root], rule, in: &t)[0]
}

private func visit<R: Rule>(
    _ id: NodeID,
    _ outer: R.Context,
    _ rule: R,
    _ cache: inout [Visit<R.Context>: NodeID],
    _ memo: inout Memo,
    _ t: inout Table,
) throws -> NodeID {
    let key = Visit(id: id, context: rule.narrow(outer, id, in: t))
    if let done = cache[key] { return done }
    let shared = memo.shares(id) && key.context == rule.start
    if shared, let form = memo.form(of: id) { return form }
    let result = try rewrite(id, key.context, rule, &cache, &memo, &t)
    cache[key] = result
    if shared { memo.record(id, result) }
    return result
}

private func rewrite<R: Rule>(
    _ id: NodeID,
    _ c: R.Context,
    _ rule: R,
    _ cache: inout [Visit<R.Context>: NodeID],
    _ memo: inout Memo,
    _ t: inout Table,
) throws -> NodeID {
    if let replaced = try rule.before(id, context: c, in: &t) { return replaced }
    let n = t[id]
    let rebuilt = try n.mapChildren { child, binds in
        let inner = binds == .none ? c : rule.enter(c, n, binds, in: t)
        return try visit(child, inner, rule, &cache, &memo, &t)
    }
    if let rewritten = try rule.after(rebuilt, was: id, context: c, in: &t) { return rewritten }
    return try t.intern(rebuilt)
}
