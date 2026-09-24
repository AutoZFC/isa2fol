import IR

struct LowerTrueprop: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaTrueprop = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaTrueprop(a) = b.graph.op(id) else { return }
        b.replaceAllUses(of: id, with: a)
        b.erase(id)
    }
}

struct LowerImp: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaImp = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaImp(a, c) = b.graph.op(id) else { return }
        let new = try b.insert(.folImplies(a, c), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

struct LowerFree: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaFree(n, _) = b.graph.op(id) else { return }
        let new = try b.insert(.folVar(n), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

struct LowerAtom: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaAtom = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaAtom(n, xs) = b.graph.op(id) else { return }
        let new = try b.insert(.folPred(n, xs), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

/// ⚠ A CLASS BINDER TAKES NO GUARD — one makes the claim FALSE, not redundant.
/// So a non-`i` sort refuses rather than guessing.
struct GuardBinder: RewritePattern {
    func matches(_ op: Op) -> Bool { if case .isaAll = op { return true }; return false }
    func rewrite(_ id: OpID, _ b: inout Builder) throws {
        guard case let .isaAll(sort, region) = b.graph.op(id) else { return }
        guard sort == .i else { throw IRRefusal.binderSortNotGuardable(sort) }
        guard let body = b.graph.region(region).result else {
            throw IRRefusal.regionHasNoResult(region)
        }
        let x = b.graph.region(region).args[0]
        let guarded = try b.append(.folPred("set", [x]), to: region)
        let implies = try b.append(.folImplies(guarded, body), to: region)
        b.setResult(region, implies)

        let new = try b.insert(.folForall(.setVar, region), before: id)
        b.replaceAllUses(of: id, with: new)
        b.erase(id)
    }
}

/// ⚠ ORDER IS FORCED. `GuardBinder` builds a `folImplies` over the region's
/// result, which must already be a formula — so Pure's coercion has to go first.
public let statementLowering = PassManager([
    PatternPass(name: "lower-pure",
                patterns: [LowerTrueprop(), LowerImp()]),
    PatternPass(name: "lower-ifol",
                patterns: [LowerFree(), LowerAtom()]),
    PatternPass(name: "guard-binders",
                patterns: [GuardBinder()]),
])

public func lowerStatement(_ g: Graph) throws -> Graph {
    let out = try statementLowering.run(g)
    try legalize(out)
    return out
}
