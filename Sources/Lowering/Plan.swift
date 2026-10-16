import IR

public func plan(_ base: Base) -> [Pass] { [Expand(), Logic(base: base), Fol()] }

public func provers(_ base: Base) -> Provers {
    Provers([ReifyProver(base: base), TupleProver(base: base), ClassProver(base: base)])
}

public func pipeline(_ base: Base) -> Pipeline { Pipeline(passes: plan(base), registry: provers(base), provingAfter: "logic") }

func isObject(_ T: IRType) -> Bool {
    switch T {
    case .i: return true
    case .o, .variable: return false
    case let .fn(a, b): return a == .i && (b == .o || isObject(b))
    }
}

func unfolds(_ f: Family, _ level: Level) -> Bool {
    switch (f, level) {
    case (.pure, _), (.ifol, _), (.fol, _), (.zf, .meta): return true
    case (.zf, .object): return false
    }
}

func isLogic(_ f: Family) -> Bool {
    switch f {
    case .pure, .ifol, .fol: return true
    case .zf: return false
    }
}

struct Anywhere: Hashable {}

func children(_ n: Node) -> [NodeID] {
    var found: [NodeID] = []
    n.forEachChild { c, _ in found.append(c) }
    return found
}
