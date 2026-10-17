import IR

public func plan(_ base: Base) -> [Pass] {
    [Expand(), Logic(base: base), Fol(base: base)]
}

public func provers(_ base: Base) -> Provers {
    Provers([ReifyProver(base: base), TupleProver(base: base), ClassProver(base: base), LambdaProver(base: base)])
}

public func pipeline(_ base: Base) -> Pipeline {
    Pipeline(
        passes: plan(base),
        registry: provers(base),
        provingAfter: "logic",
    )
}

func unfolds(_ f: Family, _ level: Level) -> Bool {
    switch (f, level) {
    case (.pure, _), (.ifol, _), (.fol, _), (.zf, .meta): true
    case (.zf, .object): false
    }
}

func isLogic(_ f: Family) -> Bool {
    switch f {
    case .pure, .ifol, .fol: true
    case .zf: false
    }
}

struct Anywhere: Hashable { }

func children(_ n: Node) -> [NodeID] {
    var found = [NodeID]()
    n.forEachChild { c, _ in found.append(c) }
    return found
}
