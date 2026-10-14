import IR

public var plan: [Pass] { [Expand(), Logic(), Reify(), Fol()] }

public var pipeline: Pipeline { Pipeline(passes: plan, registry: Typing(provers: []), provingAfter: "reify") }

func isObject(_ T: IRType) -> Bool {
    switch T {
    case .i: return true
    case .o, .variable: return false
    case let .fn(a, b): return a == .i && (b == .o || isObject(b))
    }
}

func mentionsTypeVariable(_ T: IRType) -> Bool {
    switch T {
    case .i, .o: return false
    case .variable: return true
    case let .fn(a, b): return mentionsTypeVariable(a) || mentionsTypeVariable(b)
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
