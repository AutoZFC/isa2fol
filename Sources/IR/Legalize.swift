public func verify(_ g: Graph, _ ensures: [Invariant]) throws {
    for inv in ensures {
        switch inv {
        case let .noOpsFrom(d):
            for id in g.liveOps where g.op(id).dialect == d {
                throw IRRefusal.opSurvivedLowering(g.op(id), id)
            }
        case let .noTypeShape(s):
            for v in g.liveValues where g.type(of: v).shapes.contains(s) {
                throw IRRefusal.typeSurvivedLowering(s, v)
            }
        }
    }
}

/// ⚠ THE ONLY PLACE THAT NAMES BOTH VOCABULARIES. Exhaustive on purpose: a new
/// op that nothing lowers is caught HERE, because a rewrite pattern is partial
/// and adding a case breaks no pattern.
public func legalize(_ g: Graph) throws {
    for id in g.liveOps {
        switch g.op(id) {
        case .folVar, .folPred, .folImplies, .folForall, .folUse:
            continue
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll, .isaAxiom:
            throw IRRefusal.opSurvivedLowering(g.op(id), id)
        case .cast:
            throw IRRefusal.opSurvivedLowering(g.op(id), id)
        }
    }
    for v in g.liveValues {
        for s in g.type(of: v).shapes where s == .prop || s == .fn {
            throw IRRefusal.typeSurvivedLowering(s, v)
        }
    }
}

public let folZfcOnly: [Invariant] = [
    .noOpsFrom(.isa), .noOpsFrom(.builtin),
    .noTypeShape(.prop), .noTypeShape(.fn),
]
