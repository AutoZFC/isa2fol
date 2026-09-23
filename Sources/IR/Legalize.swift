public func verify(_ g: Graph, _ ensures: [Invariant]) throws {
    for inv in ensures {
        switch inv {
        case let .noOpsFrom(d):
            for id in g.liveOps where g.op(id).dialect == d {
                throw IRRefusal.opSurvivedLowering(g.op(id), id)
            }
        case let .noTypeShape(s):
            for id in g.liveOps where g.type(of: id).shapes.contains(s) {
                throw IRRefusal.typeSurvivedLowering(s, id)
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
        case .folVar, .folPred, .folImplies, .folForall, .folUse, .blockArg:
            continue
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll, .isaAxiom, .cast:
            throw IRRefusal.opSurvivedLowering(g.op(id), id)
        }
        for s in g.type(of: id).shapes where s == .prop || s == .fn {
            throw IRRefusal.typeSurvivedLowering(s, id)
        }
    }
}

public let folZfcOnly: [Invariant] = [
    .noOpsFrom(.isa), .noTypeShape(.prop), .noTypeShape(.fn),
]
