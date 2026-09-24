/// ⚠ THE ONLY PLACE THAT NAMES BOTH VOCABULARIES. Exhaustive on purpose: a new
/// op that nothing lowers is caught HERE, because a rewrite pattern is partial
/// and adding a case breaks no pattern.
public func legalize(_ g: Graph) throws {
    for id in g.liveOps {
        switch g.op(id) {
        case .folVar, .folPred, .folImplies, .folForall, .blockArg:
            break
        case .isaFree, .isaAtom, .isaTrueprop, .isaImp, .isaAll:
            throw IRRefusal.opSurvivedLowering(g.op(id), id)
        }
        switch g.type(of: id) {
        case .i, .o: continue
        case .prop, .fn: throw IRRefusal.typeSurvivedLowering(g.type(of: id), id)
        }
    }
}
