public func legalize(_ root: NodeID, in t: Table) throws {
    var seen: Set<NodeID> = [], pending = [root]
    while let id = pending.popLast() {
        guard seen.insert(id).inserted else { continue }
        guard Pattern(t[id], in: t).dialects.contains(.fol) else { throw IRRefusal.sourceKindSurvived(id) }
        t[id].forEachChild { c, _ in pending.append(c) }
    }
}
