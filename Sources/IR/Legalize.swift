public func legalize(_ root: NodeID, in t: Table) throws {
    var pending = [root]
    while let id = pending.popLast() {
        guard t[id].dialects.contains(.fol) else { throw IRRefusal.sourceKindSurvived(id) }
        t[id].forEachChild { c, _ in pending.append(c) }
    }
}
