public struct Builder: Sendable {
    public private(set) var graph: Graph

    public init(_ g: Graph = Graph()) { graph = g }

    public mutating func region(args: [IRType]) -> RegionID {
        let id = RegionID(raw: graph.regionStore.count)
        graph.regionStore.append(Graph.Region(args: [], ops: []))
        graph.regionStore[id.raw].args =
            args.enumerated().map { store(.blockArg($0.offset, $0.element), in: id) }
        return id
    }

    mutating func store(_ op: Op, in parent: RegionID) -> OpID {
        let id = OpID(raw: graph.storage.count)
        graph.storage.append(op)
        graph.parents.append(parent)
        graph.dead.append(false)
        return id
    }

    @discardableResult
    public mutating func append(_ op: Op, to parent: RegionID) throws -> OpID {
        try check(op)
        let id = store(op, in: parent)
        graph.regionStore[parent.raw].ops.append(id)
        return id
    }

    @discardableResult
    public mutating func insert(_ op: Op, before anchor: OpID) throws -> OpID {
        try check(op)
        let parent = graph.parent(of: anchor)
        let id = store(op, in: parent)
        let at = graph.regionStore[parent.raw].ops.firstIndex(of: anchor)
            ?? graph.regionStore[parent.raw].ops.count
        graph.regionStore[parent.raw].ops.insert(id, at: at)
        return id
    }

    func check(_ op: Op) throws {
        for v in op.operands where v.raw >= graph.storage.count {
            throw IRRefusal.unknownOperand(v)
        }
    }

    public mutating func replaceAllUses(of v: OpID, with w: OpID) throws {
        if graph.op(v).producesEvidence { throw IRRefusal.rewroteADerivation(v) }
        for i in graph.storage.indices
        where !graph.dead[i] && graph.storage[i].references(v) {
            graph.storage[i] = graph.storage[i].substituting { $0 == v ? w : $0 }
        }
    }

    public mutating func erase(_ o: OpID) throws {
        if graph.op(o).producesEvidence { throw IRRefusal.erasedADerivation(o) }
        graph.dead[o.raw] = true
    }
}
