public struct Builder: Sendable {
    public private(set) var graph: Graph

    public init(_ g: Graph = Graph()) { graph = g }

    public mutating func region(args: [IRType]) -> RegionID {
        let id = RegionID(raw: graph.regionStore.count)
        graph.regionStore.append(Graph.Region(args: [], ops: [], result: nil))
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

    public mutating func replaceAllUses(of v: OpID, with w: OpID) {
        for i in graph.storage.indices
        where !graph.dead[i] && graph.storage[i].references(v) {
            graph.storage[i] = graph.storage[i].mapOperands { $0 == v ? w : $0 }
        }
        for i in graph.regionStore.indices where graph.regionStore[i].result == v {
            graph.regionStore[i].result = w
        }
    }

    public mutating func setResult(_ r: RegionID, _ o: OpID) {
        graph.regionStore[r.raw].result = o
    }

    public mutating func erase(_ o: OpID) {
        graph.dead[o.raw] = true
    }
}
