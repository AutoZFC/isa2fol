public struct Builder: Sendable {
    public private(set) var graph: Graph

    public init(_ g: Graph = Graph()) { graph = g }

    public mutating func region(args: [IRType], in parent: RegionID? = nil) -> RegionID {
        let id = RegionID(raw: graph.regionNodes.count)
        graph.regionNodes.append(Graph.RegionNode(args: [], ops: []))
        var made: [ValueID] = []
        for t in args { made.append(freshValue(t, producer: nil)) }
        graph.regionNodes[id.raw].args = made
        _ = parent
        return id
    }

    mutating func freshValue(_ t: IRType, producer: OpID?) -> ValueID {
        let id = ValueID(raw: graph.valueNodes.count)
        graph.valueNodes.append(Graph.ValueNode(type: t, producer: producer))
        return id
    }

    @discardableResult
    public mutating func append(_ op: Op,
                                operands: [ValueID] = [],
                                results: [IRType] = [],
                                regions: [RegionID] = [],
                                to parent: RegionID) throws -> [ValueID] {
        try make(op, operands, results, regions, parent, at: nil)
    }

    @discardableResult
    public mutating func insert(_ op: Op,
                                operands: [ValueID] = [],
                                results: [IRType] = [],
                                regions: [RegionID] = [],
                                before anchor: OpID) throws -> [ValueID] {
        let parent = graph.parent(of: anchor)
        let at = graph.regionNodes[parent.raw].ops.firstIndex(of: anchor)
        return try make(op, operands, results, regions, parent, at: at)
    }

    mutating func make(_ op: Op, _ operands: [ValueID], _ results: [IRType],
                       _ regions: [RegionID], _ parent: RegionID,
                       at index: Int?) throws -> [ValueID] {
        if let n = op.arity, n != operands.count {
            throw IRRefusal.arityMismatch(op, expected: n, got: operands.count)
        }
        for v in operands where v.raw >= graph.valueNodes.count {
            throw IRRefusal.unknownValue(v)
        }
        let id = OpID(raw: graph.opNodes.count)
        graph.opNodes.append(Graph.OpNode(op: op, operands: operands, results: [],
                                          regions: regions, parent: parent,
                                          erased: false))
        let made = results.map { freshValue($0, producer: id) }
        graph.opNodes[id.raw].results = made
        if let i = index {
            graph.regionNodes[parent.raw].ops.insert(id, at: i)
        } else {
            graph.regionNodes[parent.raw].ops.append(id)
        }
        return made
    }

    public mutating func replaceAllUses(of v: ValueID, with w: ValueID) throws {
        if let p = graph.producer(of: v), graph.op(p).producesEvidence {
            throw IRRefusal.rewroteADerivation(v)
        }
        for i in graph.opNodes.indices {
            for j in graph.opNodes[i].operands.indices where graph.opNodes[i].operands[j] == v {
                graph.opNodes[i].operands[j] = w
            }
        }
    }

    public mutating func erase(_ o: OpID) throws {
        if graph.op(o).producesEvidence {
            throw IRRefusal.erasedADerivation(o)
        }
        graph.opNodes[o.raw].erased = true
    }

    public mutating func setOperands(_ o: OpID, _ vs: [ValueID]) {
        graph.opNodes[o.raw].operands = vs
    }
}
