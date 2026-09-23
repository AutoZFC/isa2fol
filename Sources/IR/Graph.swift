public struct Graph: Sendable {
    public struct ValueNode: Sendable {
        public var type: IRType
        public var producer: OpID?
    }

    public struct OpNode: Sendable {
        public var op: Op
        public var operands: [ValueID]
        public var results: [ValueID]
        public var regions: [RegionID]
        public var parent: RegionID
        public var erased: Bool
    }

    public struct RegionNode: Sendable {
        public var args: [ValueID]
        public var ops: [OpID]
    }

    var valueNodes: [ValueNode] = []
    var opNodes: [OpNode] = []
    var regionNodes: [RegionNode] = []
    public let root: RegionID

    public init() {
        regionNodes = [RegionNode(args: [], ops: [])]
        root = RegionID(raw: 0)
    }

    public func type(of v: ValueID) -> IRType { valueNodes[v.raw].type }
    public func producer(of v: ValueID) -> OpID? { valueNodes[v.raw].producer }
    public func node(_ o: OpID) -> OpNode { opNodes[o.raw] }
    public func op(_ o: OpID) -> Op { opNodes[o.raw].op }
    public func region(_ r: RegionID) -> RegionNode { regionNodes[r.raw] }
    public func parent(of o: OpID) -> RegionID { opNodes[o.raw].parent }

    public var liveOps: [OpID] {
        var out: [OpID] = []
        walk(root) { out.append($0) }
        return out
    }

    public func walk(_ r: RegionID, _ body: (OpID) -> Void) {
        for o in regionNodes[r.raw].ops where !opNodes[o.raw].erased {
            body(o)
            for sub in opNodes[o.raw].regions { walk(sub, body) }
        }
    }

    public var liveValues: [ValueID] {
        var out: [ValueID] = []
        var seen = Set<ValueID>()
        func take(_ v: ValueID) { if seen.insert(v).inserted { out.append(v) } }
        func sweep(_ r: RegionID) {
            for a in regionNodes[r.raw].args { take(a) }
            for o in regionNodes[r.raw].ops where !opNodes[o.raw].erased {
                for v in opNodes[o.raw].results { take(v) }
                for sub in opNodes[o.raw].regions { sweep(sub) }
            }
        }
        sweep(root)
        return out
    }
}
