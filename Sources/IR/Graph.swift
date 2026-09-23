public struct Graph: Sendable, Equatable {
    /// ⚠ `result` IS THE REGION'S VALUE. Never "the last op" — a pass that
    /// appends would silently change what the enclosing binder binds.
    public struct Region: Sendable, Equatable {
        public var args: [OpID]
        public var ops: [OpID]
        public var result: OpID?
    }

    var storage: [Op] = []
    var parents: [RegionID] = []
    var dead: [Bool] = []
    var regionStore: [Region] = [Region(args: [], ops: [], result: nil)]
    public let root = RegionID(raw: 0)

    public init() {}

    public func op(_ o: OpID) -> Op { storage[o.raw] }
    public func type(of o: OpID) -> IRType { storage[o.raw].type }
    public func parent(of o: OpID) -> RegionID { parents[o.raw] }
    public func isErased(_ o: OpID) -> Bool { dead[o.raw] }
    public func region(_ r: RegionID) -> Region { regionStore[r.raw] }

    public var liveOps: [OpID] {
        var out: [OpID] = []
        walk(root) { out.append($0) }
        return out
    }

    public func walk(_ r: RegionID, _ body: (OpID) -> Void) {
        for a in regionStore[r.raw].args where !dead[a.raw] { body(a) }
        for o in regionStore[r.raw].ops where !dead[o.raw] {
            body(o)
            if let sub = storage[o.raw].region { walk(sub, body) }
        }
    }
}
