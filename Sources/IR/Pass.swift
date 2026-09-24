public protocol Pass: Sendable {
    var name: String { get }
    func run(_ b: inout Builder) throws
}

public protocol RewritePattern: Sendable {
    func matches(_ op: Op) -> Bool
    func rewrite(_ id: OpID, _ b: inout Builder) throws
}

public struct PatternPass: Pass {
    public let name: String
    public let patterns: [any RewritePattern]

    public init(name: String, patterns: [any RewritePattern]) {
        self.name = name
        self.patterns = patterns
    }

    public func run(_ b: inout Builder) throws {
        var changed = true
        while changed {
            changed = false
            for id in b.graph.liveOps where !b.graph.isErased(id) {
                let op = b.graph.op(id)
                if let p = patterns.first(where: { $0.matches(op) }) {
                    try p.rewrite(id, &b)
                    changed = true
                }
            }
        }
    }
}

public struct PassManager: Sendable {
    public let passes: [any Pass]
    public init(_ passes: [any Pass]) { self.passes = passes }

    public func run(_ g: Graph) throws -> Graph {
        var b = Builder(g)
        for p in passes { try p.run(&b) }
        return b.graph
    }
}
