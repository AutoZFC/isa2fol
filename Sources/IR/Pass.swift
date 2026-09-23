public enum Invariant: Hashable, Sendable {
    case noTypeShape(TypeShape)
}

public protocol Pass: Sendable {
    var name: String { get }
    var ensures: [Invariant] { get }
    func run(_ b: inout Builder) throws
}

public protocol RewritePattern: Sendable {
    func matches(_ op: Op) -> Bool
    func rewrite(_ id: OpID, _ b: inout Builder) throws
}

public struct PatternPass: Pass {
    public let name: String
    public let ensures: [Invariant]
    public let patterns: [any RewritePattern]
    public let maxRounds: Int

    public init(name: String, ensures: [Invariant],
                patterns: [any RewritePattern], maxRounds: Int = 64) {
        self.name = name
        self.ensures = ensures
        self.patterns = patterns
        self.maxRounds = maxRounds
    }

    public func run(_ b: inout Builder) throws {
        for round in 0...maxRounds {
            var fired = false
            sweep: for id in b.graph.liveOps {
                let op = b.graph.op(id)
                for p in patterns where p.matches(op) {
                    try p.rewrite(id, &b)
                    fired = true
                    break sweep
                }
            }
            if !fired { return }
            if round == maxRounds {
                throw IRRefusal.fixpointDidNotConverge(pass: name, rounds: maxRounds)
            }
        }
    }
}

public struct PassManager: Sendable {
    public let passes: [any Pass]
    public init(_ passes: [any Pass]) { self.passes = passes }

    public func run(_ g: Graph) throws -> Graph {
        var b = Builder(g)
        for p in passes {
            try p.run(&b)
            try verify(b.graph, p.ensures)
        }
        return b.graph
    }
}
