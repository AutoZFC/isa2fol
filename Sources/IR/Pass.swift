public protocol Pass {
    var name: String { get }
    func run(_ root: NodeID, in t: inout Table) throws -> NodeID
}

public struct RulePass: Pass {
    public let name: String
    public let rule: Rule

    public init(name: String, rule: Rule) {
        self.name = name
        self.rule = rule
    }

    public func run(_ root: NodeID, in t: inout Table) throws -> NodeID {
        var current = root
        while true {
            let next = try transform(current, rule, in: &t)
            if next == current { return current }
            current = next
        }
    }
}

public struct Statement: Sendable {
    public let name: String
    public var root: NodeID

    public init(name: String, root: NodeID) {
        self.name = name
        self.root = root
    }
}

public struct Unit: Sendable {
    public var table: Table
    public var statements: [Statement]

    public init(table: Table, statements: [Statement]) {
        self.table = table
        self.statements = statements
    }
}

public struct Pipeline {
    public let passes: [Pass]

    public init(passes: [Pass]) { self.passes = passes }

    public func run(_ unit: inout Unit) throws {
        for k in unit.statements.indices {
            var root = unit.statements[k].root
            for pass in passes { root = try pass.run(root, in: &unit.table) }
            unit.statements[k].root = root
        }
    }
}
