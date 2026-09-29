public protocol Pass {
    var name: String { get }
    func run(_ roots: [NodeID], in t: inout Table) throws -> [NodeID]
}

public struct RulePass: Pass {
    public let name: String
    public let rule: any Rule

    public init(name: String, rule: any Rule) {
        self.name = name
        self.rule = rule
    }

    public func run(_ roots: [NodeID], in t: inout Table) throws -> [NodeID] {
        var current = roots
        while true {
            let next = try transform(current, rule, in: &t)
            if next == current { return current }
            current = next
        }
    }
}

@frozen public enum PipelineError: Error, Equatable, Sendable {
    case unproved(name: String, pass: String, statement: NodeID, conclusion: NodeID?)
}

public struct Statement: Sendable {
    public let name: String
    public var root: NodeID
    public var proof: NodeID

    public init(name: String, root: NodeID, proof: NodeID) {
        self.name = name
        self.root = root
        self.proof = proof
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
        for pass in passes {
            let lowered = try pass.run(unit.statements.flatMap { [$0.root, $0.proof] }, in: &unit.table)
            for k in unit.statements.indices {
                unit.statements[k].root = lowered[2 * k]
                unit.statements[k].proof = lowered[2 * k + 1]
                let s = unit.statements[k]
                let concluded = unit.table.conclusion(of: s.proof)
                guard concluded == s.root else {
                    throw PipelineError.unproved(name: s.name, pass: pass.name, statement: s.root, conclusion: concluded)
                }
            }
        }
    }
}
