public protocol Pass {
    var name: String { get }
    func run(_ roots: [NodeID], in t: inout Table) throws -> [Rewrite]
}

public struct RulePass: Pass {
    public let name: String
    public let rule: any Rule

    public init(name: String, rule: any Rule) {
        self.name = name
        self.rule = rule
    }

    public func run(_ roots: [NodeID], in t: inout Table) throws -> [Rewrite] {
        var current = roots.map(Rewrite.rewritten)
        while true {
            let live = current.indices.compactMap { k -> (Int, NodeID)? in
                guard case let .rewritten(id) = current[k] else { return nil }
                return (k, id)
            }
            var changed = false
            for ((k, id), next) in zip(live, try transform(live.map(\.1), rule, in: &t)) {
                if case .rewritten(id) = next { continue }
                current[k] = next
                changed = true
            }
            if !changed { return current }
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

public struct Refused: Sendable {
    public let name: String
    public let pass: String
    public let refusal: any Refusal
}

public struct Unit: Sendable {
    public var table: Table
    public var statements: [Statement]
    public private(set) var refused: [Refused] = []

    public init(table: Table, statements: [Statement]) {
        self.table = table
        self.statements = statements
    }

    mutating func refuse(_ s: Statement, _ pass: String, _ refusal: any Refusal) {
        refused.append(Refused(name: s.name, pass: pass, refusal: refusal))
    }
}

public struct Pipeline {
    public let passes: [Pass]

    public init(passes: [Pass]) { self.passes = passes }

    public func run(_ unit: inout Unit) throws {
        for pass in passes {
            let lowered = try pass.run(unit.statements.flatMap { [$0.root, $0.proof] }, in: &unit.table)
            var kept: [Statement] = []
            for (k, s) in unit.statements.enumerated() {
                switch (lowered[2 * k], lowered[2 * k + 1]) {
                case let (.rewritten(root), .rewritten(proof)):
                    let concluded = unit.table.conclusion(of: proof)
                    guard concluded == root else {
                        throw PipelineError.unproved(name: s.name, pass: pass.name, statement: root, conclusion: concluded)
                    }
                    kept.append(Statement(name: s.name, root: root, proof: proof))
                case let (.refused(refusal), _), let (_, .refused(refusal)):
                    unit.refuse(s, pass.name, refusal)
                }
            }
            unit.statements = kept
        }
    }
}
