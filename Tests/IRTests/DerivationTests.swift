import Testing
@testable import IR

@Test func anUnknownOperandIsAnError() throws {
    var b = Builder()
    #expect(throws: IRRefusal.unknownOperand(OpID(raw: 99))) {
        try b.append(.isaTrueprop(OpID(raw: 99)), to: b.graph.root)
    }
}

@Test func aFixpointThatDoesNotConvergeThrows() throws {
    struct Churn: RewritePattern {
        func matches(_ op: Op) -> Bool { if case .folVar = op { return true }; return false }
        func rewrite(_ id: OpID, _ b: inout Builder) throws {
            _ = try b.insert(.folVar("x"), before: id)
        }
    }
    var b = Builder()
    _ = try b.append(.folVar("x"), to: b.graph.root)
    let p = PatternPass(name: "churn", ensures: [], patterns: [Churn()], maxRounds: 4)
    #expect(throws: IRRefusal.fixpointDidNotConverge(pass: "churn", rounds: 4)) {
        var c = b; try p.run(&c)
    }
}
