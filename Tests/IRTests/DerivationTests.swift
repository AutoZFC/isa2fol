import Testing
@testable import IR

@Test func aDerivationCannotBeRewritten() throws {
    var b = Builder()
    let r = b.graph.root
    let x = try b.append(.folVar("x"), results: [.i], to: r)[0]
    let p = try b.append(.folPred("set"), operands: [x], results: [.o], to: r)[0]
    let d = try b.append(.folUse("members_are_sets"),
                         results: [.o], to: r)[0]
    let e = try b.append(.folUse("elem_second"),
                         results: [.o], to: r)[0]

    try b.replaceAllUses(of: p, with: p)

    #expect(throws: IRRefusal.rewroteADerivation(d)) {
        try b.replaceAllUses(of: d, with: e)
    }
}

@Test func aDerivationCannotBeErased() throws {
    var b = Builder()
    let r = b.graph.root
    _ = try b.append(.folUse("eq_refl"), results: [.o], to: r)
    let op = b.graph.liveOps.last!
    #expect(throws: IRRefusal.erasedADerivation(op)) { try b.erase(op) }
}

@Test func anArityMismatchIsAnError() throws {
    var b = Builder()
    let r = b.graph.root
    let x = try b.append(.folVar("x"), results: [.i], to: r)[0]
    #expect(throws: IRRefusal.self) {
        try b.append(.folImplies, operands: [x], results: [.o], to: r)
    }
}

@Test func aFixpointThatDoesNotConvergeThrows() throws {
    struct Churn: RewritePattern {
        func matches(_ op: Op) -> Bool { if case .folVar = op { return true }; return false }
        func rewrite(_ id: OpID, _ b: inout Builder) throws {
            _ = try b.insert(.folVar("x"), results: [.i], before: id)
        }
    }
    var b = Builder()
    _ = try b.append(.folVar("x"), results: [.i], to: b.graph.root)
    let p = PatternPass(name: "churn", ensures: [], patterns: [Churn()], maxRounds: 4)
    #expect(throws: IRRefusal.fixpointDidNotConverge(pass: "churn", rounds: 4)) {
        var c = b
        try p.run(&c)
    }
}
