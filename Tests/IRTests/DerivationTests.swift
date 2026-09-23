import Testing
@testable import IR

@Test func aDerivationCannotBeRewritten() throws {
    var b = Builder()
    let r = b.graph.root
    let x = try b.append(.folVar("x"), to: r)
    let p = try b.append(.folPred("set", [x]), to: r)
    let d = try b.append(.folUse("members_are_sets"), to: r)
    let e = try b.append(.folUse("elem_second"), to: r)

    #expect(b.graph.type(of: p) == b.graph.type(of: d),
            "same type — only the OP may distinguish evidence")
    try b.replaceAllUses(of: p, with: p)
    #expect(throws: IRRefusal.rewroteADerivation(d)) {
        try b.replaceAllUses(of: d, with: e)
    }
}

@Test func aDerivationCannotBeErased() throws {
    var b = Builder()
    let d = try b.append(.folUse("eq_refl"), to: b.graph.root)
    #expect(throws: IRRefusal.erasedADerivation(d)) { try b.erase(d) }
}

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

/// ⚠ THE SOURCE SIDE MUST STAY LOWERABLE. Freezing `isaAxiom` as evidence made
/// `legalize` unreachable for any graph containing a proof.
@Test func anIsaAxiomCanBeLoweredToAFolUse() throws {
    var b = Builder()
    let ax = try b.append(.isaAxiom("ZF_Base.extension"), to: b.graph.root)
    let new = try b.insert(.folUse("extension"), before: ax)
    try b.replaceAllUses(of: ax, with: new)
    try b.erase(ax)
    try legalize(b.graph)
}
