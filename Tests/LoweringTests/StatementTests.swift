import Testing
@testable import IR
@testable import Lowering

/// `⋀x. (mem(x,y) ⟹ mem(x,y))` — Pure's binder and arrow over an IFOL atom.
private func isabelleStatement() throws -> Graph {
    var b = Builder()
    let top = b.graph.root
    let y = try b.append(.isaFree("y", .i), to: top)
    let body = b.region(args: [.i])
    let x = b.graph.region(body).args[0]
    let a = try b.append(.isaAtom("mem", [x, y]), to: body)
    let p = try b.append(.isaTrueprop(a), to: body)
    let imp = try b.append(.isaImp(p, p), to: body)
    b.setResult(body, imp)
    _ = try b.append(.isaAll(.i, body), to: top)
    return b.graph
}

@Test func theStatementLoweringAddsTheGuard() throws {
    let out = try lowerStatement(try isabelleStatement())
    let text = out.dump()
    #expect(text.contains("folForall"), "the binder lowered")
    #expect(text.contains(#"folPred("set""#), "R3's guard was inserted")
    #expect(!text.contains("isaAll") && !text.contains("isaImp")
            && !text.contains("isaTrueprop"), "no Pure construct survives")
}

/// The guard must dominate the body, not sit beside it.
@Test func theGuardIsTheAntecedentOfTheRegionResult() throws {
    let out = try lowerStatement(try isabelleStatement())
    let forall = out.liveOps.first { if case .folForall = out.op($0) { return true }; return false }
    guard case let .folForall(binder, region) = out.op(forall!) else { return }
    #expect(binder == .setVar)
    guard let result = out.region(region).result else { return }
    guard case let .folImplies(ante, _) = out.op(result) else {
        Issue.record("the region's result is not an implication: \(out.op(result))"); return
    }
    guard case let .folPred(name, args) = out.op(ante) else {
        Issue.record("the antecedent is not the guard: \(out.op(ante))"); return
    }
    #expect(name == "set")
    #expect(args == [out.region(region).args[0]], "the guard is on the BOUND variable")
}

/// ⚠ PHASE 2 RE-RUNS THIS RATHER THAN RECEIVING IT, so it must be a function.
@Test func loweringIsDeterministic() throws {
    let a = try lowerStatement(try isabelleStatement())
    let b = try lowerStatement(try isabelleStatement())
    #expect(a == b, "same statement in, same graph out — including OpIDs")
}

@Test func aBinderAtANonSetSortRefusesRatherThanGuessing() throws {
    var b = Builder()
    let body = b.region(args: [.o])
    let p = try b.append(.folPred("P", []), to: body)
    b.setResult(body, p)
    _ = try b.append(.isaAll(.o, body), to: b.graph.root)
    #expect(throws: IRRefusal.binderSortNotGuardable(.o)) {
        _ = try lowerStatement(b.graph)
    }
}
