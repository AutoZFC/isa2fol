import Testing
@testable import IR

/// `forall x. (set(x) -> mem(x, y))` — a binder, its bound variable, and its body.
@Test func aRegionHoldsABinderBody() throws {
    var b = Builder()
    let top = b.graph.root
    let y = try b.append(.folVar("y"), to: top)

    let body = b.region(args: [.i])          // the scope; its arg IS the bound x
    let x = b.graph.region(body).args[0]
    let guarded = try b.append(.folPred("set", [x]), to: body)
    let inner = try b.append(.folPred("mem", [x, y]), to: body)
    _ = try b.append(.folImplies(guarded, inner), to: body)

    _ = try b.append(.folForall(.setVar, body), to: top)
    #expect(b.graph.op(x) == .blockArg(0, .i), "the bound variable is an ordinary op")
    #expect(b.graph.type(of: x) == .i)
    #expect(b.graph.liveOps.count == 6, "walk descends into the region")
    #expect(b.graph.dump().contains("^1(%1:i):"), "the region prints its argument")
    try legalize(b.graph)
}
