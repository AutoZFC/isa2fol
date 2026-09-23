import Testing
@testable import IR

private func r1(_ x: Double) -> Double { (x * 10).rounded() / 10 }

private func ms(_ body: () throws -> Void) rethrows -> Double {
    let d = try ContinuousClock().measure { try body() }
    return Double(d.components.attoseconds) / 1e15 + Double(d.components.seconds) * 1000
}

@Test func bench() throws {
    print("--- sizes (bytes) ---")
    print("IRType size=\(MemoryLayout<IRType>.size) stride=\(MemoryLayout<IRType>.stride)")
    print("Op     size=\(MemoryLayout<Op>.size) stride=\(MemoryLayout<Op>.stride)")
    print("OpID   size=\(MemoryLayout<OpID>.size)")
    print("Graph  size=\(MemoryLayout<Graph>.size)")
    print("Region size=\(MemoryLayout<Graph.Region>.size)")

    for n in [10_000, 20_000, 40_000] {
        var b = Builder()
        let r = b.graph.root
        let build = try ms {
            for i in 0..<n { _ = try b.append(.isaFree("v\(i)", .i), to: r) }
        }
        let live = b.graph.liveOps
        let sweep = ms { _ = b.graph.liveOps }
        let one = ms { b.replaceAllUses(of: live[0], with: live[1]) }
        print("n=\(n)  build=\(r1(build))ms  liveOps=\(r1(sweep))ms  1xreplaceAllUses=\(r1(one))ms")
    }

    struct ToFol: RewritePattern {
        func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
        func rewrite(_ id: OpID, _ b: inout Builder) throws {
            guard case let .isaFree(n, _) = b.graph.op(id) else { return }
            let new = try b.insert(.folVar(n), before: id)
            b.replaceAllUses(of: id, with: new)
            b.erase(id)
        }
    }
    print("--- PatternPass fixpoint ---")
    for k in [200, 400, 800] {
        var b = Builder()
        let r = b.graph.root
        for i in 0..<k { _ = try b.append(.isaFree("v\(i)", .i), to: r) }
        let p = PatternPass(name: "x", ensures: [], patterns: [ToFol()], maxRounds: k + 2)
        let t = try ms { var c = b; try p.run(&c) }
        print("k=\(k)  pass=\(r1(t))ms")
    }
}
