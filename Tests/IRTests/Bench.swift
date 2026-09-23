import Testing
@testable import IR

private func r1(_ x: Double) -> Double { (x * 10).rounded() / 10 }

private func ms(_ body: () throws -> Void) rethrows -> Double {
    let c = ContinuousClock()
    let d = try c.measure { try body() }
    return Double(d.components.attoseconds) / 1e15 + Double(d.components.seconds) * 1000
}

@Test func bench() throws {
    print("--- sizes (bytes) ---")
    print("IRType      size=\(MemoryLayout<IRType>.size) stride=\(MemoryLayout<IRType>.stride)")
    print("Op          size=\(MemoryLayout<Op>.size) stride=\(MemoryLayout<Op>.stride)")
    print("ValueID     size=\(MemoryLayout<ValueID>.size)")
    print("Graph       size=\(MemoryLayout<Graph>.size)")
    print("ValueNode   size=\(MemoryLayout<Graph.ValueNode>.size)")
    print("OpNode      size=\(MemoryLayout<Graph.OpNode>.size)")
    print("RegionNode  size=\(MemoryLayout<Graph.RegionNode>.size)")

    for n in [10_000, 20_000, 40_000] {
        var b = Builder()
        let r = b.graph.root
        let build = try ms {
            for i in 0..<n {
                _ = try b.append(.isaFree("v\(i)"), results: [.i], to: r)
            }
        }
        let vals = b.graph.liveValues
        let sweep = ms { _ = b.graph.liveOps }
        let one = try ms { try b.replaceAllUses(of: vals[0], with: vals[1]) }
        print("n=\(n)  build=\(r1(build))ms  liveOps=\(r1(sweep))ms  1xreplaceAllUses=\(r1(one))ms")
    }

    print("--- PatternPass fixpoint, k rewritable ops ---")
    struct ToFol: RewritePattern {
        func matches(_ op: Op) -> Bool { if case .isaFree = op { return true }; return false }
        func rewrite(_ id: OpID, _ b: inout Builder) throws {
            guard case let .isaFree(n) = b.graph.op(id) else { return }
            let old = b.graph.node(id).results[0]
            let new = try b.insert(.folVar(n), results: [.i], before: id)[0]
            try b.replaceAllUses(of: old, with: new)
            try b.erase(id)
        }
    }
    for k in [200, 400, 800] {
        var b = Builder()
        let r = b.graph.root
        for i in 0..<k { _ = try b.append(.isaFree("v\(i)"), results: [.i], to: r) }
        let p = PatternPass(name: "x", ensures: [], patterns: [ToFol()], maxRounds: k + 2)
        let t = try ms { var c = b; try p.run(&c) }
        print("k=\(k)  pass=\(r1(t))ms")
    }
}
