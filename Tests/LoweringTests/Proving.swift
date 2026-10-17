import IR
import Testing
@testable import Lowering

private let i = IRType.i
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

/// A lemma and every lemma its proof cites, transitively, as the registry proves them: each proof concludes its
/// statement
/// by ID before Fol and after, and every hypothesis is its binder's. Returns the proved and the unbuilt.
func proveAll(_ requests: [(Lemma, NodeID)], _ definitions: [Definition], in t: inout Table) throws
    -> (proved: [(name: String, root: NodeID, proof: NodeID)], unbuilt: Set<String>)
{
    let base = try LoweringTests.base(in: &t)
    let provers = Lowering.provers(base)
    var proved = [(name: String, root: NodeID, proof: NodeID)]()
    var unbuilt = Set<String>()
    var seen = Set<String>()
    var work = requests
    while let (l, root) = work.popLast() {
        guard seen.insert(l.name).inserted else { continue }
        let answer: Proved
        do { answer = try provers.prove(l, root, definitions, in: &t) } catch {
            Issue.record("\(l.name): \(error)")
            throw error
        }
        switch answer {
        case .unbuilt:
            unbuilt.insert(l.name)
        case .proof(let p):
            #expect(t.conclusion(of: p) == root, "\(l.name)")
            #expect(try misscoped(p, in: t).isEmpty, "\(l.name): a hypothesis is not its binder's")
            let lowered = try Fol(base: base).run([root, p], [], in: &t)
            #expect(t.conclusion(of: lowered[1]) == lowered[0], "\(l.name) through Fol")
            try legalize(lowered[1], in: t)
            proved.append((l.name, root, p))
            var stack = [p]
            var visited = Set<NodeID>()
            while let id = stack.popLast() {
                guard visited.insert(id).inserted else { continue }
                if case .use(.lemma(let cited), _, let r) = t[id] { work.append((cited, r)) }
                t[id].forEachChild { c, _ in stack.append(c) }
            }
        }
    }
    return (proved, unbuilt)
}

struct Terms {
    var t = Table()

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func x(_ k: Int) throws -> NodeID {
        try n(.isaBound(k, i))
    }

    mutating func zero() throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.zero)), i, args: []))
    }

    mutating func pow(_ a: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.pow)), fn(i, i), args: [a]))
    }

    mutating func lam(_ T: IRType, _ body: NodeID) throws -> NodeID {
        try n(.isaAbs(T, body: body))
    }

    mutating func requests(_ a: NodeID) throws -> [(Lemma, NodeID)] {
        let ex = try existence(of: a, in: &t)
        let uniq = try uniqueness(of: a, in: &t)
        return [(Lemma(ex), try statement(ex, in: &t)), (Lemma(uniq), try statement(uniq, in: &t))]
    }
}
