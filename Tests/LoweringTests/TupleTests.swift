import Testing
import IR
@testable import Lowering

/// Each tuple fact at arities 0 to 3: its proof concludes its statement by ID, before Fol and after, every hypothesis is
/// its binder's, and the real checker proves it from base.
@Test func eachTupleFactIsProvedAtEveryArity() throws {
    var t = Table()
    let prover = TupleProver(base: try LoweringTests.base(in: &t))
    var claims: [(name: String, root: NodeID, proof: NodeID)] = []
    for n in 0...3 {
        for fact in [TupleFact.Fact.existence, .uniqueness, .injectivity] where n > 0 || fact != .injectivity {
            let f = TupleFact(arity: n, fact: fact)
            let root = try statement(f, in: &t)
            let proof = try prover.prove(Lemma(f), root, [], in: &t)
            #expect(t.conclusion(of: proof) == root, "\(f.name)")
            #expect(try misscoped(proof, in: t).isEmpty, "\(f.name): a hypothesis is not its binder's")
            let lowered = try Fol().run([root, proof], [], in: &t)
            #expect(t.conclusion(of: lowered[1]) == lowered[0], "\(f.name) through Fol")
            try legalize(lowered[1], in: t)
            if n > 0 { claims.append((f.name, root, proof)) }
        }
    }
    try kernelChecks(claims, in: &t)
}
