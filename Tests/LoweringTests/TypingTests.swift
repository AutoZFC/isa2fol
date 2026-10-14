import Testing
import IR
import Lowering

private struct Ask: Request {
    let name: String
}

private struct Tell: Request {
    let name: String
}

private struct Answering<R: Request>: Prover {
    let name: String
    let owned: Owned
    let proof: NodeID

    func owns(_ l: Lemma) -> Owned? { l.request is R ? owned : nil }
    func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID { proof }
}

private func asked(_ registry: Typing, _ l: Lemma) throws -> Proved {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    return try registry.prove(l, bottom, [], in: &t)
}

@Test func theRegistryHandsEachLemmaToTheProverThatOwnsItsRequest() throws {
    var t = Table()
    let p = try t.intern(.folBottom), q = try t.intern(.folNot(p))
    let registry = Typing(provers: [Answering<Ask>(name: "ask", owned: .rule, proof: p),
                                    Answering<Tell>(name: "tell", owned: .rule, proof: q)])
    #expect(try asked(registry, Lemma(Ask(name: "a"))) == .proof(p))
    #expect(try asked(registry, Lemma(Tell(name: "b"))) == .proof(q))
}

private func anyProof() throws -> NodeID {
    var t = Table()
    return try t.intern(.folBottom)
}

@Test func aLemmaItsProverHasNotBuiltIsUnbuilt() throws {
    let registry = Typing(provers: [Answering<Ask>(name: "ask", owned: .unbuilt, proof: try anyProof())])
    #expect(try asked(registry, Lemma(Ask(name: "a"))) == .unbuilt)
}

@Test func aRequestNoProverOrTwoProversOwnStopsTheRun() throws {
    let p = try anyProof()
    let none = Typing(provers: [Answering<Ask>(name: "ask", owned: .rule, proof: p)])
    #expect(throws: TypingError.owners(lemma: "b", provers: [])) { _ = try asked(none, Lemma(Tell(name: "b"))) }
    let two = Typing(provers: [Answering<Ask>(name: "ask", owned: .rule, proof: p),
                               Answering<Ask>(name: "again", owned: .unbuilt, proof: p)])
    #expect(throws: TypingError.owners(lemma: "a", provers: ["ask", "again"])) { _ = try asked(two, Lemma(Ask(name: "a"))) }
}
