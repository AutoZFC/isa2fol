import IR
import Lowering
import Testing

private struct Ask: Request {
    let name: String

    func remapped(_: (NodeID) throws -> NodeID) rethrows -> Ask {
        self
    }
}

private struct Tell: Request {
    let name: String

    func remapped(_: (NodeID) throws -> NodeID) rethrows -> Tell {
        self
    }
}

private struct Answering<R: Request>: Prover {
    let name: String
    let owned: Owned
    let proof: NodeID

    func owns(_ l: Lemma) -> Owned? {
        l.request is R ? owned : nil
    }

    func prove(_: Lemma, _: NodeID, _: [Definition], _: [String: NodeID], in _: inout Table) throws -> Proved {
        .proof(proof)
    }

    func defines(_ c: Defined) -> Owned? {
        c.name == name ? owned : nil
    }

    func define(_: Defined, _: [Definition], in _: inout Table) throws -> NodeID {
        proof
    }
}

private func asked(_ registry: Provers, _ l: Lemma) throws -> Proved {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    return try registry.prove(l, bottom, [], [:], in: &t)
}

@Test
func theRegistryHandsEachLemmaToTheProverThatOwnsItsRequest() throws {
    var t = Table()
    let p = try t.intern(.folBottom)
    let q = try t.intern(.folNot(p))
    let registry = Provers([
        Answering<Ask>(name: "ask", owned: .rule, proof: p),
        Answering<Tell>(name: "tell", owned: .rule, proof: q),
    ])
    #expect(try asked(registry, Lemma(Ask(name: "a"))) == .proof(p))
    #expect(try asked(registry, Lemma(Tell(name: "b"))) == .proof(q))
}

private func anyProof() throws -> NodeID {
    var t = Table()
    return try t.intern(.folBottom)
}

@Test
func aLemmaItsProverHasNotBuiltIsUnbuilt() throws {
    let registry = Provers([Answering<Ask>(name: "ask", owned: .unbuilt, proof: try anyProof())])
    #expect(try asked(registry, Lemma(Ask(name: "a"))) == .unbuilt)
}

@Test
func aRequestNoProverOrTwoProversOwnStopsTheRun() throws {
    let p = try anyProof()
    let none = Provers([Answering<Ask>(name: "ask", owned: .rule, proof: p)])
    #expect(throws: ProversError.owners(lemma: "b", provers: [])) { _ = try asked(none, Lemma(Tell(name: "b"))) }
    let two = Provers([
        Answering<Ask>(name: "ask", owned: .rule, proof: p),
        Answering<Ask>(name: "again", owned: .unbuilt, proof: p),
    ])
    #expect(throws: ProversError.owners(lemma: "a", provers: ["ask", "again"])) { _ = try asked(
        two,
        Lemma(Ask(name: "a")),
    ) }
}

/// A constant's `@def` is routed as a lemma is: to the one prover defining the constant.
@Test
func theRegistryHandsEachConstantsDefinitionToTheProverThatDefinesIt() throws {
    var t = Table()
    let p = try t.intern(.folBottom)
    let registry = Provers([
        Answering<Ask>(name: "T.d", owned: .rule, proof: p),
        Answering<Tell>(name: "T.e", owned: .unbuilt, proof: p),
    ])
    #expect(try registry.define(Defined(.zf, "T.d", .object), [], in: &t) == .statement(p))
    #expect(try registry.define(Defined(.zf, "T.e", .object), [], in: &t) == .unbuilt)
    #expect(throws: ProversError.owners(lemma: "T.f_DEF", provers: [])) {
        _ = try registry.define(Defined(.zf, "T.f", .object), [], in: &t)
    }
}
