import IR

@frozen public enum TypingError: Error, Equatable {
    case owners(lemma: String, provers: [String])
}

public protocol Prover {
    var name: String { get }
    func owns(_ l: Lemma) -> Owned?
    func prove(_ l: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> NodeID
}

public struct Typing: Registry {
    let provers: [Prover]

    public init(provers: [Prover]) { self.provers = provers }

    public func prove(_ lemma: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> Proved {
        let owners = provers.filter { $0.owns(lemma) != nil }
        guard owners.count == 1, let prover = owners.first, let owned = prover.owns(lemma) else {
            throw TypingError.owners(lemma: lemma.name, provers: owners.map(\.name))
        }
        switch owned {
        case .rule: return .proof(try prover.prove(lemma, statement, definitions, in: &t))
        case .unbuilt: return .unbuilt
        }
    }

    static func guarded(_ x: NodeID, in t: inout Table) throws -> NodeID {
        try t.intern(.folPred("set", args: [x]))
    }
}
