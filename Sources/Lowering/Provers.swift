import IR

@frozen
public enum ProversError: Error, Equatable {
    case owners(lemma: String, provers: [String])
}

public protocol Prover {
    var name: String { get }

    func owns(_ l: Lemma) -> Owned?
    func prove(
        _ l: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        _ theorems: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved
    func defines(_ c: Defined) -> Owned?
    func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> NodeID
}

public struct Provers: Registry {
    public init(_ provers: [Prover]) {
        self.provers = provers
    }

    public func prove(
        _ lemma: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        _ theorems: [String: NamedStatement],
        in t: inout Table,
    ) throws -> Proved {
        let (prover, owned) = try owner(lemma.name) { $0.owns(lemma) }
        switch owned {
        case .rule: return try prover.prove(lemma, statement, definitions, theorems, in: &t)
        case .unbuilt: return .unbuilt
        }
    }

    public func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> Stated {
        let (prover, owned) = try owner(c.definitionName) { $0.defines(c) }
        switch owned {
        case .rule: return .statement(try prover.define(c, definitions, in: &t))
        case .unbuilt: return .unbuilt
        }
    }

    let provers: [Prover]

    private func owner(_ name: String, _ owns: (Prover) -> Owned?) throws -> (Prover, Owned) {
        let owners = provers.filter { owns($0) != nil }
        guard owners.count == 1, let prover = owners.first, let owned = owns(prover) else {
            throw ProversError.owners(lemma: name, provers: owners.map(\.name))
        }
        return (prover, owned)
    }
}
