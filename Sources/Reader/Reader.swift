import IR
import YXML

public struct Theorem: Hashable, Sendable, CustomStringConvertible {
    public let theory: String
    public let serial: Int

    init(_ key: TheoremKey) {
        theory = key.theory
        serial = key.serial
    }

    var key: TheoremKey { TheoremKey(theory: theory, serial: serial) }
    public var description: String { key.path }
}

@frozen public enum Outcome: Equatable, Sendable {
    case proved(statement: NodeID, proof: NodeID)
    case refused(ReaderRefusal)
}

struct ProofScope: Hashable {
    struct Hypothesis: Hashable {
        let formula: NodeID
        let depth: Int
    }

    private(set) var terms: Scope
    private(set) var hypotheses: [Hypothesis] = []

    init(_ terms: Scope) { self.terms = terms }

    func fixing(_ T: IRType) -> ProofScope {
        var s = self
        s.terms = terms.source(T)
        return s
    }

    func assuming(_ A: NodeID) -> ProofScope {
        var s = self
        s.hypotheses.append(Hypothesis(formula: A, depth: terms.depth))
        return s
    }
}

private struct FileProof {
    struct Key: Hashable {
        let body: Body
        let scope: ProofScope
    }

    var terms: Terms
    var steps: [Key: NodeID] = [:]
}

public struct Reader {
    private enum Source: Hashable {
        case theorem(TheoremKey)
        case axiom(String)
    }

    private struct Instance: Hashable {
        let source: Source
        let types: [IRType]
    }

    public private(set) var table = Table()
    public let population: [Theorem]
    public private(set) var cited: [Theorem] = []
    private var citedOnce: Set<TheoremKey> = []
    private let decode: Decode
    private let constants: Constants
    private let classes: Classes
    private let corpus: Corpus
    private var statements: [Instance: NodeID] = [:]
    private var boxes: [Instance: NodeID] = [:]

    public init(_ export: Export) throws {
        var export = export
        corpus = try export.load()
        decode = Decode(forest: export.forest)
        constants = export.constants
        classes = export.classes
        population = corpus.names.keys.filter { session(of: $0.theory) != nil }
            .sorted { ($0.theory, $0.serial) < ($1.theory, $1.serial) }
            .map(Theorem.init)
    }

    public func name(of theorem: Theorem) -> String? { corpus.names[theorem.key] }

    public mutating func read(_ theorem: Theorem) throws -> Outcome {
        do {
            let (e, _) = try located(theorem.key.path) { try decode.proofFile(try corpus.file(theorem.key)) }
            let (statement, proof) = try prove(theorem.key, at: e.tfrees.map(IRType.variable))
            return .proved(statement: statement, proof: proof)
        } catch let refusal as ReaderRefusal {
            return .refused(refusal)
        }
    }

    private mutating func prove(_ key: TheoremKey, at types: [IRType]) throws -> (statement: NodeID, proof: NodeID) {
        try located(key.path) {
            let (e, proof) = try decode.proofFile(try corpus.file(key))
            var f = FileProof(terms: try Terms(decode: decode, constants: constants, classes: classes, file: e, at: types))
            let root = try f.terms.statement(e.prop, in: &table)
            let body = try step(proof, ProofScope(f.terms.closure), &f)
            let p = try f.terms.close(body, Node.isaAllIntro, in: &table)
            guard table.conclusion(of: p) == root else {
                throw MalformedExport.unproved(statement: root, conclusion: table.conclusion(of: p))
            }
            return (root, p)
        }
    }

    private mutating func step(_ body: Body, _ s: ProofScope, _ f: inout FileProof) throws -> NodeID {
        let key = FileProof.Key(body: body, scope: s)
        if let p = f.steps[key] { return p }
        let spine = try decode.proofSpine(body)
        var p = try head(spine.node, s, &f)
        for argument in spine.arguments {
            switch argument {
            case let .term(x):
                guard case let .ifolAll(T, _)? = table.conclusion(of: p).map({ table[$0] }) else {
                    throw TableError.principalConnective(p)
                }
                let term = try f.terms.term(x, T, s.terms, in: &table)
                p = try table.intern(.isaAllElim(p, term))
            case let .proof(q):
                p = try table.intern(.folImpliesElim(p, try step(q, s, &f)))
            }
        }
        f.steps[key] = p
        return p
    }

    private mutating func head(_ h: ProofHead, _ s: ProofScope, _ f: inout FileProof) throws -> NodeID {
        switch h {
        case .nop:
            throw ReaderRefusal.omittedProof
        case let .bound(k):
            return try hypothesis(k, s)
        case let .termAbstraction(T, p):
            let U = try f.terms.irType(T)
            let body = try step(p, s.fixing(U), &f)
            return try table.intern(.isaAllIntro(U, body: body))
        case let .hypothesisAbstraction(x, p):
            let A = try f.terms.proposition(x, s.terms, in: &table)
            let body = try step(p, s.assuming(A), &f)
            return try table.intern(.folImpliesIntro(A, body: body))
        case .hypothesis:
            throw MalformedExport.freeHypothesis
        case let .axiom(name, types):
            let instance = Instance(source: .axiom(name), types: try types.map(f.terms.irType))
            return try use(name, instance)
        case let .ofclass(_, c):
            throw ReaderRefusal.ofclass(c)
        case let .oracle(name, _):
            throw ReaderRefusal.oracle(name)
        case let .theorem(c):
            let key = TheoremKey(theory: c.theory, serial: c.serial)
            let instance = Instance(source: .theorem(key), types: try c.types.map(f.terms.irType))
            guard let name = corpus.names[key] else { return try box(key, instance) }
            if citedOnce.insert(key).inserted { cited.append(Theorem(key)) }
            return try use(try claimName(name), instance)
        }
    }

    private mutating func use(_ name: String, _ instance: Instance) throws -> NodeID {
        try table.intern(.use(name, instance.types, try statement(instance)))
    }

    private mutating func box(_ key: TheoremKey, _ instance: Instance) throws -> NodeID {
        if let b = boxes[instance] { return b }
        let proof = try prove(key, at: instance.types).proof
        boxes[instance] = proof
        return proof
    }

    private mutating func hypothesis(_ k: Int, _ s: ProofScope) throws -> NodeID {
        let hs = s.hypotheses
        guard k >= 0, k < hs.count else { throw MalformedExport.unboundHypothesis(k) }
        let h = hs[hs.count - 1 - k]
        return try table.intern(.hyp(k, try shift(h.formula, by: s.terms.depth - h.depth, in: &table)))
    }

    private mutating func statement(_ instance: Instance) throws -> NodeID {
        if let p = statements[instance] { return p }
        let (path, e): (String, Envelope)
        switch instance.source {
        case let .theorem(key):
            path = key.path
            e = try located(path) { try decode.proofFile(try corpus.file(key)).0 }
        case let .axiom(name):
            guard let axiom = corpus.axioms[name] else { throw MalformedExport.undeclaredAxiom(name) }
            path = axiom.file
            e = try located(path) { try decode.axiom(axiom.body) }
        }
        let p = try located(path) {
            var terms = try Terms(decode: decode, constants: constants, classes: classes, file: e, at: instance.types)
            return try terms.statement(e.prop, in: &table)
        }
        statements[instance] = p
        return p
    }
}
