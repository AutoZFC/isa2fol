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
    case classFact
    case refused(ReaderRefusal)
}

struct ProofScope: Hashable {
    enum Hypothesis: Hashable {
        case formula(NodeID, depth: Int)
        case classPremise(String)
    }

    private(set) var terms: Scope
    private(set) var hypotheses: [Hypothesis] = []

    init(_ terms: Scope) { self.terms = terms }

    func fixing(_ T: IRType) -> ProofScope {
        var s = self
        s.terms = terms.source(T)
        return s
    }

    func assuming(_ h: Hypothesis) -> ProofScope {
        var s = self
        s.hypotheses.append(h)
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

private enum Proved {
    case claim(NodeID, classPremises: Int, proof: NodeID)
    case classFact(String)
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
    private var statements: [Instance: Proposition] = [:]
    private var boxes: [Instance: (NodeID, absorb: Int)] = [:]

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
            switch try prove(theorem.key, at: e.tfrees.map(IRType.variable)) {
            case let .claim(root, _, proof): return .proved(statement: root, proof: proof)
            case .classFact: return .classFact
            }
        } catch let refusal as ReaderRefusal {
            return .refused(refusal)
        }
    }

    private mutating func prove(_ key: TheoremKey, at types: [IRType]) throws -> Proved {
        try located(key.path) {
            let (e, proof) = try decode.proofFile(try corpus.file(key))
            var f = FileProof(terms: try Terms(decode: decode, constants: constants, file: e, at: types))
            switch try f.terms.statement(e.prop, classes, in: &table) {
            case let .classFact(c):
                return .classFact(c)
            case let .claim(root, n):
                let body = try step(proof, ProofScope(f.terms.closure), &f)
                let p = try f.terms.close(body, Node.isaAllIntro, in: &table)
                guard table.conclusion(of: p) == root else {
                    throw MalformedExport.unproved(statement: root, conclusion: table.conclusion(of: p))
                }
                return .claim(root, classPremises: n, proof: p)
            }
        }
    }

    private mutating func step(_ body: Body, _ s: ProofScope, _ f: inout FileProof) throws -> NodeID {
        let key = FileProof.Key(body: body, scope: s)
        if let p = f.steps[key] { return p }
        let spine = try decode.proofSpine(body)
        var (p, absorb) = try head(spine.node, s, &f)
        for argument in spine.arguments {
            switch argument {
            case let .term(x):
                guard case let .ifolAll(T, _)? = table.conclusion(of: p).map({ table[$0] }) else {
                    throw TableError.principalConnective(p)
                }
                let term = try f.terms.term(x, T, s.terms, in: &table)
                p = try table.intern(.isaAllElim(p, term))
            case let .proof(q):
                if absorb > 0 {
                    absorb -= 1
                    continue
                }
                let premise = try step(q, s, &f)
                p = try table.intern(.folImpliesElim(p, premise))
            }
        }
        f.steps[key] = p
        return p
    }

    private mutating func head(_ h: ProofHead, _ s: ProofScope, _ f: inout FileProof) throws -> (NodeID, absorb: Int) {
        switch h {
        case .nop:
            throw ReaderRefusal.omittedProof
        case let .bound(k):
            return (try hypothesis(k, s), 0)
        case let .termAbstraction(T, p):
            let U = try f.terms.irType(T)
            let body = try step(p, s.fixing(U), &f)
            return (try table.intern(.isaAllIntro(U, body: body)), 0)
        case let .hypothesisAbstraction(x, p):
            if case let (.ofclass(c), []) = try decode.spine(x) {
                try classes.absorb(c)
                return (try step(p, s.assuming(.classPremise(c)), &f), 0)
            }
            let A = try f.terms.proposition(x, s.terms, in: &table)
            let body = try step(p, s.assuming(.formula(A, depth: s.terms.depth)), &f)
            return (try table.intern(.folImpliesIntro(A, body: body)), 0)
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

    private mutating func use(_ name: String, _ instance: Instance) throws -> (NodeID, absorb: Int) {
        switch try statement(instance) {
        case let .claim(root, n): return (try table.intern(.use(name, instance.types, root)), n)
        case let .classFact(c): throw ReaderRefusal.ofclass(c)
        }
    }

    private mutating func box(_ key: TheoremKey, _ instance: Instance) throws -> (NodeID, absorb: Int) {
        if let b = boxes[instance] { return b }
        switch try prove(key, at: instance.types) {
        case let .claim(_, n, proof):
            boxes[instance] = (proof, n)
            return (proof, n)
        case let .classFact(c):
            throw ReaderRefusal.ofclass(c)
        }
    }

    private mutating func hypothesis(_ k: Int, _ s: ProofScope) throws -> NodeID {
        let hs = s.hypotheses
        guard k >= 0, k < hs.count else { throw MalformedExport.unboundHypothesis(k) }
        let position = hs.count - 1 - k
        switch hs[position] {
        case let .classPremise(c):
            throw ReaderRefusal.ofclass(c)
        case let .formula(A, depth):
            let index = hs[(position + 1)...].filter { if case .formula = $0 { true } else { false } }.count
            let here = try shift(A, by: s.terms.depth - depth, in: &table)
            return try table.intern(.hyp(index, here))
        }
    }

    private mutating func statement(_ instance: Instance) throws -> Proposition {
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
            var terms = try Terms(decode: decode, constants: constants, file: e, at: instance.types)
            return try terms.statement(e.prop, classes, in: &table)
        }
        statements[instance] = p
        return p
    }
}
