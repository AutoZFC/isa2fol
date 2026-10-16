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

private let axioms = Dictionary(uniqueKeysWithValues: Axiom.all.map { ($0.name, $0) })

private enum PureRule: String {
    case reflexive = "Pure.reflexive", symmetric = "Pure.symmetric", transitive = "Pure.transitive"
    case combination = "Pure.combination", abstractRule = "Pure.abstract_rule"
    case equalIntr = "Pure.equal_intr", equalElim = "Pure.equal_elim"

    var premises: Int {
        switch self {
        case .reflexive: return 0
        case .symmetric, .abstractRule: return 1
        case .transitive, .combination, .equalIntr, .equalElim: return 2
        }
    }
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
    private(set) var citedAs: [String: Theorem] = [:]
    private let decode: Decode
    private let constants: Constants
    private let classes: Classes
    private let families: Families
    private let corpus: Corpus
    private var statements: [Instance: NodeID] = [:]
    private var boxes: [Instance: NodeID] = [:]

    public init(_ export: Export) throws {
        var export = export
        corpus = try export.load()
        decode = Decode(forest: export.forest)
        constants = export.constants
        classes = export.classes
        families = export.families
        population = corpus.names.keys.filter { session(of: $0.theory) != nil }
            .sorted { ($0.theory, $0.serial) < ($1.theory, $1.serial) }
            .map(Theorem.init)
    }

    public func name(of theorem: Theorem) -> String? { corpus.names[theorem.key] }

    func typeVariables(of theorem: Theorem) throws -> [String] {
        try located(theorem.key.path) { try decode.proofFile(try corpus.file(theorem.key)).0.tfrees }
    }

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
        var p: NodeID, arguments = spine.arguments[...]
        if case let .axiom(name, types) = spine.node, let rule = PureRule(rawValue: name) {
            (p, arguments) = try pure(rule, try types.map(f.terms.irType), arguments, s, &f)
        } else {
            p = try head(spine.node, s, &f)
        }
        for argument in arguments {
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
            return try use(try cited(axiom: name), instance)
        case let .ofclass(_, c):
            throw ReaderRefusal.ofclass(c)
        case let .oracle(name, _):
            throw ReaderRefusal.oracle(name)
        case let .theorem(c):
            let key = TheoremKey(theory: c.theory, serial: c.serial)
            let instance = Instance(source: .theorem(key), types: try c.types.map(f.terms.irType))
            guard let name = corpus.names[key] else { return try box(key, instance) }
            let claim = try claimName(name)
            if citedAs.updateValue(Theorem(key), forKey: claim) == nil { cited.append(Theorem(key)) }
            return try use(.theorem(claim), instance)
        }
    }

    private mutating func pure(_ rule: PureRule, _ types: [IRType], _ arguments: ArraySlice<ProofArgument>, _ s: ProofScope,
                               _ f: inout FileProof) throws -> (NodeID, ArraySlice<ProofArgument>) {
        var stated = try statement(Instance(source: .axiom(rule.rawValue), types: types)), rest = arguments
        var terms: [NodeID] = []
        while case let .ifolAll(T, body) = table[stated] {
            guard case let .term(x)? = rest.first else {
                throw MalformedExport.applicationArity(rule.rawValue, expected: terms.count + 1, found: terms.count)
            }
            let term = try f.terms.term(x, T, s.terms, in: &table)
            terms.append(term)
            stated = try instantiate(body, with: term, in: &table)
            rest = rest.dropFirst()
        }
        var antecedents: [NodeID] = [], conclusion = stated
        while antecedents.count < rule.premises {
            guard case let .folImplies(a, c) = table[conclusion] else { throw TableError.principalConnective(conclusion) }
            antecedents.append(a)
            conclusion = c
        }
        var premises: [NodeID] = []
        while premises.count < antecedents.count, case let .proof(q)? = rest.first {
            let premise = try step(q, s, &f)
            guard table.conclusion(of: premise) == antecedents[premises.count] else {
                throw MalformedExport.unproved(statement: antecedents[premises.count], conclusion: table.conclusion(of: premise))
            }
            premises.append(premise)
            rest = rest.dropFirst()
        }
        if premises.count == antecedents.count {
            let p = try pureStep(rule, terms, premises)
            guard table.conclusion(of: p) == conclusion else {
                throw MalformedExport.unproved(statement: conclusion, conclusion: table.conclusion(of: p))
            }
            return (p, rest)
        }
        let n = antecedents.count
        let hyps = try antecedents.indices.map { try table.intern(.hyp(n - 1 - $0, antecedents[$0])) }
        var closed = try pureStep(rule, terms, hyps)
        for a in antecedents.reversed() { closed = try table.intern(.folImpliesIntro(a, body: closed)) }
        for q in premises { closed = try table.intern(.folImpliesElim(closed, q)) }
        return (closed, rest)
    }

    private mutating func pureStep(_ rule: PureRule, _ terms: [NodeID], _ premises: [NodeID]) throws -> NodeID {
        func equated(_ p: NodeID) throws -> IRType {
            guard let c = table.conclusion(of: p), let (T, _, _) = table.sides(ofEquation: c) else {
                throw TableError.principalConnective(p)
            }
            return T
        }
        switch rule {
        case .reflexive:
            return try table.intern(.isaReflexive(terms[0]))
        case .symmetric:
            return try table.intern(.isaSymmetric(try equated(premises[0]), premises[0]))
        case .transitive:
            return try table.intern(.isaTransitive(try equated(premises[0]), premises[0], premises[1]))
        case .combination:
            return try table.intern(.isaCombination(try equated(premises[0]), premises[0], premises[1]))
        case .abstractRule:
            guard let c = table.conclusion(of: premises[0]), case let .ifolAll(T, body) = table[c],
                  let (U, _, _) = table.sides(ofEquation: body) else { throw TableError.principalConnective(premises[0]) }
            return try table.intern(.isaAbstract(.fn(T, U), premises[0]))
        case .equalIntr:
            return try table.intern(.folIffIntro(premises[0], premises[1]))
        case .equalElim:
            return try table.intern(.folIffElimL(premises[0], premises[1]))
        }
    }

    private func cited(axiom name: String) throws -> Cited {
        if let a = axioms[name] { return .axiom(a) }
        if let d = constants.defined(byAxiom: name) { return .isaDefinition(name, of: d) }
        guard let entry = corpus.axioms[name] else { throw MalformedExport.undeclaredAxiom(name) }
        guard !families.isFoundation(entry.theory) else { throw DialectGap.axiom(name) }
        return .theoryAxiom(name)
    }

    private mutating func use(_ cited: Cited, _ instance: Instance) throws -> NodeID {
        try table.intern(.use(cited, instance.types, try statement(instance)))
    }

    mutating func definition(of d: Defined) throws -> NodeID {
        guard let axiom = constants[d.name]?.definition else { throw MalformedExport.undeclaredConstant(d.name) }
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        let e = try located(entry.file) { try decode.axiom(entry.body) }
        return try statement(Instance(source: .axiom(axiom), types: e.tfrees.map(IRType.variable)))
    }

    mutating func definition(of d: Defined, at T: IRType) throws -> Definition {
        guard let axiom = constants[d.name]?.definition else { throw MalformedExport.undeclaredConstant(d.name) }
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        return try located(entry.file) {
            let e = try decode.axiom(entry.body)
            let (head, sides) = try decode.spine(e.prop)
            guard case let .constant("Pure.eq", types) = head, types.count == 1, sides.count == 2 else {
                throw MalformedExport.notADefinition(axiom)
            }
            let (lhs, parameters) = try decode.spine(sides[0])
            guard case let .constant(c, _) = lhs, c == d.name else { throw MalformedExport.notADefinition(axiom) }
            let names = try parameters.map { p in
                let (h, arguments) = try decode.spine(p)
                guard case let .free(name, _) = h, arguments.isEmpty else { throw MalformedExport.notADefinition(axiom) }
                return name
            }
            guard names == e.frees.map(\.0) else { throw MalformedExport.notADefinition(axiom) }
            let declared = try e.frees.reversed().reduce(try types[0].irType()) { U, free in .fn(try free.1.irType(), U) }
            var bound: [String: IRType] = [:]
            guard match(declared, T, &bound) else { throw MalformedExport.notADefinition(axiom) }
            let instance = try e.tfrees.map { v in
                guard let U = bound[v] else { throw MalformedExport.notADefinition(axiom) }
                return U
            }
            var terms = try Terms(decode: decode, constants: constants, classes: classes, file: e, at: instance)
            let body = try terms.term(sides[1], try terms.irType(types[0]), terms.closure, in: &table)
            let definiens = try terms.close(body, Node.isaAbs, in: &table)
            return Definition(constant: d, type: T, axiomTypes: instance, parameters: names.count, definiens: definiens)
        }
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
            guard let entry = corpus.axioms[name] else { throw MalformedExport.undeclaredAxiom(name) }
            path = entry.file
            e = try located(path) { try decode.axiom(entry.body) }
        }
        let p = try located(path) {
            var terms = try Terms(decode: decode, constants: constants, classes: classes, file: e, at: instance.types)
            return try terms.statement(e.prop, in: &table)
        }
        statements[instance] = p
        return p
    }
}

private func match(_ pattern: IRType, _ T: IRType, _ bound: inout [String: IRType]) -> Bool {
    switch pattern {
    case let .variable(v):
        if let U = bound[v] { return U == T }
        bound[v] = T
        return true
    case .i, .o:
        return pattern == T
    case let .fn(a, b):
        guard case let .fn(c, d) = T else { return false }
        return match(a, c, &bound) && match(b, d, &bound)
    }
}

private struct Reached: Hashable {
    let constant: Defined
    let type: IRType
}

extension Reader {
    public mutating func unit() throws -> Unit {
        var statements: [Statement] = [], unread: [String] = [], taken: Set<String> = []
        var definitions: [Definition] = [], reached: Set<Reached> = [], seen: Set<NodeID> = [], work: [NodeID] = []
        func take(_ theorem: Theorem, _ name: String) throws {
            guard taken.insert(name).inserted else { return }
            switch try read(theorem) {
            case let .proved(statement, proof):
                statements.append(Statement(name: name, root: statement, proof: proof, theory: theorem.theory))
                work += [proof, statement]
            case .refused:
                unread.append(name)
            }
        }
        for theorem in population { try take(theorem, try claimName(corpus.names[theorem.key]!)) }
        work.reverse()
        while let id = work.popLast() {
            guard seen.insert(id).inserted else { continue }
            if case let .use(.theorem(name), [], _) = table[id], let theorem = citedAs[name] { try take(theorem, name) }
            if case let .isaConst(.defined(d), T, _) = table[id], reached.insert(Reached(constant: d, type: T)).inserted {
                let definition = try definition(of: d, at: T)
                definitions.append(definition)
                work.append(definition.definiens)
            }
            table[id].forEachChild { c, _ in work.append(c) }
        }
        return Unit(table: table, statements: statements, definitions: definitions, unread: unread)
    }
}
