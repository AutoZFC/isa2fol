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

    func fixing(_ T: IRType, proposition: Bool = false) -> ProofScope {
        var s = self
        s.terms = terms.source(T, proposition: proposition)
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
        let top: Bool
    }

    var terms: Terms
    var steps: [Key: NodeID] = [:]
}

private let axioms = Dictionary(uniqueKeysWithValues: Axiom.all.map { ($0.name, $0) })
private let termClass = "IFOL.term"

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

private enum LogicRule {
    case conjI, conjunct1, conjunct2, disjI1, disjI2, disjE, impI, mp, falseE, allI, spec, exE, refl, eqReflection
    case classical, iffReflection

    init?(_ a: Axiom) {
        switch a {
        case .ifol(.conjI): self = .conjI
        case .ifol(.conjunct1): self = .conjunct1
        case .ifol(.conjunct2): self = .conjunct2
        case .ifol(.disjI1): self = .disjI1
        case .ifol(.disjI2): self = .disjI2
        case .ifol(.disjE): self = .disjE
        case .ifol(.impI): self = .impI
        case .ifol(.mp): self = .mp
        case .ifol(.falseE): self = .falseE
        case .ifol(.allI): self = .allI
        case .ifol(.spec): self = .spec
        case .ifol(.exE): self = .exE
        case .ifol(.refl): self = .refl
        case .ifol(.eqReflection): self = .eqReflection
        case .fol(.classical): self = .classical
        case .ifol(.iffReflection): self = .iffReflection
        case .ifol(.subst), .ifol(.exI), .zf: return nil
        }
    }

    var premises: Int {
        switch self {
        case .refl: return 0
        case .conjunct1, .conjunct2, .disjI1, .disjI2, .impI, .falseE, .allI, .spec, .eqReflection, .classical, .iffReflection:
            return 1
        case .conjI, .mp, .exE: return 2
        case .disjE: return 3
        }
    }
}

private enum Rule {
    case pure(PureRule)
    case logic(Axiom, LogicRule)

    init?(_ name: String) {
        if let r = PureRule(rawValue: name) {
            self = .pure(r)
        } else if let a = axioms[name], let r = LogicRule(a) {
            self = .logic(a, r)
        } else {
            return nil
        }
    }

    var name: String {
        switch self {
        case let .pure(r): return r.rawValue
        case let .logic(a, _): return a.name
        }
    }

    var premises: Int {
        switch self {
        case let .pure(r): return r.premises
        case let .logic(_, r): return r.premises
        }
    }

    /// ⚠ `exE`'S STEP BINDS ITS WITNESS OVER ITS MINOR PREMISE: built at the premises themselves, a premise holding a
    /// hypothesis would be read under one binder too many. It is its closed proof, applied to them.
    var bindsOverPremises: Bool {
        guard case .logic(_, .exE) = self else { return false }
        return true
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
    private var proofs: [Instance: (statement: NodeID, proof: NodeID)] = [:]
    private var claims: [TheoremKey: String?] = [:]
    private var readAt: [TheoremKey: [IRType]] = [:]
    private var definienda: [String: Definiendum] = [:]
    private var classAxioms: [TypeClass: String]?

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
            let (statement, proof) = try prove(theorem.key, at: try types(of: theorem.key))
            return .proved(statement: statement, proof: proof)
        } catch let refusal as ReaderRefusal {
            return .refused(refusal)
        }
    }

    private mutating func types(of key: TheoremKey) throws -> [IRType] {
        if let types = readAt[key] { return types }
        let tfrees = try typeVariables(of: Theorem(key))
        var types = tfrees.map(IRType.variable)
        if !tfrees.isEmpty {
            let stated = try statement(Instance(source: .theorem(key), types: types))
            if restrictedToTerm(stated) == Set(tfrees) { types = tfrees.map { _ in .i } }
        }
        readAt[key] = types
        return types
    }

    private func restrictedToTerm(_ statement: NodeID) -> Set<String> {
        var x = statement, restricted: Set<String> = []
        while case let .ifolAll(_, body) = table[x] { x = body }
        while case let .folImplies(premise, rest) = table[x], case let .isaOfClass(T, c) = table[premise] {
            guard case let .variable(v) = T, c.name == termClass else { return [] }
            restricted.insert(v)
            x = rest
        }
        return restricted
    }

    private mutating func prove(_ key: TheoremKey, at types: [IRType]) throws -> (statement: NodeID, proof: NodeID) {
        let instance = Instance(source: .theorem(key), types: types)
        if let proved = proofs[instance] { return proved }
        let proved = try located(key.path) {
            let (e, proof) = try decode.proofFile(try corpus.file(key))
            var f = FileProof(terms: try Terms(decode: decode, constants: constants, classes: classes, file: e, at: types))
            let root = try f.terms.statement(e.prop, in: &table)
            let body = try step(proof, ProofScope(f.terms.closure), &f, top: true)
            let p = try f.terms.close(body, Node.isaAllIntro, in: &table)
            guard table.conclusion(of: p) == root else {
                throw MalformedExport.unproved(statement: root, conclusion: table.conclusion(of: p))
            }
            return (statement: root, proof: p)
        }
        proofs[instance] = proved
        return proved
    }

    /// ⚠ A BOX IS NAMED BY ITS CONTENT, NEVER ITS SERIAL: a serial names a box only within one build of the export.
    private mutating func claim(_ key: TheoremKey) throws -> String? {
        if let c = claims[key] { return c }
        var c: String?
        if let name = corpus.names[key] {
            c = try claimName(name)
        } else {
            let read = try types(of: key)
            let stated = try statement(Instance(source: .theorem(key), types: read))
            if spineLetters(stated, in: table) > 0 {
                let proof = try prove(key, at: read).proof
                c = "\(key.theory.split(separator: ".").last!).BOX_\(fingerprint(proof, table))"
            }
        }
        claims[key] = c
        return c
    }

    private mutating func step(_ body: Body, _ s: ProofScope, _ f: inout FileProof, top: Bool = false) throws -> NodeID {
        let key = FileProof.Key(body: body, scope: s, top: top)
        if let p = f.steps[key] { return p }
        let spine = try decode.proofSpine(body)
        var p: NodeID, arguments = spine.arguments[...]
        if case let .axiom(name, types) = spine.node, let rule = Rule(name) {
            (p, arguments) = try applied(rule, try types.map(f.terms.irType), arguments, s, &f)
        } else if case let .axiom(name, types) = spine.node, let d = constants.defined(byAxiom: name) {
            (p, arguments) = try definition(name, try definiendum(name, d), try types.map(f.terms.irType), arguments, s, &f)
        } else {
            p = try head(spine.node, s, &f, top: top && arguments.isEmpty)
        }
        for argument in arguments {
            switch argument {
            case let .term(x):
                let concluded = table.conclusion(of: p).map { table[$0] }, T: IRType
                if case let .ifolAll(U, _)? = concluded { T = U } else if case .isaPropAll? = concluded { T = .o } else {
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

    private mutating func head(_ h: ProofHead, _ s: ProofScope, _ f: inout FileProof, top: Bool = false) throws -> NodeID {
        switch h {
        case .nop:
            throw ReaderRefusal.omittedProof
        case let .bound(k):
            return try hypothesis(k, s)
        case let .termAbstraction(T, p):
            let U = try f.terms.irType(T)
            guard U == .o, !top else { return try table.intern(.isaAllIntro(U, body: try step(p, s.fixing(U), &f, top: top))) }
            return try table.intern(.isaPropIntro(body: try step(p, s.fixing(U, proposition: true), &f)))
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
            guard let name = try claim(key) else { return try prove(key, at: instance.types).proof }
            let read = try types(of: key), root = try statement(instance)
            if instance.types != read, !instance.types.contains(where: mentionsTypeVariable), spineLetters(root, in: table) == 0 {
                return try prove(key, at: instance.types).proof
            }
            if citedAs[name] == nil {
                citedAs[name] = Theorem(key)
                cited.append(Theorem(key))
            }
            let types = instance.types == read && read.allSatisfy { $0 == .i } ? [] : instance.types
            return try table.intern(.use(.theorem(name), types, root))
        }
    }

    private mutating func applied(_ rule: Rule, _ types: [IRType], _ arguments: ArraySlice<ProofArgument>, _ s: ProofScope,
                                  _ f: inout FileProof) throws -> (NodeID, ArraySlice<ProofArgument>) {
        var stated = try statement(Instance(source: .axiom(rule.name), types: types)), rest = arguments
        while case let .folImplies(premise, body) = table[stated], case .isaOfClass = table[premise] {
            guard case .proof? = rest.first else { throw MalformedExport.applicationArity(rule.name, expected: 1, found: 0) }
            rest = rest.dropFirst()
            stated = body
        }
        var terms: [NodeID] = []
        while let (T, body) = termBinder(stated) {
            guard case let .term(x)? = rest.first else {
                throw MalformedExport.applicationArity(rule.name, expected: terms.count + 1, found: terms.count)
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
        if premises.count == antecedents.count, !rule.bindsOverPremises {
            let p = try ruleStep(rule, terms, premises)
            return (try concluding(conclusion, p), rest)
        }
        let n = antecedents.count
        let hyps = try antecedents.indices.map { try table.intern(.hyp(n - 1 - $0, antecedents[$0])) }
        let step = try ruleStep(rule, terms, hyps)
        var closed = try concluding(conclusion, step)
        for a in antecedents.reversed() { closed = try table.intern(.folImpliesIntro(a, body: closed)) }
        for q in premises { closed = try table.intern(.folImpliesElim(closed, q)) }
        return (closed, rest)
    }

    private mutating func definition(_ axiom: String, _ d: Definiendum, _ types: [IRType], _ arguments: ArraySlice<ProofArgument>,
                                     _ s: ProofScope, _ f: inout FileProof) throws -> (NodeID, ArraySlice<ProofArgument>) {
        let stated = try statement(Instance(source: .axiom(axiom), types: types))
        var at = stated, terms: [NodeID] = [], rest = arguments
        while case let .term(x)? = rest.first, let (T, body) = termBinder(at) {
            let term = try f.terms.term(x, T, s.terms, in: &table)
            terms.append(term)
            at = try instantiate(body, with: term, in: &table)
            rest = rest.dropFirst()
        }
        return (try table.intern(.isaDefinition(axiom, of: d, types, stated, args: terms)), rest)
    }

    private func concluding(_ conclusion: NodeID, _ p: NodeID) throws -> NodeID {
        guard table.conclusion(of: p) == conclusion else {
            throw MalformedExport.unproved(statement: conclusion, conclusion: table.conclusion(of: p))
        }
        return p
    }

    private mutating func ruleStep(_ rule: Rule, _ terms: [NodeID], _ premises: [NodeID]) throws -> NodeID {
        switch rule {
        case let .pure(r): return try pureStep(r, terms, premises)
        case let .logic(_, r): return try logicStep(r, terms, premises)
        }
    }

    private mutating func logicStep(_ rule: LogicRule, _ terms: [NodeID], _ premises: [NodeID]) throws -> NodeID {
        switch rule {
        case .conjI: return try table.intern(.folAndIntro(premises[0], premises[1]))
        case .conjunct1: return try table.intern(.folAndElimL(premises[0]))
        case .conjunct2: return try table.intern(.folAndElimR(premises[0]))
        case .disjI1: return try table.intern(.folOrIntroL(premises[0], terms[1]))
        case .disjI2: return try table.intern(.folOrIntroR(terms[0], premises[0]))
        case .disjE: return try table.intern(.folOrElim(premises[0], premises[1], premises[2]))
        case .impI, .allI, .eqReflection: return premises[0]
        case .mp: return try table.intern(.folImpliesElim(premises[0], premises[1]))
        case .falseE: return try table.intern(.folBottomElim(premises[0], terms[0]))
        case .spec: return try table.intern(.isaAllElim(premises[0], terms[1]))
        case .exE:
            guard let major = table.conclusion(of: premises[0]), case let .ifolEx(T, body) = table[major],
                  case let .hyp(k, minor) = table[premises[1]] else { throw TableError.principalConnective(premises[0]) }
            let lifted = try table.intern(.hyp(k + 1, try shift(minor, by: 1, in: &table)))
            let atWitness = try table.intern(.isaAllElim(lifted, try table.intern(.isaBound(0, T))))
            let concluded = try table.intern(.folImpliesElim(atWitness, try table.intern(.hyp(0, body))))
            return try table.intern(.isaExElim(T, premises[0], body: concluded))
        case .refl: return try table.intern(.isaReflexive(terms[0]))
        case .classical: return try table.intern(.isaClassical(terms[0], premises[0]))
        case .iffReflection: return try table.intern(.isaIffReflection(terms[0], terms[1], premises[0]))
        }
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
        guard let entry = corpus.axioms[name] else { throw MalformedExport.undeclaredAxiom(name) }
        guard !families.isFoundation(entry.theory) else { throw DialectGap.axiom(name) }
        return .theoryAxiom(name)
    }

    private mutating func use(_ cited: Cited, _ instance: Instance) throws -> NodeID {
        try table.intern(.use(cited, instance.types, try statement(instance)))
    }

    mutating func definition(of x: Definiendum) throws -> NodeID {
        let axiom = try self.axiom(defining: x)
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        let e = try located(entry.file) { try decode.axiom(entry.body) }
        return try statement(Instance(source: .axiom(axiom), types: e.tfrees.map(IRType.variable)))
    }

    mutating func definition(of d: Defined, at T: IRType) throws -> Definition {
        let axiom = try self.axiom(defining: .constant(d))
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        return try located(entry.file) {
            let e = try decode.axiom(entry.body)
            let (type, lhs, rhs) = try equation(axiom, e)
            let (head, parameters) = try decode.spine(lhs)
            guard case let .constant(c, _) = head, c == d.name else { throw MalformedExport.notADefinition(axiom) }
            let names = try parameters.map { p in
                let (h, arguments) = try decode.spine(p)
                guard case let .free(name, _) = h, arguments.isEmpty else { throw MalformedExport.notADefinition(axiom) }
                return name
            }
            guard names == e.frees.map(\.0) else { throw MalformedExport.notADefinition(axiom) }
            let declared = try e.frees.reversed().reduce(try type.irType()) { U, free in .fn(try free.1.irType(), U) }
            var bound: [String: IRType] = [:]
            guard match(declared, T, &bound) else { throw MalformedExport.notADefinition(axiom) }
            let instance = try e.tfrees.map { v in
                guard let U = bound[v] else { throw MalformedExport.notADefinition(axiom) }
                return U
            }
            var terms = try Terms(decode: decode, constants: constants, classes: classes, file: e, at: instance)
            let body = try terms.term(rhs, try terms.irType(type), terms.closure, in: &table)
            let definiens = try terms.close(body, Node.isaAbs, in: &table)
            return Definition(defines: .constant(d), type: T, axiomTypes: instance, parameters: names.count, definiens: definiens)
        }
    }

    mutating func definition(of k: TypeClass, at T: IRType) throws -> Definition {
        let axiom = try self.axiom(defining: .ofClass(k))
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        return try located(entry.file) {
            let e = try decode.axiom(entry.body)
            let (type, lhs, rhs) = try equation(axiom, e)
            guard case let .ofclass(c, .tfree(v, _)) = try decode.spine(lhs).head, c == k.name, [v] == e.tfrees, e.frees.isEmpty else {
                throw MalformedExport.notADefinition(axiom)
            }
            var terms = try Terms(decode: decode, constants: constants, classes: classes, file: e, at: [T])
            let U = try terms.irType(type)
            let definiens = try terms.term(rhs, U, terms.closure, in: &table)
            return Definition(defines: .ofClass(k), type: U, axiomTypes: [T], parameters: 0, definiens: definiens)
        }
    }

    private mutating func axiom(defining x: Definiendum) throws -> String {
        switch x {
        case let .constant(d):
            guard let axiom = constants[d.name]?.definition else { throw MalformedExport.undeclaredConstant(d.name) }
            return axiom
        case let .ofClass(k):
            if classAxioms == nil {
                var found: [TypeClass: String] = [:]
                for axiom in corpus.axioms.keys.sorted() {
                    guard let d = constants.defined(byAxiom: axiom), case let .ofClass(c) = try definiendum(axiom, d) else { continue }
                    guard found.updateValue(axiom, forKey: c) == nil else { throw MalformedExport.duplicateDefinition(c.name) }
                }
                classAxioms = found
            }
            guard let axiom = classAxioms?[k] else { throw MalformedExport.undefinedClass(k.name) }
            return axiom
        }
    }

    private mutating func definiendum(_ axiom: String, _ d: Defined) throws -> Definiendum {
        if let x = definienda[axiom] { return x }
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        let x = try located(entry.file) { () throws -> Definiendum in
            let head = try decode.spine(try equation(axiom, try decode.axiom(entry.body)).lhs).head
            if case let .ofclass(c, _) = head { return .ofClass(try classes.typeClass(c)) }
            guard case let .constant(c, _) = head, c == d.name else { throw MalformedExport.notADefinition(axiom) }
            return .constant(d)
        }
        definienda[axiom] = x
        return x
    }

    private func equation(_ axiom: String, _ e: Envelope) throws -> (type: IsaType, lhs: Body, rhs: Body) {
        let (head, sides) = try decode.spine(e.prop)
        guard case let .constant("Pure.eq", types) = head, types.count == 1, sides.count == 2 else {
            throw MalformedExport.notADefinition(axiom)
        }
        return (types[0], sides[0], sides[1])
    }

    private func termBinder(_ formula: NodeID) -> (IRType, NodeID)? {
        if case let .ifolAll(T, body) = table[formula] { return (T, body) }
        if case let .isaPropAll(body) = table[formula] { return (.o, body) }
        return nil
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
    let defines: Definiendum
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
            var met: Definition?
            if case let .isaConst(.defined(d), T, _) = table[id], reached.insert(Reached(defines: .constant(d), type: T)).inserted {
                met = try definition(of: d, at: T)
            } else if case let .isaOfClass(T, k) = table[id], reached.insert(Reached(defines: .ofClass(k), type: T)).inserted {
                met = try definition(of: k, at: T)
            }
            if let definition = met {
                definitions.append(definition)
                work.append(definition.definiens)
            }
            table[id].forEachChild { c, _ in work.append(c) }
        }
        return Unit(table: table, statements: statements, definitions: definitions, unread: unread)
    }
}
