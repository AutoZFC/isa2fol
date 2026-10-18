import IR
import YXML

public struct Theorem: Hashable, Sendable, CustomStringConvertible {
    init(_ key: TheoremKey) {
        theory = key.theory
        serial = key.serial
    }

    public let theory: String
    public let serial: Int

    public var description: String {
        key.path
    }

    var key: TheoremKey {
        TheoremKey(theory: theory, serial: serial)
    }
}

@frozen
public enum Outcome: Equatable, Sendable {
    case proved(statement: NodeID, proof: NodeID)
    case refused(ReaderRefusal)
}

struct ProofScope: Hashable {
    init(_ terms: Scope) {
        self.terms = terms
    }

    struct Hypothesis: Hashable {
        let formula: NodeID
        let depth: Int
    }

    private(set) var terms: Scope
    private(set) var hypotheses = [Hypothesis]()

    func fixing(_ T: IRType, proposition: Bool = false) -> ProofScope {
        var s = self
        s.terms = terms.source(T, proposition: proposition)
        return s
    }

    func hiding() -> ProofScope {
        var s = self
        s.terms = terms.unwritten()
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
    var steps = [Key: NodeID]()
}

private let axioms = Dictionary(uniqueKeysWithValues: Axiom.all.map { ($0.name, $0) })
private let termClass = "IFOL.term"

private enum PureRule: String {
    case reflexive = "Pure.reflexive"
    case symmetric = "Pure.symmetric"
    case transitive = "Pure.transitive"
    case combination = "Pure.combination"
    case abstractRule = "Pure.abstract_rule"
    case equalIntr = "Pure.equal_intr"
    case equalElim = "Pure.equal_elim"

    var premises: Int {
        switch self {
        case .reflexive: 0
        case .symmetric, .abstractRule: 1
        case .transitive, .combination, .equalIntr, .equalElim: 2
        }
    }
}

private enum LogicRule {
    case conjI
    case conjunct1
    case conjunct2
    case disjI1
    case disjI2
    case disjE
    case impI
    case mp
    case falseE
    case allI
    case spec
    case exI
    case exE
    case refl
    case eqReflection
    case classical
    case iffReflection

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
        case .ifol(.exI): self = .exI
        case .ifol(.exE): self = .exE
        case .ifol(.refl): self = .refl
        case .ifol(.eqReflection): self = .eqReflection
        case .fol(.classical): self = .classical
        case .ifol(.iffReflection): self = .iffReflection
        case .ifol(.subst), .zf: return nil
        }
    }

    var premises: Int {
        switch self {
        case .refl: 0
        case .conjunct1, .conjunct2, .disjI1, .disjI2, .impI, .falseE, .allI, .spec, .exI, .eqReflection, .classical,
             .iffReflection:
            1
        case .conjI, .mp, .exE: 2
        case .disjE: 3
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
        case .pure(let r): r.rawValue
        case .logic(let a, _): a.name
        }
    }

    var premises: Int {
        switch self {
        case .pure(let r): r.premises
        case .logic(_, let r): r.premises
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

    public private(set) var table = Table()
    public let population: [Theorem]
    public private(set) var cited = [Theorem]()

    public func name(of theorem: Theorem) -> String? {
        corpus.names[theorem.key]
    }

    public mutating func read(_ theorem: Theorem) throws -> Outcome {
        do {
            let (statement, proof) = try prove(theorem.key, at: try types(of: theorem.key))
            return .proved(statement: statement, proof: proof)
        } catch let refusal as ReaderRefusal {
            return .refused(refusal)
        }
    }

    private(set) var citedAs = [String: Theorem]()

    func typeVariables(of theorem: Theorem) throws -> [String] {
        try located(theorem.key.path) { try decode.proofFile(try corpus.file(theorem.key)).0.tfrees }
    }

    mutating func definition(of x: Definiendum) throws -> NodeID {
        let axiom = try axiom(defining: x)
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        let e = try located(entry.file) { try decode.axiom(entry.body) }
        return try statement(Instance(source: .axiom(axiom), types: e.tfrees.map(IRType.variable)))
    }

    mutating func definition(of d: Defined, at T: IRType) throws -> Definition {
        let axiom = try axiom(defining: .constant(d))
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        return try located(entry.file) {
            let e = try decode.axiom(entry.body)
            let (type, lhs, rhs) = try equation(axiom, e)
            let (head, parameters) = try decode.spine(lhs)
            guard case .constant(let c, _) = head, c == d.name else { throw MalformedExport.notADefinition(axiom) }
            let names = try parameters.map { p in
                let (h, arguments) = try decode.spine(p)
                guard
                    case .free(let name, _) = h,
                    arguments.isEmpty
                else { throw MalformedExport.notADefinition(axiom) }
                return name
            }
            guard names == e.frees.map(\.0) else { throw MalformedExport.notADefinition(axiom) }
            let declared = try e.frees.reversed().reduce(try type.irType()) { U, free in .fn(try free.1.irType(), U) }
            var bound = [String: IRType]()
            guard match(declared, T, &bound) else { throw MalformedExport.notADefinition(axiom) }
            let instance = try e.tfrees.map { v in
                guard let U = bound[v] else { throw MalformedExport.notADefinition(axiom) }
                return U
            }
            var terms = try Terms(
                decode: decode,
                constants: constants,
                classes: classes,
                file: e,
                at: instance,
                order: .stated,
            )
            let body = try terms.term(rhs, try terms.irType(type), terms.closure, in: &table)
            let definiens = try terms.close(body, Node.isaAbs, in: &table)
            return Definition(
                defines: .constant(d),
                type: T,
                axiomTypes: instance,
                parameters: names.count,
                definiens: definiens,
            )
        }
    }

    mutating func definition(of k: TypeClass, at T: IRType) throws -> Definition {
        let axiom = try axiom(defining: .ofClass(k))
        guard let entry = corpus.axioms[axiom] else { throw MalformedExport.undeclaredAxiom(axiom) }
        return try located(entry.file) {
            let e = try decode.axiom(entry.body)
            let (type, lhs, rhs) = try equation(axiom, e)
            guard
                case .ofclass(let c, .tfree(let v, _)) = try decode.spine(lhs).head, c == k.name, [v] == e.tfrees,
                e.frees.isEmpty
            else {
                throw MalformedExport.notADefinition(axiom)
            }
            var terms = try Terms(
                decode: decode,
                constants: constants,
                classes: classes,
                file: e,
                at: [T],
                order: .stated,
            )
            let U = try terms.irType(type)
            let definiens = try terms.term(rhs, U, terms.closure, in: &table)
            return Definition(defines: .ofClass(k), type: U, axiomTypes: [T], parameters: 0, definiens: definiens)
        }
    }

    private enum Source: Hashable {
        case theorem(TheoremKey)
        case axiom(String)
    }

    private struct Instance: Hashable {
        let source: Source
        let types: [IRType]
    }

    private let decode: Decode
    private let constants: Constants
    private let classes: Classes
    private let families: Families
    private let corpus: Corpus
    private var statements = [Instance: NodeID]()
    private var letterMasks = [Instance: [Bool]]()
    private var proofs = [Instance: (statement: NodeID, proof: NodeID)]()
    private var claims = [TheoremKey: String?]()
    private var readAt = [TheoremKey: [IRType]]()
    private var definienda = [String: Definiendum]()
    private var classAxioms: [TypeClass: String]?

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
        var x = statement
        var restricted = Set<String>()
        while case .ifolAll(_, let body) = table[x] { x = body }
        while case .folImplies(let premise, let rest) = table[x], case .isaOfClass(let T, let c) = table[premise] {
            guard case .variable(let v) = T, c.name == termClass else { return [] }
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
            var f = FileProof(terms: try Terms(
                decode: decode,
                constants: constants,
                classes: classes,
                file: e,
                at: types,
                order: .lettersFirst,
            ))
            letterMasks[instance] = f.terms.letters
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

    private mutating func step(
        _ body: Body,
        _ s: ProofScope,
        _ f: inout FileProof,
        top: Bool = false,
    ) throws -> NodeID {
        let key = FileProof.Key(body: body, scope: s, top: top)
        if let p = f.steps[key] { return p }
        let spine = try decode.proofSpine(body)
        if top, !spine.arguments.isEmpty || !isTermAbstraction(spine.node) {
            let types = try f.terms.hide(body, from: s.terms.depth)
            var p = try step(body, types.reduce(s) { s, _ in s.hiding() }, &f)
            for T in types.reversed() { p = try table.intern(.isaHidden(T, body: p)) }
            f.steps[key] = p
            return p
        }
        var p: NodeID
        var arguments = spine.arguments[...]
        if case .axiom(let name, let types) = spine.node, let rule = Rule(name) {
            (p, arguments) = try applied(rule, try types.map(f.terms.irType), arguments, s, &f)
        } else if case .axiom(let name, let types) = spine.node, let d = constants.defined(byAxiom: name) {
            (p, arguments) = try definition(
                name,
                try definiendum(name, d),
                try types.map(f.terms.irType),
                arguments,
                s,
                &f,
            )
        } else {
            p = try head(spine.node, s, &f, top: top && arguments.isEmpty)
            if case .theorem(let c) = spine.node {
                let instance = Instance(
                    source: .theorem(TheoremKey(theory: c.theory, serial: c.serial)),
                    types: try c.types.map(f.terms.irType),
                )
                arguments = try citedLettersFirst(arguments, try letters(of: instance))
            }
        }
        let substituting = bindsAFunction(p)
        for argument in arguments {
            switch argument {
            case .term(let x):
                let concluded = table.conclusion(of: p).map { table[$0] }
                let T: IRType
                if case .ifolAll(let U, _)? = concluded { T = U } else if case .isaPropAll? = concluded { T = .o }
                else {
                    throw TableError.principalConnective(p)
                }
                let term = try f.terms.term(x, T, s.terms, in: &table)
                if substituting, case .isaAllIntro(_, let body) = table[p] {
                    p = try instantiate(body, with: term, in: &table)
                } else {
                    p = try table.intern(.isaAllElim(p, term))
                }

            case .proof(let q):
                p = try table.intern(.folImpliesElim(p, try step(q, s, &f)))
            }
        }
        f.steps[key] = p
        return p
    }

    private func bindsAFunction(_ p: NodeID) -> Bool {
        var p = p
        while case .isaAllIntro(let T, let body) = table[p] {
            if takesAFunction(T), !mentionsTypeVariable(T) { return true }
            p = body
        }
        return false
    }

    private func isTermAbstraction(_ h: ProofHead) -> Bool {
        if case .termAbstraction = h { return true }
        return false
    }

    private mutating func letters(of instance: Instance) throws -> [Bool] {
        if let letters = letterMasks[instance] { return letters }
        return try stating(instance).letters
    }

    private func citedLettersFirst(
        _ arguments: ArraySlice<ProofArgument>,
        _ letters: [Bool],
    ) throws -> ArraySlice<ProofArgument> {
        guard letters.contains(true) else { return arguments }
        var given = [ProofArgument]()
        for a in arguments.prefix(letters.count) {
            guard case .term = a else { break }
            given.append(a)
        }
        guard !letters[given.count...].contains(true) else { throw ReaderRefusal.letterLeft }
        return ArraySlice(lettersFirst(given, Array(letters[..<given.count])) + arguments.dropFirst(given.count))
    }

    private mutating func head(
        _ h: ProofHead,
        _ s: ProofScope,
        _ f: inout FileProof,
        top: Bool = false,
    ) throws -> NodeID {
        switch h {
        case .nop:
            throw ReaderRefusal.omittedProof

        case .bound(let k):
            return try hypothesis(k, s)

        case .termAbstraction(let T, let p):
            let U = try f.terms.irType(T)
            guard U == .o, !top else { return try table.intern(.isaAllIntro(
                U,
                body: try step(p, s.fixing(U), &f, top: top),
            )) }
            return try table.intern(.isaPropIntro(body: try step(p, s.fixing(U, proposition: true), &f)))

        case .hypothesisAbstraction(let x, let p):
            let A = try f.terms.proposition(x, s.terms, in: &table)
            let body = try step(p, s.assuming(A), &f)
            return try table.intern(.folImpliesIntro(A, body: body))

        case .hypothesis:
            throw MalformedExport.freeHypothesis

        case .axiom(let name, let types):
            let instance = Instance(source: .axiom(name), types: try types.map(f.terms.irType))
            return try use(try cited(axiom: name), instance)

        case .ofclass(_, let c):
            throw ReaderRefusal.ofclass(c)

        case .oracle(let name, _):
            throw ReaderRefusal.oracle(name)

        case .theorem(let c):
            let key = TheoremKey(theory: c.theory, serial: c.serial)
            let instance = Instance(source: .theorem(key), types: try c.types.map(f.terms.irType))
            guard let name = try claim(key) else { return try prove(key, at: instance.types).proof }
            let read = try types(of: key)
            let root = try statement(instance)
            if
                instance.types != read, !instance.types.contains(where: mentionsTypeVariable), spineLetters(
                    root,
                    in: table,
                ) == 0
            {
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

    private mutating func applied(
        _ rule: Rule,
        _ types: [IRType],
        _ arguments: ArraySlice<ProofArgument>,
        _ s: ProofScope,
        _ f: inout FileProof,
    ) throws -> (NodeID, ArraySlice<ProofArgument>) {
        var stated = try statement(Instance(source: .axiom(rule.name), types: types))
        var rest = arguments
        while case .folImplies(let premise, let body) = table[stated], case .isaOfClass = table[premise] {
            guard case .proof? = rest.first else { throw MalformedExport.applicationArity(
                rule.name,
                expected: 1,
                found: 0,
            ) }
            rest = rest.dropFirst()
            stated = body
        }
        var terms = [NodeID]()
        while let (T, body) = termBinder(stated) {
            guard case .term(let x)? = rest.first else {
                throw MalformedExport.applicationArity(rule.name, expected: terms.count + 1, found: terms.count)
            }
            let term = try f.terms.term(x, T, s.terms, in: &table)
            terms.append(term)
            stated = try instantiate(body, with: term, in: &table)
            rest = rest.dropFirst()
        }
        var antecedents = [NodeID]()
        var conclusion = stated
        while antecedents.count < rule.premises {
            guard case .folImplies(let a, let c) = table[conclusion]
            else { throw TableError.principalConnective(conclusion) }
            antecedents.append(a)
            conclusion = c
        }
        var premises = [NodeID]()
        while premises.count < antecedents.count, case .proof(let q)? = rest.first {
            let premise = try step(q, s, &f)
            guard table.conclusion(of: premise) == antecedents[premises.count] else {
                throw MalformedExport.unproved(
                    statement: antecedents[premises.count],
                    conclusion: table.conclusion(of: premise),
                )
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

    private mutating func definition(
        _ axiom: String,
        _ d: Definiendum,
        _ types: [IRType],
        _ arguments: ArraySlice<ProofArgument>,
        _ s: ProofScope,
        _ f: inout FileProof,
    ) throws -> (NodeID, ArraySlice<ProofArgument>) {
        let stated = try statement(Instance(source: .axiom(axiom), types: types))
        var at = stated
        var terms = [NodeID]()
        var rest = arguments
        while case .term(let x)? = rest.first, let (T, body) = termBinder(at) {
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
        case .pure(let r): try pureStep(r, terms, premises)
        case .logic(_, let r): try logicStep(r, terms, premises)
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

        case .exI:
            guard case .isaAbs(_, let body) = table[terms[0]] else {
                throw TableError.functionArgumentNotAbstraction(terms[0])
            }
            return try table.intern(.isaExIntro(premises[0], terms[1], body: body))

        case .exE:
            guard
                let major = table.conclusion(of: premises[0]), case .ifolEx(let T, let body) = table[major],
                case .hyp(let k, let minor) = table[premises[1]]
            else { throw TableError.principalConnective(premises[0]) }
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
            guard
                let c = table.conclusion(of: premises[0]), case .ifolAll(let T, let body) = table[c],
                let (U, _, _) = table.sides(ofEquation: body)
            else { throw TableError.principalConnective(premises[0]) }
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

    private mutating func axiom(defining x: Definiendum) throws -> String {
        switch x {
        case .constant(let d):
            guard let axiom = constants[d.name]?.definition else { throw MalformedExport.undeclaredConstant(d.name) }
            return axiom

        case .ofClass(let k):
            if classAxioms == nil {
                var found = [TypeClass: String]()
                for axiom in corpus.axioms.keys.sorted() {
                    guard
                        let d = constants.defined(byAxiom: axiom),
                        case .ofClass(let c) = try definiendum(axiom, d)
                    else { continue }
                    guard found.updateValue(axiom, forKey: c) == nil
                    else { throw MalformedExport.duplicateDefinition(c.name) }
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
            if case .ofclass(let c, _) = head { return .ofClass(try classes.typeClass(c)) }
            guard case .constant(let c, _) = head, c == d.name else { throw MalformedExport.notADefinition(axiom) }
            return .constant(d)
        }
        definienda[axiom] = x
        return x
    }

    private func equation(_ axiom: String, _ e: Envelope) throws -> (type: IsaType, lhs: Body, rhs: Body) {
        let (head, sides) = try decode.spine(e.prop)
        guard case .constant("Pure.eq", let types) = head, types.count == 1, sides.count == 2 else {
            throw MalformedExport.notADefinition(axiom)
        }
        return (types[0], sides[0], sides[1])
    }

    private func termBinder(_ formula: NodeID) -> (IRType, NodeID)? {
        if case .ifolAll(let T, let body) = table[formula] { return (T, body) }
        if case .isaPropAll(let body) = table[formula] { return (.o, body) }
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
        return try stating(instance).root
    }

    private mutating func stating(_ instance: Instance) throws -> (root: NodeID, letters: [Bool]) {
        let path: String
        let e: Envelope
        let order: FreeOrder
        switch instance.source {
        case .theorem(let key):
            path = key.path
            e = try located(path) { try decode.proofFile(try corpus.file(key)).0 }
            order = .lettersFirst

        case .axiom(let name):
            guard let entry = corpus.axioms[name] else { throw MalformedExport.undeclaredAxiom(name) }
            path = entry.file
            e = try located(path) { try decode.axiom(entry.body) }
            order = .stated
        }
        let (p, letters) = try located(path) {
            var terms = try Terms(
                decode: decode,
                constants: constants,
                classes: classes,
                file: e,
                at: instance.types,
                order: order,
            )
            return (try terms.statement(e.prop, in: &table), terms.letters)
        }
        statements[instance] = p
        letterMasks[instance] = letters
        return (p, letters)
    }
}

private func match(_ pattern: IRType, _ T: IRType, _ bound: inout [String: IRType]) -> Bool {
    switch pattern {
    case .variable(let v):
        if let U = bound[v] { return U == T }
        bound[v] = T
        return true

    case .i, .o:
        return pattern == T

    case .fn(let a, let b):
        guard case .fn(let c, let d) = T else { return false }
        return match(a, c, &bound) && match(b, d, &bound)
    }
}

private struct Reached: Hashable {
    let defines: Definiendum
    let type: IRType
}

extension Reader {
    public mutating func unit() throws -> Unit {
        try unit(of: population)
    }

    public mutating func unit(of selection: [Theorem]) throws -> Unit {
        var statements = [Statement]()
        var unread = [String]()
        var taken = Set<String>()
        var definitions = [Definition]()
        var reached = Set<Reached>()
        var seen = Set<NodeID>()
        var work = [NodeID]()
        func take(_ theorem: Theorem, _ name: String) throws {
            guard taken.insert(name).inserted else { return }
            switch try read(theorem) {
            case .proved(let statement, let proof):
                statements.append(Statement(name: name, root: statement, proof: proof, theory: theorem.theory))
                work += [proof, statement]

            case .refused:
                unread.append(name)
            }
        }
        for theorem in selection { try take(theorem, try claimName(corpus.names[theorem.key]!)) }
        work.reverse()
        while let id = work.popLast() {
            guard seen.insert(id).inserted else { continue }
            if case .use(.theorem(let name), [], _) = table[id], let theorem = citedAs[name] { try take(theorem, name) }
            var met: Definition?
            if
                case .isaConst(.defined(let d), let T, _) = table[id], reached.insert(Reached(
                    defines: .constant(d),
                    type: T,
                )).inserted
            {
                met = try definition(of: d, at: T)
            } else if
                case .isaOfClass(let T, let k) = table[id],
                reached.insert(Reached(defines: .ofClass(k), type: T)).inserted
            {
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
