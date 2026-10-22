import IR
import YXML

struct Reach: Hashable {
    var parameters = [String]()
    var premises = [String]()
}

/// ⚠ `AC.AC` IS THE DIALECT'S AXIOM, STATED ABOVE THE FOUNDATION (`ZF.AC`): taken for a theory's own axiom, every
/// theorem resting on choice carried it as a premise instead of citing it, derived from NBG's Choice.
func isTheorysOwnAxiom(_ name: String, _ entry: AxiomEntry, _ constants: Constants, _ families: Families) -> Bool {
    !Axiom.all.contains { $0.name == name } && !families.isFoundation(entry.theory)
        && constants.defined(byAxiom: name) == nil
}

struct ParameterContext {
    var types = [String: IRType]()
    var ofConstant = [String: [String]]()
}

private enum Vertex: Hashable {
    case theorem(TheoremKey)
    case constant(String)
    case axiom(String)
}

private struct Own {
    var parameters = Set<String>()
    var premises = Set<String>()
    var edges = Set<Vertex>()
}

struct Reaches {
    init(_ decode: Decode, _ constants: Constants, _ corpus: Corpus, _ families: Families, reaching: Set<String>) {
        self.decode = decode
        self.constants = constants
        self.corpus = corpus
        self.families = families
        self.reaching = reaching
        rank = Dictionary(uniqueKeysWithValues: constants.parameters.enumerated().map { ($0.element, $0.offset) })
    }

    static func reaching(_ export: Export, _ corpus: Corpus) throws -> Set<String> {
        var roots = Set(export.constants.parameters.compactMap { export.constants[$0]?.theory })
        for (name, entry) in corpus.axioms where isTheorysOwnAxiom(name, entry, export.constants, export.families) {
            roots.insert(entry.theory)
        }
        guard !roots.isEmpty else { return [] }
        var known = [String: Bool]()
        func reaches(_ theory: String) throws -> Bool {
            if let r = known[theory] { return r }
            var r = roots.contains(theory)
            if !r, !export.families.isFoundation(theory) {
                for p in try export.parents(theory) where try reaches(p) {
                    r = true
                    break
                }
            }
            known[theory] = r
            return r
        }
        return try Set(export.theories.filter { try reaches($0) })
    }

    mutating func of(_ key: TheoremKey) throws -> Reach {
        try closed(.theorem(key))
    }

    mutating func parameters(ofConstant name: String) throws -> [String] {
        try closed(.constant(name)).parameters
    }

    mutating func parameters(ofAxiom name: String) throws -> [String] {
        try closed(.axiom(name)).parameters
    }

    private let decode: Decode
    private let constants: Constants
    private let corpus: Corpus
    private let families: Families
    private let reaching: Set<String>
    private let rank: [String: Int]
    private var own = [Vertex: Own]()
    private var reached = [Vertex: Reach]()

    private mutating func closed(_ root: Vertex) throws -> Reach {
        if let r = reached[root] { return r }
        var work: [(Vertex, expanded: Bool)] = [(root, false)]
        var open = Set<Vertex>()
        while let (v, expanded) = work.popLast() {
            if reached[v] != nil { continue }
            let o = try owned(v)
            guard expanded else {
                guard open.insert(v).inserted else { throw MalformedExport.cyclicClosure("\(v)") }
                work.append((v, true))
                for e in o.edges where reached[e] == nil { work.append((e, false)) }
                continue
            }
            var parameters = o.parameters
            var premises = o.premises
            for e in o.edges {
                guard let r = reached[e] else { throw MalformedExport.cyclicClosure("\(v) → \(e)") }
                parameters.formUnion(r.parameters)
                premises.formUnion(r.premises)
            }
            reached[v] = Reach(
                parameters: try parameters.map { p in
                    guard let r = rank[p] else { throw MalformedExport.unreachedParameter(p) }
                    return (r, p)
                }.sorted { $0.0 < $1.0 }.map(\.1),
                premises: try premises.map { a in
                    guard let entry = corpus.axioms[a] else { throw MalformedExport.undeclaredAxiom(a) }
                    return (entry.order, a)
                }.sorted { $0.0 < $1.0 }.map(\.1),
            )
            open.remove(v)
        }
        guard let r = reached[root] else { throw MalformedExport.cyclicClosure("\(root)") }
        return r
    }

    private mutating func owned(_ v: Vertex) throws -> Own {
        if let o = own[v] { return o }
        var scan = Scan(decode: decode, constants: constants, corpus: corpus, families: families)
        switch v {
        case .theorem(let key):
            if reaching.contains(key.theory) {
                try located(key.path) {
                    let (e, proof) = try decode.proofFile(try corpus.file(key))
                    try scan.term(e.prop)
                    try scan.proof(proof)
                }
            }

        case .constant(let name):
            if
                let axiom = constants[name]?.definition, let entry = corpus.axioms[axiom],
                reaching.contains(entry.theory)
            {
                try located(entry.file) { try scan.term(try decode.axiom(entry.body).prop) }
                scan.found.edges.remove(.constant(name))
            }

        case .axiom(let name):
            if let entry = corpus.axioms[name], reaching.contains(entry.theory) {
                try located(entry.file) {
                    let e = try decode.axiom(entry.body)
                    guard e.tfrees.isEmpty else { throw DialectGap.premise(name) }
                    try scan.term(e.prop)
                }
                scan.found.premises.insert(name)
            }
        }
        own[v] = scan.found
        return scan.found
    }
}

private struct Scan {
    let decode: Decode
    let constants: Constants
    let corpus: Corpus
    let families: Families
    var found = Own()
    var terms = Set<Ref>()
    var steps = Set<Ref>()

    mutating func term(_ body: Body) throws {
        guard terms.insert(body[0]).inserted else { return }
        let (head, arguments) = try decode.spine(body)
        switch head {
        case .constant(let name, _):
            switch try constants.reading(name) {
            case .parameter: found.parameters.insert(name)
            case .constant(.defined(let d)): found.edges.insert(.constant(d.name))
            case .constant(.primitive), .erased, .implies, .and, .or, .bottom, .all, .ex, .metaAll, .metaEquality,
                 .hidden:
                break
            }

        case .abstraction(_, let inner):
            try term(inner)

        case .free, .schematic, .bound, .ofclass:
            break
        }
        for a in arguments { try term(a) }
    }

    mutating func proof(_ body: Body) throws {
        guard steps.insert(body[0]).inserted else { return }
        switch try decode.proofNode(body) {
        case .head(.termAbstraction(_, let p)):
            try proof(p)

        case .head(.hypothesisAbstraction(let x, let p)):
            try term(x)
            try proof(p)

        case .head(.hypothesis(let x)):
            try term(x)

        case .head(.theorem(let c)):
            found.edges.insert(.theorem(TheoremKey(theory: c.theory, serial: c.serial)))

        case .head(.axiom(let name, _)):
            if let d = constants.defined(byAxiom: name) {
                found.edges.insert(.constant(d.name))
            } else if let entry = corpus.axioms[name], isTheorysOwnAxiom(name, entry, constants, families) {
                found.edges.insert(.axiom(name))
            }

        case .head(.nop), .head(.bound), .head(.ofclass), .head(.oracle):
            break

        case .application(let p, .term(let x)):
            try proof(p)
            try term(x)

        case .application(let p, .proof(let q)):
            try proof(p)
            try proof(q)
        }
    }
}
