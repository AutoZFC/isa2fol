import YXML

public let zfSessions = ["ZF", "ZF-AC", "ZF-Coind", "ZF-Constructible", "ZF-IMP", "ZF-Induct", "ZF-Resid", "ZF-UNITY", "ZF-ex"]

public func session(of theory: String) -> String? {
    if theory.hasPrefix("ZF-") { return String(theory.prefix { $0 != "." }) }
    if theory == "ZF" || theory == "ZFC" || theory.hasPrefix("ZF.") { return "ZF" }
    return nil
}

private let logic: Set = ["Pure", "IFOL", "FOL"]

public struct Item: Hashable, Comparable, Sendable {
    @frozen public enum Kind: Int, Comparable, Sendable {
        case constant, type, typeVariable, schematic, ofclass, axiom, theorem, oracle, calculus

        public static func < (a: Kind, b: Kind) -> Bool { a.rawValue < b.rawValue }
    }

    public let kind: Kind
    public let name: String

    public init(_ kind: Kind, _ name: String) {
        self.kind = kind
        self.name = name
    }

    public static func < (a: Item, b: Item) -> Bool { (a.kind, a.name) < (b.kind, b.name) }
}

public struct Surface: Sendable {
    public var named: [String: Int] = [:]
    public var statement: [Item: Int] = [:]
    public var proof: [Item: Int] = [:]
    public var citedZF = 0
}

public struct Closure: Sendable {
    public var named: [String: Int] = [:]
    public var leaves: [Item: Int] = [:]
    public var polymorphic = 0
    public var unboundTypeVariables: [String] = []
}

extension Export {
    public mutating func surface() throws -> Surface {
        var census = try loadCensus()
        var s = Surface()
        var cited: Set<TheoremKey> = []
        for key in census.population {
            try located(key.path) { try census.survey(key, into: &s, cited: &cited) }
        }
        s.citedZF = cited.count
        return s
    }

    public mutating func closure() throws -> Closure {
        var census = try loadCensus()
        var c = Closure()
        for key in census.population {
            try located(key.path) {
                for leaf in try census.leaves(key) { c.leaves[leaf, default: 0] += 1 }
                if try census.polymorphic(key) { c.polymorphic += 1 }
            }
            c.named[session(of: key.theory)!, default: 0] += 1
        }
        c.unboundTypeVariables = census.unbound.sorted()
        return c
    }

    private mutating func loadCensus() throws -> Census {
        let corpus = try load()
        let population = corpus.names.keys.filter { session(of: $0.theory) != nil }
            .sorted { ($0.theory, $0.serial) < ($1.theory, $1.serial) }
        return Census(decode: Decode(forest: forest), corpus: corpus, population: population)
    }
}

private struct Census {
    struct Region {
        var items: Set<Item> = []
        var boxes: Set<TheoremKey> = []
        var named: Set<TheoremKey> = []
    }

    let decode: Decode
    let corpus: Corpus
    let population: [TheoremKey]
    private(set) var unbound: Set<String> = []
    private var regions: [TheoremKey: Region] = [:]
    private var boxClosures: [TheoremKey: Region] = [:]
    private var leafClosures: [TheoremKey: Set<Item>] = [:]

    init(decode: Decode, corpus: Corpus, population: [TheoremKey]) {
        self.decode = decode
        self.corpus = corpus
        self.population = population
    }

    mutating func survey(_ key: TheoremKey, into s: inout Surface, cited: inout Set<TheoremKey>) throws {
        let (e, _) = try decode.proofFile(try corpus.file(key))
        var statement = try terms([e.prop])
        e.frees.forEach { Self.types($0.1, &statement) }
        if !e.tfrees.isEmpty { statement.insert(Item(.typeVariable, "")) }
        for item in statement { s.statement[item, default: 0] += 1 }

        var proof = try ownRegion(key)
        for box in proof.boxes {
            let c = try boxClosure(box)
            proof.items.formUnion(Self.instantiated(c.items))
            proof.named.formUnion(c.named)
        }
        for item in proof.items { s.proof[item, default: 0] += 1 }
        cited.formUnion(proof.named.filter { !logic.contains($0.theory) })
        s.named[session(of: key.theory)!, default: 0] += 1
    }

    func polymorphic(_ key: TheoremKey) throws -> Bool {
        !(try decode.proofFile(try corpus.file(key)).0.tfrees.isEmpty)
    }

    mutating func leaves(_ root: TheoremKey) throws -> Set<Item> {
        var work: [(TheoremKey, expanded: Bool)] = [(root, false)]
        while let (key, expanded) = work.popLast() {
            if leafClosures[key] != nil { continue }
            let own = try ownRegion(key)
            let children = own.boxes.union(own.named)
            if expanded {
                var leaves = own.items.filter { $0.kind == .axiom || $0.kind == .oracle }
                for child in children { leaves.formUnion(leafClosures[child]!) }
                leafClosures[key] = leaves
                continue
            }
            work.append((key, true))
            for child in children where leafClosures[child] == nil { work.append((child, false)) }
        }
        return leafClosures[root]!
    }

    private mutating func ownRegion(_ key: TheoremKey) throws -> Region {
        if let r = regions[key] { return r }
        let (e, proof) = try decode.proofFile(try corpus.file(key))
        let r = try located(key.path) { try region(proof, binding: Set(e.tfrees), label: key.path) }
        regions[key] = r
        return r
    }

    private mutating func boxClosure(_ root: TheoremKey) throws -> Region {
        var work: [(TheoremKey, expanded: Bool)] = [(root, false)]
        while let (key, expanded) = work.popLast() {
            if boxClosures[key] != nil { continue }
            var own = try ownRegion(key)
            if expanded {
                own.items.formUnion(try terms([try decode.proofFile(try corpus.file(key)).0.prop]))
                for child in own.boxes {
                    own.items.formUnion(Self.instantiated(boxClosures[child]!.items))
                    own.named.formUnion(boxClosures[child]!.named)
                }
                boxClosures[key] = own
                continue
            }
            work.append((key, true))
            for child in own.boxes where boxClosures[child] == nil { work.append((child, false)) }
        }
        return boxClosures[root]!
    }

    private mutating func region(_ proof: Body, binding: Set<String>, label: String) throws -> Region {
        var r = Region()
        var seen: Set<Ref> = []
        var work = [proof]
        var props: [Body] = []
        func check(_ types: [IsaType], _ cited: String) {
            for v in types.reduce(into: Set<IsaType>(), { $0.formUnion($1.variables) }) {
                switch v {
                case let .tfree(name, _) where !binding.contains(name):
                    unbound.insert("\(label) cites \(cited) at \(name)")
                case let .tvar(name, _, _):
                    unbound.insert("\(label) cites \(cited) at ?\(name)")
                case .tfree, .type:
                    break
                }
            }
        }
        while let body = work.popLast() {
            let spine = try decode.proofSpine(body)
            guard seen.insert(body[0]).inserted else { continue }
            switch spine.node {
            case .nop:
                r.items.insert(Item(.calculus, "empty proof"))
            case .bound:
                r.items.insert(Item(.calculus, "hypothesis"))
            case let .termAbstraction(T, p):
                r.items.insert(Item(.calculus, "⋀-intro"))
                Self.types(T, &r.items)
                work.append(p)
            case let .hypothesisAbstraction(t, p):
                r.items.insert(Item(.calculus, "⟹-intro"))
                props.append(t)
                work.append(p)
            case let .hypothesis(t):
                r.items.insert(Item(.calculus, "hypothesis"))
                props.append(t)
            case let .axiom(name, types):
                r.items.insert(Item(.axiom, name))
                types.forEach { Self.types($0, &r.items) }
                check(types, name)
            case let .ofclass(T, c):
                r.items.insert(Item(.ofclass, c))
                Self.types(T, &r.items)
            case let .oracle(name, _):
                r.items.insert(Item(.oracle, name))
            case let .theorem(c):
                let key = TheoremKey(theory: c.theory, serial: c.serial)
                if let name = corpus.names[key] {
                    if logic.contains(c.theory) { r.items.insert(Item(.theorem, name)) }
                    r.named.insert(key)
                } else {
                    r.boxes.insert(key)
                }
                c.types.forEach { Self.types($0, &r.items) }
                check(c.types, corpus.names[key] ?? key.path)
            }
            for argument in spine.arguments {
                switch argument {
                case let .term(t):
                    r.items.insert(Item(.calculus, "⋀-elim"))
                    props.append(t)
                case let .proof(p):
                    r.items.insert(Item(.calculus, "⟹-elim"))
                    work.append(p)
                }
            }
        }
        r.items.formUnion(try terms(props))
        return r
    }

    private static func instantiated(_ items: Set<Item>) -> Set<Item> {
        items.filter { $0.kind != .typeVariable }
    }

    private func terms(_ roots: [Body]) throws -> Set<Item> {
        var items: Set<Item> = []
        var seen: Set<Ref> = []
        var work = roots
        while let body = work.popLast() {
            let (head, arguments) = try decode.spine(body)
            guard seen.insert(body[0]).inserted else { continue }
            switch head {
            case let .constant(name, types):
                items.insert(Item(.constant, name))
                types.forEach { Self.types($0, &items) }
            case .free, .bound:
                break
            case .schematic:
                items.insert(Item(.schematic, ""))
            case let .abstraction(T, inner):
                Self.types(T, &items)
                work.append(inner)
            case let .ofclass(c, T):
                items.insert(Item(.ofclass, c))
                Self.types(T, &items)
            }
            work.append(contentsOf: arguments)
        }
        return items
    }

    private static func types(_ T: IsaType, _ items: inout Set<Item>) {
        switch T {
        case let .type(name, arguments):
            items.insert(Item(.type, name))
            arguments.forEach { types($0, &items) }
        case .tfree, .tvar:
            items.insert(Item(.typeVariable, ""))
        }
    }
}
