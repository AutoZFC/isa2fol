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
    public var absorbed = 0
}

struct TheoremKey: Hashable {
    let theory: String
    let serial: Int
}

extension Export {
    public mutating func surface() throws -> Surface {
        var names: [TheoremKey: String] = [:]
        var files: [TheoremKey: Body] = [:]
        for theory in theories {
            for (serial, name) in try located("\(theory)/theory/thms", { try self.names(theory) }) {
                names[TheoremKey(theory: theory, serial: serial)] = name
            }
            for serial in try proofSerials(theory) {
                files[TheoremKey(theory: theory, serial: serial)] = try located("\(theory)/proofs/\(serial)") {
                    try forest.parse(contentsOf: "\(root)/\(theory)/proofs/\(serial)")
                }
            }
        }
        var census = Census(decode: Decode(forest: forest), names: names, files: files)
        let population = names.keys.filter { session(of: $0.theory) != nil }
            .sorted { ($0.theory, $0.serial) < ($1.theory, $1.serial) }
        for key in population {
            try located("\(key.theory)/proofs/\(key.serial)") { try census.named(key) }
        }
        return census.finished()
    }
}

private struct Census {
    struct Region {
        var items: Set<Item> = []
        var boxes: Set<TheoremKey> = []
        var cited: Set<TheoremKey> = []
    }

    let decode: Decode
    let names: [TheoremKey: String]
    let files: [TheoremKey: Body]
    private var surface = Surface()
    private var cited: Set<TheoremKey> = []
    private var closures: [TheoremKey: Region] = [:]
    private var premises: [TheoremKey: Int] = [:]

    init(decode: Decode, names: [TheoremKey: String], files: [TheoremKey: Body]) {
        self.decode = decode
        self.names = names
        self.files = files
    }

    func finished() -> Surface {
        var s = surface
        s.citedZF = cited.count
        return s
    }

    mutating func named(_ key: TheoremKey) throws {
        let e = try decode.envelope(try file(key))
        var statement = try terms([try unconditional(e.prop).rest])
        e.frees.forEach { Self.types($0.1, &statement) }
        if !e.tfrees.isEmpty { statement.insert(Item(.typeVariable, "")) }
        for item in statement { surface.statement[item, default: 0] += 1 }

        var proof = try region(e.proof)
        for box in proof.boxes {
            let c = try closure(box)
            proof.items.formUnion(Self.instantiated(c.items))
            proof.cited.formUnion(c.cited)
        }
        for item in proof.items { surface.proof[item, default: 0] += 1 }
        cited.formUnion(proof.cited)
        surface.named[session(of: key.theory)!, default: 0] += 1
    }

    private func file(_ key: TheoremKey) throws -> Body {
        guard let body = files[key] else { throw MalformedExport.unresolvedCitation(theory: key.theory, serial: key.serial) }
        return body
    }

    private mutating func closure(_ root: TheoremKey) throws -> Region {
        var own: [TheoremKey: Region] = [:]
        var work: [(TheoremKey, expanded: Bool)] = [(root, false)]
        while let (key, expanded) = work.popLast() {
            if closures[key] != nil { continue }
            if expanded {
                var c = own[key]!
                for child in c.boxes {
                    c.items.formUnion(Self.instantiated(closures[child]!.items))
                    c.cited.formUnion(closures[child]!.cited)
                }
                closures[key] = c
                continue
            }
            let e = try decode.envelope(try file(key))
            var r = try located("\(key.theory)/proofs/\(key.serial)") { try region(e.proof) }
            r.items.formUnion(try terms([try unconditional(e.prop).rest]))
            own[key] = r
            work.append((key, true))
            for child in r.boxes where closures[child] == nil { work.append((child, false)) }
        }
        return closures[root]!
    }

    private mutating func region(_ proof: Body) throws -> Region {
        var r = Region()
        var seen: Set<Ref> = []
        var work = [proof]
        var props: [Body] = []
        while let body = work.popLast() {
            let spine = try decode.proofSpine(body)
            guard seen.insert(body[0]).inserted else { continue }
            var absorb = 0
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
                if case .ofclass = try decode.spine(t).head {
                    work.append(p)
                } else {
                    r.items.insert(Item(.calculus, "⟹-intro"))
                    props.append(t)
                    work.append(p)
                }
            case let .hypothesis(t):
                r.items.insert(Item(.calculus, "hypothesis"))
                props.append(t)
            case let .axiom(name, types):
                r.items.insert(Item(.axiom, name))
                types.forEach { Self.types($0, &r.items) }
            case let .ofclass(T, c):
                r.items.insert(Item(.ofclass, c))
                Self.types(T, &r.items)
            case let .oracle(name, _):
                r.items.insert(Item(.oracle, name))
            case let .theorem(c):
                let key = TheoremKey(theory: c.theory, serial: c.serial)
                absorb = try classPremises(key)
                if let name = names[key] {
                    if logic.contains(c.theory) { r.items.insert(Item(.theorem, name)) } else { r.cited.insert(key) }
                } else {
                    r.boxes.insert(key)
                }
                c.types.forEach { Self.types($0, &r.items) }
            }
            var proofArguments = 0
            for argument in spine.arguments {
                switch argument {
                case let .term(t):
                    r.items.insert(Item(.calculus, "⋀-elim"))
                    props.append(t)
                case let .proof(p):
                    r.items.insert(Item(.calculus, "⟹-elim"))
                    if proofArguments < absorb { surface.absorbed += 1 } else { work.append(p) }
                    proofArguments += 1
                }
            }
        }
        r.items.formUnion(try terms(props))
        return r
    }

    private mutating func classPremises(_ key: TheoremKey) throws -> Int {
        if let n = premises[key] { return n }
        let n = try unconditional(try decode.envelope(try file(key)).prop).premises
        premises[key] = n
        return n
    }

    private func unconditional(_ prop: Body) throws -> (premises: Int, rest: Body) {
        var n = 0
        var t = prop
        while true {
            let (head, arguments) = try decode.spine(t)
            guard case .constant("Pure.imp", _) = head, arguments.count == 2 else { return (n, t) }
            guard case .ofclass = try decode.spine(arguments[0]).head else { return (n, t) }
            n += 1
            t = arguments[1]
        }
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
            case let .ofclass(c):
                items.insert(Item(.ofclass, c))
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
