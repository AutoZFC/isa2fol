import IR
import YXML

struct Envelope {
    let tfrees: [String]
    let frees: [(String, IsaType)]
    let prop: Body
}

extension Decode {
    func proofFile(_ file: Body) throws -> (Envelope, proof: Body) {
        let (tfrees, rest) = try pair(tfreesHeader, { $0 }, file)
        let (frees, statement) = try pair(freesHeader, { $0 }, rest)
        let (prop, proof) = try pair({ $0 }, { $0 }, statement)
        return (Envelope(tfrees: tfrees, frees: frees, prop: prop), proof)
    }

    func axiom(_ body: Body) throws -> Envelope {
        guard body.count == 3 else { throw MalformedExport.bodyLength(expected: 3, found: body.count) }
        return Envelope(tfrees: try tfreesHeader(try node(body[0])), frees: try freesHeader(try node(body[1])),
                        prop: try node(body[2]))
    }

    private func tfreesHeader(_ ts: Body) throws -> [String] {
        let names = try list({ entry in
            let (name, sort) = try pair(string, { try list(string, $0) }, entry)
            guard sort.isEmpty else { throw MalformedExport.sortedTypeVariable(name) }
            return name
        }, ts)
        guard Set(names).count == names.count else { throw MalformedExport.tfreesHeader(names) }
        return names
    }

    private func freesHeader(_ ts: Body) throws -> [(String, IsaType)] {
        try list({ try pair(string, type, $0) }, ts)
    }

    func frees(_ body: Body) throws -> [String] {
        var seen = Set<Ref>(), known = Set<String>(), names: [String] = []
        try collect(body, &seen, &known, &names)
        return names
    }

    private func collect(_ body: Body, _ seen: inout Set<Ref>, _ known: inout Set<String>, _ names: inout [String]) throws {
        let (head, arguments) = try spine(body)
        guard seen.insert(body[0]).inserted else { return }
        switch head {
        case let .free(name, _):
            if known.insert(name).inserted { names.append(name) }
        case let .abstraction(_, inner):
            try collect(inner, &seen, &known, &names)
        case .constant, .schematic, .bound, .ofclass:
            break
        }
        for a in arguments { try collect(a, &seen, &known, &names) }
    }
}

struct Classes {
    private var declared: Set<String> = []

    mutating func load(_ body: [Ref], in forest: Forest) throws {
        let d = Decode(forest: forest)
        for r in body {
            guard case let .element(entity) = forest[r], entity.tag == "entity" else {
                throw MalformedExport.notAnEntity(tag: d.tag(r))
            }
            let name = try entity.attribute("name")
            _ = try d.pair({ $0 }, { $0 }, entity.children)
            guard declared.insert(name).inserted else { throw MalformedExport.duplicateClass(name) }
        }
    }

    func check(_ c: String) throws {
        guard declared.contains(c) else { throw MalformedExport.undeclaredClass(c) }
    }
}

extension Terms {
    mutating func statement(_ prop: Body, in t: inout Table) throws -> NodeID {
        try close(try proposition(prop, closure, in: &t), Node.ifolAll, in: &t)
    }
}

public func claimName(_ entity: String) throws -> String {
    var base = Substring(entity), index = ""
    if entity.hasSuffix(")"), let open = entity.lastIndex(of: "(") {
        let digits = entity[entity.index(after: open)..<entity.index(before: entity.endIndex)]
        if !digits.isEmpty, digits.allSatisfy({ $0.isASCII && $0.isNumber }) {
            base = entity[..<open]
            index = "." + digits
        }
    }
    let wellFormed = base.split(separator: ".", omittingEmptySubsequences: false).allSatisfy { segment in
        guard let c = segment.first else { return false }
        return !c.isNumber
    }
    guard wellFormed else { throw ReaderRefusal.nameSegment(entity) }
    return base + index
}
