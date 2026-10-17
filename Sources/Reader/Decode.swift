import YXML

typealias Body = [Ref]

struct Decode {
    let forest: Forest

    static func int(_ atom: String) throws -> Int {
        guard let n = Int(atom) else { throw MalformedExport.notAnInt(atom) }
        return n
    }

    func node(_ t: Ref) throws -> Body {
        guard case .element(let e) = forest[t], e.tag == ":", e.attributes.isEmpty else {
            throw MalformedExport.notANode(tag: tag(t))
        }
        return e.children
    }

    func string(_ ts: Body) throws -> String {
        guard ts.count <= 1 else { throw MalformedExport.notAString }
        guard let t = ts.first else { return "" }
        guard case .text(let s) = forest[t] else { throw MalformedExport.notAString }
        return s
    }

    func pair<A, B>(_ f: (Body) throws -> A, _ g: (Body) throws -> B, _ ts: Body) throws -> (A, B) {
        guard ts.count == 2 else { throw MalformedExport.bodyLength(expected: 2, found: ts.count) }
        return (try f(node(ts[0])), try g(node(ts[1])))
    }

    func list<A>(_ f: (Body) throws -> A, _ ts: Body) throws -> [A] {
        try ts.map { try f(node($0)) }
    }

    func variant<A>(_ fs: [([String], Body) throws -> A], _ ts: Body) throws -> A {
        guard ts.count == 1 else { throw MalformedExport.bodyLength(expected: 1, found: ts.count) }
        guard case .element(let e) = forest[ts[0]], let index = Int(e.tag), fs.indices.contains(index) else {
            throw MalformedExport.unknownVariant(tag: tag(ts[0]))
        }
        let names = e.attributes.map(\.name)
        guard names == names.indices.map(String.init) else { throw MalformedExport.vector(names: names) }
        return try fs[index](e.attributes.map(\.value), e.children)
    }

    func tag(_ t: Ref) -> String {
        guard case .element(let e) = forest[t] else { return "" }
        return e.tag
    }
}

func one(_ atoms: [String]) throws -> String {
    guard atoms.count == 1 else { throw MalformedExport.atoms(atoms) }
    return atoms[0]
}

func indexname(_ atoms: [String]) throws -> (String, Int) {
    if atoms.count == 1 { return (atoms[0], 0) }
    guard atoms.count == 2 else { throw MalformedExport.atoms(atoms) }
    return (atoms[0], try Decode.int(atoms[1]))
}

func noAtoms(_ atoms: [String]) throws {
    guard atoms.isEmpty else { throw MalformedExport.atoms(atoms) }
}

func emptyBody(_ ts: Body) throws {
    guard ts.isEmpty else { throw MalformedExport.bodyLength(expected: 0, found: ts.count) }
}
