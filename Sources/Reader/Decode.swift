import YXML

typealias Body = [YXML.Node]

enum Decode {
    static func node(_ t: YXML.Node) throws -> Body {
        guard t.tag == ":", t.attributes.isEmpty else { throw MalformedExport.notANode(tag: t.tag) }
        return t.children
    }

    static func string(_ ts: Body) throws -> String {
        guard ts.count <= 1, ts.allSatisfy(\.isText) else { throw MalformedExport.notAString }
        return ts.first?.text ?? ""
    }

    static func int(_ atom: String) throws -> Int {
        guard let n = Int(atom) else { throw MalformedExport.notAnInt(atom) }
        return n
    }

    static func pair<A, B>(_ f: (Body) throws -> A, _ g: (Body) throws -> B, _ ts: Body) throws -> (A, B) {
        guard ts.count == 2 else { throw MalformedExport.bodyLength(expected: 2, found: ts.count) }
        return (try f(node(ts[0])), try g(node(ts[1])))
    }

    static func list<A>(_ f: (Body) throws -> A, _ ts: Body) throws -> [A] {
        try ts.map { try f(node($0)) }
    }

    static func variant<A>(_ fs: [([String], Body) throws -> A], _ ts: Body) throws -> A {
        guard ts.count == 1 else { throw MalformedExport.bodyLength(expected: 1, found: ts.count) }
        let t = ts[0]
        guard let tag = Int(t.tag), fs.indices.contains(tag) else { throw MalformedExport.unknownVariant(tag: t.tag) }
        let atoms = try (0..<t.attributes.count).map { i in
            guard let a = t.attributes[String(i)] else {
                throw MalformedExport.vector(names: t.attributes.keys.sorted())
            }
            return a
        }
        return try fs[tag](atoms, t.children)
    }
}
