import YXML

typealias Body = [Ref]

struct Decode {
    let forest: Forest

    func node(_ t: Ref) throws -> Body {
        guard case let .element(e) = forest[t], e.tag == ":", e.attributes.isEmpty else {
            throw MalformedExport.notANode(tag: tag(t))
        }
        return e.children
    }

    func string(_ ts: Body) throws -> String {
        guard ts.count <= 1 else { throw MalformedExport.notAString }
        guard let t = ts.first else { return "" }
        guard case let .text(s) = forest[t] else { throw MalformedExport.notAString }
        return s
    }

    static func int(_ atom: String) throws -> Int {
        guard let n = Int(atom) else { throw MalformedExport.notAnInt(atom) }
        return n
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
        guard case let .element(e) = forest[ts[0]], let index = Int(e.tag), fs.indices.contains(index) else {
            throw MalformedExport.unknownVariant(tag: tag(ts[0]))
        }
        let names = e.attributes.map(\.name)
        guard names == names.indices.map(String.init) else { throw MalformedExport.vector(names: names) }
        return try fs[index](e.attributes.map(\.value), e.children)
    }

    func tag(_ t: Ref) -> String {
        guard case let .element(e) = forest[t] else { return "" }
        return e.tag
    }
}
