import IR

public struct Census: Sendable {
    public internal(set) var named = [String: Int]()
    public internal(set) var polymorphic = 0
    public internal(set) var refused = [ReaderRefusal: Int]()
    public internal(set) var patterns = [Pattern: Int]()
    public internal(set) var citations = [Cited: Int]()
    public internal(set) var definitions = [CitedDefinition: Int]()
    public internal(set) var premises = [String: Int]()
}

public struct CitedDefinition: Hashable, Sendable {
    public init(axiom: String, defines: Definiendum) {
        self.axiom = axiom
        self.defines = defines
    }

    public let axiom: String
    public let defines: Definiendum

}

private enum Fact: Hashable {
    case pattern(Pattern)
    case cited(Cited)
    case definition(CitedDefinition)
}

private enum Vertex: Hashable {
    case theorem(statement: NodeID, proof: NodeID)
    case definition(Definiendum)
}

private struct Bits {
    var words = [UInt64]()

    var members: [Int] {
        words.indices.flatMap { k in (0..<64).filter { words[k] & (1 << UInt64($0)) != 0 }.map { k * 64 + $0 } }
    }

    mutating func insert(_ k: Int) {
        while words.count <= k / 64 { words.append(0) }
        words[k / 64] |= 1 << UInt64(k % 64)
    }

    mutating func formUnion(_ other: Bits) {
        while words.count < other.words.count { words.append(0) }
        for (k, w) in other.words.enumerated() { words[k] |= w }
    }

}

private struct Closure {
    var facts = [Fact]()
    var ids = [Fact: Int]()
    var patternOf = [NodeID: Int]()
    var own = [Vertex: (facts: Bits, edges: [Vertex])]()
    var closed = [Vertex: Bits]()

    mutating func id(_ f: Fact) -> Int {
        if let k = ids[f] { return k }
        facts.append(f)
        ids[f] = facts.count - 1
        return facts.count - 1
    }

    mutating func pattern(_ n: NodeID, _ t: Table) -> Int {
        if let k = patternOf[n] { return k }
        let k = id(.pattern(Pattern(t[n], in: t)))
        patternOf[n] = k
        return k
    }

    mutating func walk(
        _ v: Vertex,
        _ roots: [NodeID],
        _ t: Table,
        _ cited: (String) -> Vertex?,
    ) -> (facts: Bits, edges: [Vertex]) {
        var bits = Bits()
        var edges = Set<Vertex>()
        var seen = Set<NodeID>()
        var work = roots
        while let n = work.popLast() {
            guard seen.insert(n).inserted else { continue }
            bits.insert(pattern(n, t))
            if case .use(let c, _, _) = t[n] {
                switch c {
                case .theorem(let name):
                    if let v = cited(name) { edges.insert(v) }
                case .axiom, .lemma, .base, .definition:
                    bits.insert(id(.cited(c)))
                }
            }
            if case .isaDefinition(let axiom, let d, _, _, _) = t[n] {
                bits.insert(id(.definition(CitedDefinition(axiom: axiom, defines: d))))
            }
            if case .isaConst(.defined(let d), _, _) = t[n] { edges.insert(.definition(.constant(d))) }
            if case .isaOfClass(_, let k) = t[n] { edges.insert(.definition(.ofClass(k))) }
            t[n].forEachChild { c, _ in work.append(c) }
        }
        edges.remove(v)
        return (bits, Array(edges))
    }
}

extension Reader {
    public mutating func census() throws -> Census {
        var c = Census()
        var proved = [Theorem: Vertex]()
        var read = Set<Theorem>()
        func take(_ theorem: Theorem) throws {
            guard read.insert(theorem).inserted else { return }
            switch try self.read(theorem) {
            case .proved(let statement, let proof): proved[theorem] = .theorem(statement: statement, proof: proof)
            case .refused(let r): c.refused[r, default: 0] += 1
            }
        }
        for theorem in population {
            try take(theorem)
            c.named[session(of: theorem.theory)!, default: 0] += 1
            if try !typeVariables(of: theorem).isEmpty { c.polymorphic += 1 }
        }
        var next = 0
        while next < cited.count {
            try take(cited[next])
            next += 1
        }

        var g = Closure()
        let citedAs = citedAs
        func own(_ v: Vertex) throws -> (facts: Bits, edges: [Vertex]) {
            if let o = g.own[v] { return o }
            let roots: [NodeID] =
                switch v {
                case .theorem(let statement, let proof): [statement, proof]
                case .definition(let d): [try definition(of: d)]
                }
            let o = g.walk(v, roots, table) { citedAs[$0].flatMap { proved[$0] } }
            g.own[v] = o
            return o
        }
        func close(_ root: Vertex) throws -> Bits {
            if let b = g.closed[root] { return b }
            var work: [(Vertex, expanded: Bool)] = [(root, false)]
            var open = Set<Vertex>()
            var last = Bits()
            while let (v, expanded) = work.popLast() {
                let o = try own(v)
                guard expanded else {
                    if g.closed[v] != nil { continue }
                    guard open.insert(v).inserted else { throw MalformedExport.cyclicClosure("\(v)") }
                    work.append((v, true))
                    for e in o.edges where g.closed[e] == nil { work.append((e, false)) }
                    continue
                }
                var bits = o.facts
                for e in o.edges {
                    guard let b = g.closed[e] else { throw MalformedExport.cyclicClosure("\(v) → \(e)") }
                    bits.formUnion(b)
                }
                g.closed[v] = bits
                open.remove(v)
                last = bits
            }
            return last
        }

        for theorem in population where proved[theorem] != nil {
            for p in try reach(of: theorem).premises { c.premises[p, default: 0] += 1 }
        }
        for theorem in population {
            guard let v = proved[theorem] else { continue }
            for k in try close(v).members {
                switch g.facts[k] {
                case .pattern(let p): c.patterns[p, default: 0] += 1
                case .cited(let cited): c.citations[cited, default: 0] += 1
                case .definition(let cited): c.definitions[cited, default: 0] += 1
                }
            }
        }
        return c
    }
}
