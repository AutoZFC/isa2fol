@frozen public enum Owned: Hashable, Sendable {
    case rule
    case unbuilt
}

public protocol Pass {
    var name: String { get }
    func owns(_ p: Pattern) -> Owned?
    func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID]
}

@frozen public enum Proved: Hashable, Sendable {
    case proof(NodeID)
    case unbuilt
}

public protocol Registry {
    func prove(_ lemma: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> Proved
}

@frozen public enum PipelineRefusal: Hashable, Sendable {
    case noOwner([Pattern])
    case unbuilt(pass: String, [Pattern])
    case lemmaUnbuilt
    case cites(String)
    case unread
}

@frozen public enum PipelineError: Error, Equatable, Sendable {
    case twoOwners(Pattern, passes: [String])
    case unproved(name: String, pass: String, statement: NodeID, conclusion: NodeID?)
    case survived(name: String, pass: String, pattern: Pattern)
    case noSuchPass(String)
    case duplicateName(String)
    case citedAfterRegistry(String)
    case misstatedLemma(name: String, pattern: Pattern)
    case citationMismatch(String)
    case citesNothing(name: String, cited: String)
    case citationCycle(String)
}

public struct Definition: Hashable, Sendable {
    public let constant: Defined
    public let type: IRType
    public var definiens: NodeID

    public init(constant: Defined, type: IRType, definiens: NodeID) {
        self.constant = constant
        self.type = type
        self.definiens = definiens
    }
}

public struct Statement: Sendable {
    public let name: String
    public var root: NodeID
    public var proof: NodeID?
    public let lemma: Lemma?

    public init(name: String, root: NodeID, proof: NodeID) {
        self.name = name
        self.root = root
        self.proof = proof
        lemma = nil
    }

    public init(lemma: Lemma, root: NodeID) {
        name = lemma.name
        self.root = root
        proof = nil
        self.lemma = lemma
    }

    public var cited: Cited { lemma.map(Cited.lemma) ?? .theorem(name) }

    var walked: [NodeID] { [root] + (proof.map { [$0] } ?? []) }
}

public struct Refused: Sendable {
    public let name: String
    public let refusal: PipelineRefusal
}

public struct Unit: Sendable {
    public var table: Table
    public var statements: [Statement]
    public var definitions: [Definition]
    public private(set) var refused: [Refused]

    public init(table: Table, statements: [Statement], definitions: [Definition] = [], unread: [String] = []) {
        self.table = table
        self.statements = statements
        self.definitions = definitions
        refused = unread.map { Refused(name: $0, refusal: .unread) }
    }

    mutating func refuse(_ name: String, _ refusal: PipelineRefusal) {
        refused.append(Refused(name: name, refusal: refusal))
    }
}

public struct Pipeline {
    public let passes: [Pass]
    public let registry: (any Registry)?
    public let provingAfter: String

    public init(passes: [Pass], registry: (any Registry)? = nil, provingAfter: String = "") {
        self.passes = passes
        self.registry = registry
        self.provingAfter = provingAfter
    }

    public func run(_ unit: inout Unit) throws {
        var run = try Run(self, unit)
        try run.lower()
        unit = try run.linked()
    }
}

private struct Live {
    var statement: Statement
    var held: Set<Pattern>
}

private struct Lowering {
    var definition: Definition
    let owner: Int
    var held: Set<Pattern>
}

private struct Run {
    let passes: [Pass]
    let registry: (any Registry)?
    let proving: Int?
    var unit: Unit
    var live: [Live] = []
    var lowering: [Lowering] = []
    var reached: [Definition] = []
    var names: Set<String> = []
    var lemmas: Set<Lemma> = []
    var checked: Set<Pattern> = []

    init(_ p: Pipeline, _ unit: Unit) throws {
        passes = p.passes
        registry = p.registry
        if p.registry == nil {
            proving = nil
        } else {
            guard let k = p.passes.firstIndex(where: { $0.name == p.provingAfter }) else {
                throw PipelineError.noSuchPass(p.provingAfter)
            }
            proving = k
        }
        self.unit = unit
        for r in unit.refused { names.insert(r.name) }
        for s in unit.statements {
            guard names.insert(s.name).inserted else { throw PipelineError.duplicateName(s.name) }
            let held = try check(patterns(under: s.walked, in: unit.table))
            let unowned = held.filter { !$0.dialects.contains(.fol) && owner(of: $0) == nil }
            if unowned.isEmpty { live.append(Live(statement: s, held: held)) } else { self.unit.refuse(s.name, .noOwner(named(unowned))) }
        }
        for d in unit.definitions {
            let constant = Pattern.isaConst(.init(.defined(d.constant)), d.type, args: domains(d.type))
            guard let k = owner(of: constant) else { continue }
            let held = try check(patterns(under: [d.definiens], in: unit.table))
            guard held.allSatisfy({ $0.dialects.contains(.fol) || owner(of: $0) != nil }) else { continue }
            lowering.append(Lowering(definition: d, owner: k, held: held))
        }
    }

    func owner(of p: Pattern) -> Int? { passes.firstIndex { $0.owns(p) != nil } }

    mutating func check(_ found: Set<Pattern>) throws -> Set<Pattern> {
        for p in named(found.subtracting(checked)) {
            checked.insert(p)
            let owners = passes.filter { $0.owns(p) != nil }.map(\.name)
            guard owners.count < 2 else { throw PipelineError.twoOwners(p, passes: owners) }
        }
        return found
    }

    func survivor(_ held: Set<Pattern>, through k: Int) -> Pattern? {
        named(held.filter { p in passes[...k].contains { $0.owns(p) != nil } }).first
    }

    mutating func lower() throws {
        for (k, pass) in passes.enumerated() {
            var ready: [Live] = []
            for l in live {
                let unbuilt = l.held.filter { pass.owns($0) == .unbuilt }
                if unbuilt.isEmpty { ready.append(l) } else { unit.refuse(l.statement.name, .unbuilt(pass: pass.name, named(unbuilt))) }
            }
            var handed: [Definition] = [], passing: [Lowering] = []
            for d in lowering {
                if d.owner == k {
                    handed.append(d.definition)
                } else if !d.held.contains(where: { pass.owns($0) == .unbuilt }) {
                    passing.append(d)
                }
            }
            reached += handed
            let out = try pass.run(ready.flatMap(\.statement.walked) + passing.map(\.definition.definiens), handed, in: &unit.table)
            var next = out.makeIterator(), cited: [(Lemma, NodeID)] = []
            live = []
            for var l in ready {
                let before = l.statement
                l.statement.root = next.next()!
                if before.proof != nil { l.statement.proof = next.next()! }
                if let proof = l.statement.proof {
                    let concluded = unit.table.conclusion(of: proof)
                    guard concluded == l.statement.root else {
                        throw PipelineError.unproved(name: before.name, pass: pass.name, statement: l.statement.root, conclusion: concluded)
                    }
                }
                if l.statement.walked != before.walked {
                    let (held, lemmas) = scan(l.statement.walked, unit.table)
                    l.held = try check(held)
                    cited += lemmas
                }
                if let p = survivor(l.held, through: k) { throw PipelineError.survived(name: before.name, pass: pass.name, pattern: p) }
                live.append(l)
            }
            lowering = []
            for var d in passing {
                let definiens = next.next()!
                if definiens != d.definition.definiens { d.held = try check(patterns(under: [definiens], in: unit.table)) }
                if let p = survivor(d.held, through: k) {
                    throw PipelineError.survived(name: d.definition.constant.name, pass: pass.name, pattern: p)
                }
                d.definition.definiens = definiens
                lowering.append(d)
            }
            try add(cited, after: k)
            if k == proving { try prove() }
        }
        for l in live {
            try legalize(l.statement.root, in: unit.table)
            guard let proof = l.statement.proof else {
                throw PipelineError.unproved(name: l.statement.name, pass: "registry", statement: l.statement.root, conclusion: nil)
            }
            try legalize(proof, in: unit.table)
        }
    }

    mutating func add(_ cited: [(Lemma, NodeID)], after k: Int) throws {
        for (l, root) in cited where lemmas.insert(l).inserted {
            guard let r = proving, k <= r else { throw PipelineError.citedAfterRegistry(l.name) }
            guard names.insert(l.name).inserted else { throw PipelineError.duplicateName(l.name) }
            let held = try check(patterns(under: [root], in: unit.table))
            let misstated = held.filter { p in
                passes[...r].contains { $0.owns(p) != nil } || !p.dialects.contains(.fol) && owner(of: p) == nil
            }
            if let p = named(misstated).first { throw PipelineError.misstatedLemma(name: l.name, pattern: p) }
            live.append(Live(statement: Statement(lemma: l, root: root), held: held))
        }
    }

    mutating func prove() throws {
        guard let registry, let r = proving else { return }
        var next = 0, unbuilt: Set<Int> = []
        while next < live.count {
            defer { next += 1 }
            guard let l = live[next].statement.lemma, live[next].statement.proof == nil else { continue }
            let root = live[next].statement.root
            switch try registry.prove(l, root, reached, in: &unit.table) {
            case .unbuilt:
                unit.refuse(l.name, .lemmaUnbuilt)
                unbuilt.insert(next)
            case let .proof(p):
                let concluded = unit.table.conclusion(of: p)
                guard concluded == root else {
                    throw PipelineError.unproved(name: l.name, pass: "registry", statement: root, conclusion: concluded)
                }
                let (held, cited) = scan([root, p], unit.table)
                live[next].held = try check(held)
                if let s = survivor(live[next].held, through: r) { throw PipelineError.survived(name: l.name, pass: "registry", pattern: s) }
                live[next].statement.proof = p
                try add(cited, after: r)
            }
        }
        live = live.indices.filter { !unbuilt.contains($0) }.map { live[$0] }
    }

    mutating func linked() throws -> Unit {
        var index: [Cited: Int] = [:]
        for (k, l) in live.enumerated() { index[l.statement.cited] = k }
        let refused = Set(unit.refused.map(\.name))
        var cites: [[Cited]] = [], edges: [[Int]] = []
        for l in live {
            var found: [Cited] = [], to: [Int] = []
            for (c, root) in citations(under: l.statement.proof!, unit.table) {
                found.append(c)
                if let j = index[c] {
                    guard live[j].statement.root == root else { throw PipelineError.citationMismatch(c.name) }
                    to.append(j)
                } else if !refused.contains(c.name) {
                    throw PipelineError.citesNothing(name: l.statement.name, cited: c.name)
                }
            }
            cites.append(found)
            edges.append(to)
        }
        try acyclic(edges)
        var gone = refused, kept = Array(repeating: true, count: live.count), changed = true
        while changed {
            changed = false
            for k in live.indices where kept[k] {
                guard let hit = cites[k].map(\.name).filter(gone.contains).min() else { continue }
                unit.refuse(live[k].statement.name, .cites(hit))
                gone.insert(live[k].statement.name)
                kept[k] = false
                changed = true
            }
        }
        unit.statements = live.indices.filter { kept[$0] }.map { live[$0].statement }
        unit.definitions = reached
        return unit
    }

    func acyclic(_ edges: [[Int]]) throws {
        var state = Array(repeating: 0, count: edges.count)
        for start in edges.indices where state[start] == 0 {
            var stack = [(start, 0)]
            state[start] = 1
            while let (v, e) = stack.last {
                guard e < edges[v].count else {
                    state[v] = 2
                    stack.removeLast()
                    continue
                }
                stack[stack.count - 1].1 += 1
                let w = edges[v][e]
                if state[w] == 1 { throw PipelineError.citationCycle(live[w].statement.name) }
                if state[w] == 0 {
                    state[w] = 1
                    stack.append((w, 0))
                }
            }
        }
    }
}

private func domains(_ T: IRType) -> [IRType] {
    guard case let .fn(a, b) = T else { return [] }
    return [a] + domains(b)
}

private func scan(_ roots: [NodeID], _ t: Table) -> (Set<Pattern>, [(Lemma, NodeID)]) {
    var seen: Set<NodeID> = [], found: Set<Pattern> = [], lemmas: [(Lemma, NodeID)] = [], work = roots
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        found.insert(Pattern(t[id], in: t))
        if case let .use(.lemma(l), _, root) = t[id] { lemmas.append((l, root)) }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    return (found, lemmas)
}

private func citations(under proof: NodeID, _ t: Table) -> [(Cited, NodeID)] {
    var seen: Set<NodeID> = [], cited: Set<Cited> = [], found: [(Cited, NodeID)] = [], work = [proof]
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case let .use(c, _, root) = t[id] {
            switch c {
            case .theorem, .lemma:
                if cited.insert(c).inserted { found.append((c, root)) }
            case .isaDefinition, .axiom, .theoryAxiom:
                break
            }
            continue
        }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private func named(_ found: Set<Pattern>) -> [Pattern] { found.sorted { "\($0)" < "\($1)" } }
