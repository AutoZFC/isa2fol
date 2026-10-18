@frozen
public enum Owned: Hashable, Sendable {
    case rule
    case unbuilt
}

public protocol Pass {
    var name: String { get }

    func owns(_ p: Pattern) -> Owned?
    func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID]
}

@frozen
public enum Proved: Hashable, Sendable {
    case proof(NodeID)
    case unbuilt
    case cites(String)
}

@frozen
public enum Stated: Hashable, Sendable {
    case statement(NodeID)
    case unbuilt
}

public protocol Registry {
    func prove(
        _ lemma: Lemma,
        _ statement: NodeID,
        _ definitions: [Definition],
        _ theorems: [String: NodeID],
        in t: inout Table,
    ) throws -> Proved
    func define(_ c: Defined, _ definitions: [Definition], in t: inout Table) throws -> Stated
}

@frozen
public enum PipelineRefusal: Hashable, Sendable {
    case noOwner([Pattern])
    case unbuilt(pass: String, [Pattern])
    case lemmaUnbuilt
    case letterOffSpine([Pattern])
    case cites(String)
    case unread
}

@frozen
public enum PipelineError: Error, Equatable, Sendable {
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
    case notADefinition(String)
}

public struct Definition: Hashable, Sendable {
    public init(defines: Definiendum, type: IRType, axiomTypes: [IRType], parameters: Int, definiens: NodeID) {
        self.defines = defines
        self.type = type
        self.axiomTypes = axiomTypes
        self.parameters = parameters
        self.definiens = definiens
    }

    public let defines: Definiendum
    public let type: IRType
    public let axiomTypes: [IRType]
    public let parameters: Int
    public var definiens: NodeID

}

extension Defined {
    public var definitionName: String {
        name + "_DEF"
    }
}

public struct Statement: Sendable {
    public init(name: String, root: NodeID, proof: NodeID, theory: String? = nil) {
        self.name = name
        self.root = root
        self.proof = proof
        lemma = nil
        defines = nil
        self.theory = theory
    }

    public init(lemma: Lemma, root: NodeID) {
        name = lemma.name
        self.root = root
        proof = nil
        self.lemma = lemma
        defines = nil
        theory = nil
    }

    public init(defining c: Defined, root: NodeID) {
        name = c.definitionName
        self.root = root
        proof = nil
        lemma = nil
        defines = c
        theory = nil
    }

    public let name: String
    public var root: NodeID
    public var proof: NodeID?
    public let lemma: Lemma?
    public let defines: Defined?
    public let theory: String?

    public var cited: Cited {
        lemma.map(Cited.lemma) ?? .theorem(name)
    }

    var walked: [NodeID] {
        [root] + (proof.map { [$0] } ?? [])
    }
}

public struct Refused: Sendable {
    public let name: String
    public let refusal: PipelineRefusal
}

public struct Unit: Sendable {
    public init(table: Table, statements: [Statement], definitions: [Definition] = [], unread: [String] = []) {
        self.table = table
        self.statements = statements
        self.definitions = definitions
        refused = unread.map { Refused(name: $0, refusal: .unread) }
    }

    public var table: Table
    public var statements: [Statement]
    public var definitions: [Definition]
    public private(set) var refused: [Refused]
    public private(set) var dropped = [String]()

    mutating func refuse(_ name: String, _ refusal: PipelineRefusal) {
        refused.append(Refused(name: name, refusal: refusal))
    }

    mutating func drop(_ name: String) {
        dropped.append(name)
    }
}

public struct Pipeline {
    public init(passes: [Pass], registry: (any Registry)? = nil, provingAfter: String = "") {
        self.passes = passes
        self.registry = registry
        self.provingAfter = provingAfter
    }

    public let passes: [Pass]
    public let registry: (any Registry)?
    public let provingAfter: String

    public func completes(through stage: String?) -> Bool {
        stage == nil || stage == passes.last?.name
    }

    @discardableResult
    public func run(_ unit: inout Unit, through stage: String? = nil) throws -> [Stage] {
        if let stage, stage == "registry" ? registry == nil : !passes.contains(where: { $0.name == stage }) {
            throw PipelineError.noSuchPass(stage)
        }
        var run = try Run(self, unit)
        guard try run.lower(through: completes(through: stage) ? nil : stage) else {
            unit = run.partial()
            return run.stages
        }
        let start = ContinuousClock.now
        try run.legalized()
        unit = try run.linked()
        run.stages.append(Stage(name: "link", since: start))
        return run.stages
    }
}

public struct Stage: Sendable {
    init(name: String, since start: ContinuousClock.Instant) {
        let elapsed = ContinuousClock.now - start
        self.name = name
        seconds = Double(elapsed.components.seconds) + Double(elapsed.components.attoseconds) / 1e18
    }

    public let name: String
    public let seconds: Double

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

private func definiendum(_ d: Definition) throws -> Pattern {
    switch d.defines {
    case .constant(let c): return .isaConst(.init(.defined(c)), d.type, args: d.type.domains)
    case .ofClass:
        guard d.axiomTypes.count == 1 else { throw PipelineError.notADefinition(d.defines.name) }
        return .isaOfClass(d.axiomTypes[0])
    }
}

private struct Run {
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
            if unowned.isEmpty { live.append(Live(statement: s, held: held)) } else { self.unit.refuse(
                s.name,
                .noOwner(named(unowned)),
            ) }
        }
        for d in unit.definitions {
            guard let k = owner(of: try definiendum(d)) else { continue }
            let held = try check(patterns(under: [d.definiens], in: unit.table))
            guard held.allSatisfy({ $0.dialects.contains(.fol) || owner(of: $0) != nil }) else { continue }
            lowering.append(Lowering(definition: d, owner: k, held: held))
        }
    }

    let passes: [Pass]
    let registry: (any Registry)?
    let proving: Int?
    var unit: Unit
    var live = [Live]()
    var aside = [Lemma: Live]()
    var asideOrder = [Lemma]()
    var lowering = [Lowering]()
    var reached = [Definition]()
    var names = Set<String>()
    var lemmas = Set<Lemma>()
    var definitionsAsked = Set<Defined>()
    var definitionsRefused = Set<Defined>()
    var checked = Set<Pattern>()
    var stages = [Stage]()

    var setAside: [String] {
        asideOrder.compactMap { aside[$0]?.statement.name }
    }

    func owner(of p: Pattern) -> Int? {
        passes.firstIndex { $0.owns(p) != nil }
    }

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

    mutating func lower(through stage: String?) throws -> Bool {
        for (k, pass) in passes.enumerated() {
            let start = ContinuousClock.now
            var ready = [Live]()
            for l in live {
                let unbuilt = l.held.filter { pass.owns($0) == .unbuilt }
                if unbuilt.isEmpty { ready.append(l) } else { unit.refuse(
                    l.statement.name,
                    .unbuilt(pass: pass.name, named(unbuilt)),
                ) }
            }
            var handed = [Definition]()
            var passing = [Lowering]()
            for d in lowering {
                if d.owner == k {
                    handed.append(d.definition)
                } else if !d.held.contains(where: { pass.owns($0) == .unbuilt }) {
                    passing.append(d)
                }
            }
            reached += handed
            let out = try pass.run(
                ready.flatMap(\.statement.walked) + passing.map(\.definition.definiens),
                handed,
                in: &unit.table,
            )
            var next = out.makeIterator()
            var cited = [(Lemma, NodeID)]()
            live = []
            for var l in ready {
                let before = l.statement
                l.statement.root = next.next()!
                if before.proof != nil { l.statement.proof = next.next()! }
                if let proof = l.statement.proof {
                    let concluded = unit.table.conclusion(of: proof)
                    guard concluded == l.statement.root else {
                        throw PipelineError.unproved(
                            name: before.name,
                            pass: pass.name,
                            statement: l.statement.root,
                            conclusion: concluded,
                        )
                    }
                }
                if l.statement.walked != before.walked {
                    let (held, lemmas) = scan(l.statement.walked, unit.table)
                    l.held = try check(held)
                    cited += lemmas
                }
                if let p = survivor(l.held, through: k) { throw PipelineError.survived(
                    name: before.name,
                    pass: pass.name,
                    pattern: p,
                ) }
                live.append(l)
            }
            lowering = []
            for var d in passing {
                let definiens = next.next()!
                if
                    definiens != d.definition
                        .definiens { d.held = try check(patterns(under: [definiens], in: unit.table)) }
                if let p = survivor(d.held, through: k) {
                    throw PipelineError.survived(name: d.definition.defines.name, pass: pass.name, pattern: p)
                }
                d.definition.definiens = definiens
                lowering.append(d)
            }
            try add(cited, after: k)
            stages.append(Stage(name: pass.name, since: start))
            if stage == pass.name { return false }
            if k == proving {
                let proving = ContinuousClock.now
                try pruned()
                try prove()
                stages.append(Stage(name: "registry", since: proving))
                if stage == "registry" { return false }
            }
        }
        return true
    }

    func partial() -> Unit {
        var partial = unit
        partial.statements = live.map(\.statement)
        partial.definitions = reached
        for name in setAside { partial.drop(name) }
        return partial
    }

    mutating func legalized() throws {
        var legal = [Live]()
        for l in live {
            try legalize(l.statement.root, in: unit.table)
            if let c = l.statement.defines {
                guard isDefinition(l.statement.root, of: c, in: unit.table)
                else { throw PipelineError.notADefinition(l.statement.name) }
            } else {
                guard let proof = l.statement.proof else {
                    throw PipelineError.unproved(
                        name: l.statement.name,
                        pass: "registry",
                        statement: l.statement.root,
                        conclusion: nil,
                    )
                }
                try legalize(proof, in: unit.table)
            }
            let misplaced = misplacedLetters(l.statement.walked, in: unit.table)
            if misplaced.isEmpty { legal.append(l) } else { unit.refuse(
                l.statement.name,
                .letterOffSpine(named(misplaced)),
            ) }
        }
        live = legal
    }

    mutating func add(_ cited: [(Lemma, NodeID)], after k: Int) throws {
        for (l, root) in cited {
            let back = aside.removeValue(forKey: l)
            guard back != nil || lemmas.insert(l).inserted else { continue }
            guard let r = proving, k <= r else { throw PipelineError.citedAfterRegistry(l.name) }
            if let back {
                live.append(back)
                continue
            }
            guard names.insert(l.name).inserted else { throw PipelineError.duplicateName(l.name) }
            let held = try check(patterns(under: [root], in: unit.table))
            if let p = misstated(held, through: r) { throw PipelineError.misstatedLemma(name: l.name, pattern: p) }
            live.append(Live(statement: Statement(lemma: l, root: root), held: held))
        }
    }

    func blocked(_ held: Set<Pattern>, through r: Int) -> PipelineRefusal? {
        let unowned = held.filter { !$0.dialects.contains(.fol) && owner(of: $0) == nil }
        if !unowned.isEmpty { return .noOwner(named(unowned)) }
        for pass in passes[...r] {
            let unbuilt = held.filter { pass.owns($0) == .unbuilt }
            if !unbuilt.isEmpty { return .unbuilt(pass: pass.name, named(unbuilt)) }
        }
        return nil
    }

    func misstated(_ held: Set<Pattern>, through r: Int) -> Pattern? {
        named(held.filter { p in
            passes[...r].contains { $0.owns(p) != nil } || !p.dialects.contains(.fol) && owner(of: p) == nil
        }).first
    }

    mutating func define(_ constants: [Defined], with registry: any Registry, through r: Int) throws {
        for c in constants where definitionsAsked.insert(c).inserted {
            let name = c.definitionName
            guard names.insert(name).inserted else { throw PipelineError.duplicateName(name) }
            if
                let d = reached.first(where: { $0.defines == .constant(c) }) ?? unit.definitions
                    .first(where: { $0.defines == .constant(c) }),
                let refusal = blocked(
                    try check(patterns(under: [body(of: d, in: unit.table)], in: unit.table)),
                    through: r,
                )
            {
                unit.refuse(name, refusal)
                definitionsRefused.insert(c)
                continue
            }
            switch try registry.define(c, reached, in: &unit.table) {
            case .unbuilt:
                unit.refuse(name, .lemmaUnbuilt)
                definitionsRefused.insert(c)

            case .statement(let root):
                let held = try check(patterns(under: [root], in: unit.table))
                if let p = misstated(held, through: r) { throw PipelineError.misstatedLemma(name: name, pattern: p) }
                guard isDefinition(root, of: c, in: unit.table) else { throw PipelineError.notADefinition(name) }
                live.append(Live(statement: Statement(defining: c, root: root), held: held))
            }
        }
    }

    mutating func prove() throws {
        guard let registry, let r = proving else { return }
        var theorems = [String: NodeID]()
        for l in live where l.statement.lemma == nil && l.statement.defines == nil {
            theorems[l.statement.name] = l.statement.root
        }
        var next = 0
        var unbuilt = Set<Int>()
        while next < live.count {
            defer { next += 1 }
            if let l = live[next].statement.lemma, live[next].statement.proof == nil {
                let root = live[next].statement.root
                let named = constantsNamed(under: [root], unit.table)
                try define(named, with: registry, through: r)
                if let c = named.first(where: definitionsRefused.contains) {
                    unit.refuse(l.name, .cites(c.definitionName))
                    unbuilt.insert(next)
                    continue
                }
                switch try registry.prove(l, root, reached, theorems, in: &unit.table) {
                case .unbuilt:
                    unit.refuse(l.name, .lemmaUnbuilt)
                    unbuilt.insert(next)
                    continue

                case .cites(let name):
                    unit.refuse(l.name, .cites(name))
                    unbuilt.insert(next)
                    continue

                case .proof(let p):
                    let concluded = unit.table.conclusion(of: p)
                    guard concluded == root else {
                        throw PipelineError.unproved(
                            name: l.name,
                            pass: "registry",
                            statement: root,
                            conclusion: concluded,
                        )
                    }
                    let (held, cited) = scan([root, p], unit.table)
                    live[next].held = try check(held)
                    if let s = survivor(live[next].held, through: r) { throw PipelineError.survived(
                        name: l.name,
                        pass: "registry",
                        pattern: s,
                    ) }
                    live[next].statement.proof = p
                    try add(cited, after: r)
                }
            }
            try define(constantsNamed(under: live[next].statement.walked, unit.table), with: registry, through: r)
        }
        live = live.indices.filter { !unbuilt.contains($0) }.map { live[$0] }
    }

    mutating func pruned() throws {
        guard let registry, let r = proving else { return }
        var next = 0
        while next < live.count {
            if live[next].statement.lemma == nil {
                try define(constantsNamed(under: live[next].statement.walked, unit.table), with: registry, through: r)
            }
            next += 1
        }
        var ready = [Live]()
        for l in live {
            if l.statement.lemma == nil, let refusal = blocked(l.held, through: passes.count - 1) {
                unit.refuse(l.statement.name, refusal)
            } else {
                ready.append(l)
            }
        }
        live = ready
        let (cites, edges) = try graph { $0.lemma == nil }
        let kept = closed(cites)
        var cited = Set<Int>()
        for k in live.indices where kept[k] && live[k].statement.lemma == nil { cited.formUnion(edges[k]) }
        var needed = [Live]()
        for k in live.indices where kept[k] {
            if let l = live[k].statement.lemma, !cited.contains(k) {
                aside[l] = live[k]
                asideOrder.append(l)
            } else {
                needed.append(live[k])
            }
        }
        live = needed
    }

    mutating func linked() throws -> Unit {
        for name in setAside { unit.drop(name) }
        let (cites, edges) = try graph { _ in true }
        try acyclic(edges)
        let kept = closed(cites)
        var needed = Set(live.indices.filter {
            kept[$0] && live[$0].statement.lemma == nil && live[$0].statement.defines == nil
        })
        var stack = Array(needed)
        while let k = stack.popLast() {
            for j in edges[k] where kept[j] && needed.insert(j).inserted { stack.append(j) }
        }
        for k in live.indices where kept[k] && !needed.contains(k) { unit.drop(live[k].statement.name) }
        unit.statements = live.indices.filter(needed.contains).map { live[$0].statement }
        unit.definitions = reached
        return unit
    }

    func graph(_ decided: (Statement) -> Bool) throws -> (cites: [[String]], edges: [[Int]]) {
        var index = [Cited: Int]()
        var definitions = [Defined: Int]()
        for (k, l) in live.enumerated() {
            if let c = l.statement.defines { definitions[c] = k } else { index[l.statement.cited] = k }
        }
        let refused = Set(unit.refused.map(\.name))
        var cites = [[String]]()
        var edges = [[Int]]()
        for l in live {
            var found = [String]()
            var to = [Int]()
            guard decided(l.statement) else {
                cites.append(found)
                edges.append(to)
                continue
            }
            for (c, root) in l.statement.proof.map({ citations(under: $0, unit.table) }) ?? [] {
                found.append(c.name)
                if case .definition(let d) = c, let j = definitions[d] {
                    guard live[j].statement.root == root else { throw PipelineError.citationMismatch(c.name) }
                    to.append(j)
                } else if let j = index[c] {
                    guard live[j].statement.root == root else { throw PipelineError.citationMismatch(c.name) }
                    to.append(j)
                } else if !refused.contains(c.name) {
                    throw PipelineError.citesNothing(name: l.statement.name, cited: c.name)
                }
            }
            for c in constantsNamed(under: l.statement.walked, unit.table) where c != l.statement.defines {
                found.append(c.definitionName)
                if let j = definitions[c] {
                    to.append(j)
                } else if !refused.contains(c.definitionName) {
                    throw PipelineError.citesNothing(name: l.statement.name, cited: c.definitionName)
                }
            }
            cites.append(found)
            edges.append(to)
        }
        return (cites, edges)
    }

    mutating func closed(_ cites: [[String]]) -> [Bool] {
        var gone = Set(unit.refused.map(\.name))
        var kept = Array(repeating: true, count: live.count)
        var changed = true
        while changed {
            changed = false
            for k in live.indices where kept[k] {
                guard let hit = cites[k].filter(gone.contains).min() else { continue }
                unit.refuse(live[k].statement.name, .cites(hit))
                gone.insert(live[k].statement.name)
                kept[k] = false
                changed = true
            }
        }
        return kept
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

private func scan(_ roots: [NodeID], _ t: Table) -> (Set<Pattern>, [(Lemma, NodeID)]) {
    var seen = Set<NodeID>()
    var found = Set<Pattern>()
    var lemmas = [(Lemma, NodeID)]()
    var work = roots
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        found.insert(Pattern(t[id], in: t))
        if case .use(.lemma(let l), _, let root) = t[id] { lemmas.append((l, root)) }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    return (found, lemmas)
}

public func cited(by s: Statement, in t: Table) -> [String] {
    (s.proof.map { citations(under: $0, t).map(\.0.name) } ?? [])
        + constantsNamed(under: s.walked, t).filter { $0 != s.defines }.map(\.definitionName)
}

private func citations(under proof: NodeID, _ t: Table) -> [(Cited, NodeID)] {
    var seen = Set<NodeID>()
    var cited = Set<Cited>()
    var found = [(Cited, NodeID)]()
    var work = [proof]
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case .use(let c, _, let root) = t[id] {
            switch c {
            case .theorem, .lemma, .definition:
                if cited.insert(c).inserted { found.append((c, root)) }
            case .axiom, .theoryAxiom, .base:
                break
            }
            continue
        }
        t[id].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private func named(_ found: Set<Pattern>) -> [Pattern] {
    found.sorted { "\($0)" < "\($1)" }
}

/// The definiens under the abstractions over the constant's arguments, which a `@def` makes its own variables.
private func body(of d: Definition, in t: Table) -> NodeID {
    var body = d.definiens
    for _ in d.type.domains {
        guard case .isaAbs(_, let inner) = t[body] else { return body }
        body = inner
    }
    return body
}

private func constantsNamed(under roots: [NodeID], _ t: Table) -> [Defined] {
    var seen = Set<NodeID>()
    var found = [Defined]()
    var met = Set<Defined>()
    var work = Array(roots.reversed())
    while let id = work.popLast() {
        guard seen.insert(id).inserted else { continue }
        if case .folPred(.constant(.defined(let c)), _) = t[id], met.insert(c).inserted { found.append(c) }
        var children = [NodeID]()
        t[id].forEachChild { c, _ in children.append(c) }
        work += children.reversed()
    }
    return found
}

/// `∀v⃗. c(v⃗) ↔ body`, the arguments exactly the binders, outermost first, and `c` absent from `body`. ⚠ An argument
/// is compared by its index alone: a class parameter stays a typed isa variable until fol.
private func isDefinition(_ root: NodeID, of c: Defined, in t: Table) -> Bool {
    var body = root
    var k = 0
    while case .folForall(let inner) = t[body] {
        body = inner
        k += 1
    }
    guard
        case .folIff(let left, let right) = t[body], case .folPred(.constant(.defined(let d)), let args) = t[left],
        d == c,
        args.map({ t[$0].boundVariable?.index }) == (0..<k).map({ k - 1 - $0 })
    else { return false }
    return !constantsNamed(under: [right], t).contains(c)
}
