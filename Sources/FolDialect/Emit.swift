import Foundation
import IR
import Synchronization

@frozen
public enum EmitError: Error, Equatable, Sendable {
    case declaredByBase(String)
    case noTheory(String)
    case unproved(String)
    case citesNothing(name: String, cited: String)
    case citationCycle(String)
    case theoriesCiteEachOther([String])
    case citesLater(name: String, cited: String)
}

public struct EmittedStatement: Sendable, Equatable {
    public let name: String
    public let part: String
    public let written: Int
    public let tree: Int
    public let dag: Int
}

public struct EmittedPart: Sendable, Equatable {
    public let name: String
    public let loads: [String]
    public let claims: Int
    public let schemas: Int
    public let definitions: Int
    public let bytes: Int
}

public struct Emission: Sendable {
    public let parts: [EmittedPart]
    public let statements: [EmittedStatement]
}

public let defaultPartBytes = 1 << 26

public func emit(
    _ unit: IR.Unit,
    to directory: URL,
    base texts: [String],
    partBytes: Int = defaultPartBytes,
    threads: Int = 1,
) throws -> Emission {
    let t = unit.table
    let statements = unit.statements
    let declared = declaredNames(from: texts)
    if
        let clash = statements
            .first(where: { declared.contains($0.name) }) { throw EmitError.declaredByBase(clash.name) }
    var letters = schemaLetters(from: texts)
    for s in statements where s.defines == nil {
        let k = spineLetters(s.root, in: t)
        if k > 0 { letters[s.name] = (0..<k).map { "A\($0)" } }
    }
    let cites = try citations(statements, t)
    let order = try theoryOrder(statements, cites)
    let partOf = try placed(statements, cites, order)
    let theories = order + (partOf.contains(order.count) ? [uncited] : [])
    let sequence = inOrder(cites, partOf, parts: theories.count)

    let written = concurrently(sequence.flatMap(\.self), threads: threads) { k in
        let s = statements[k]
        let d = declaration(s, letters)
        if s.defines == nil, s.proof == nil { throw EmitError.unproved(s.name) }
        let body = try s.proof.map { try rendered(proof: $0, of: d, in: t, letters: letters) }
        return Rendered(
            declaration: d,
            head: try render(d, in: t) + "\n",
            text: body.map { $0.text + "\n" } ?? "",
            steps: body?.steps ?? 0,
            dag: s.proof.map { dagSteps($0, t) } ?? 0,
        )
    }
    try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
    var chunks = [Chunk]()
    var chunkOf = Array(repeating: 0, count: statements.count)
    var report = [EmittedStatement]()
    var trees = [NodeID: Int]()
    var files: Files?
    var next = written.makeIterator()
    for (p, theory) in theories.enumerated() {
        var pieces = 0
        for k in sequence[p] {
            let s = statements[k]
            let w = try next.next()!.get()
            let d = w.declaration
            let head = w.head
            let text = w.text
            let bytes = head.utf8.count + text.utf8.count
            if pieces == 0 || chunks[chunks.count - 1].bytes + bytes > partBytes {
                pieces += 1
                chunks.append(Chunk(name: pieces == 1 ? theory : "\(theory).\(pieces)"))
                try files?.close()
                files = try Files(directory, chunks[chunks.count - 1].name)
            }
            try files?.write(head, text)
            let c = chunks.count - 1
            chunks[c].add(d, bytes)
            chunks[c].statements.append(k)
            chunkOf[k] = c
            report.append(EmittedStatement(
                name: s.name,
                part: chunks[c].name,
                written: w.steps,
                tree: s.proof.map { treeSteps($0, t, &trees) } ?? 0,
                dag: w.dag,
            ))
        }
    }
    try files?.close()

    var closure = [Set<Int>]()
    var parts = [EmittedPart]()
    var listing = ""
    for (x, chunk) in chunks.enumerated() {
        var loads = Set<Int>()
        for k in chunk.statements {
            for c in cites[k] where chunkOf[c] != x {
                guard chunkOf[c] < x else { throw EmitError.citesLater(
                    name: statements[k].name,
                    cited: statements[c].name,
                ) }
                loads.insert(chunkOf[c])
                loads.formUnion(closure[chunkOf[c]])
            }
        }
        closure.append(loads)
        let names = loads.sorted().map { chunks[$0].name }
        parts.append(EmittedPart(
            name: chunk.name,
            loads: names,
            claims: chunk.claims,
            schemas: chunk.schemas,
            definitions: chunk.definitions,
            bytes: chunk.bytes,
        ))
        listing += chunk.name + ":" + names.map { " " + $0 }.joined() + "\n"
    }
    try listing.write(to: directory.appendingPathComponent("parts"), atomically: true, encoding: .utf8)
    return Emission(parts: parts, statements: report)
}

private struct Rendered: Sendable {
    let declaration: Declaration
    let head: String
    let text: String
    let steps: Int
    let dag: Int
}

private final class Results<T: Sendable>: Sendable {
    init(_ count: Int) {
        state = Mutex((next: 0, slots: [T?](repeating: nil, count: count)))
    }

    var all: [T] {
        state.withLock { $0.slots.map { $0! } }
    }

    func take() -> Int? {
        state.withLock { s in
            guard s.next < s.slots.count else { return nil }
            s.next += 1
            return s.next - 1
        }
    }

    func put(_ k: Int, _ value: T) {
        state.withLock { $0.slots[k] = value }
    }

    private let state: Mutex<(next: Int, slots: [T?])>
}

/// ⚠ A WORKER'S STACK IS SET, NEVER THE PLATFORM'S DEFAULT: rendering recurses as deep as a proof, which the main
/// thread's stack held.
private func concurrently<T: Sendable>(
    _ items: [Int],
    threads: Int,
    _ body: @escaping (Int) throws -> T,
) -> [Result<T, any Error>] {
    let results = Results<Result<T, any Error>>(items.count)
    let done = DispatchSemaphore(value: 0)
    let workers = min(max(threads, 1), items.count)
    for _ in 0..<workers {
        let worker = Thread {
            while let k = results.take() { results.put(k, Result { try body(items[k]) }) }
            done.signal()
        }
        worker.stackSize = 1 << 28
        worker.start()
    }
    for _ in 0..<workers { done.wait() }
    return results.all
}

private struct Chunk {
    let name: String
    var statements = [Int]()
    var claims = 0
    var schemas = 0
    var definitions = 0
    var bytes = 0

    mutating func add(_ d: Declaration, _ size: Int) {
        switch d.kind {
        case .claim: claims += 1
        case .schema: schemas += 1
        case .definition: definitions += 1
        }
        bytes += size
    }
}

private struct Files {
    init(_ directory: URL, _ name: String) throws {
        let def = directory.appendingPathComponent(name + ".fol.def")
        let proof = directory.appendingPathComponent(name + ".fol.proof")
        try Data().write(to: def)
        try Data().write(to: proof)
        definitions = try FileHandle(forWritingTo: def)
        proofs = try FileHandle(forWritingTo: proof)
    }

    let definitions: FileHandle
    let proofs: FileHandle

    func write(_ head: String, _ text: String) throws {
        try definitions.write(contentsOf: Data(head.utf8))
        if !text.isEmpty { try proofs.write(contentsOf: Data(text.utf8)) }
    }

    func close() throws {
        try definitions.close()
        try proofs.close()
    }
}

private func declaration(_ s: Statement, _ letters: [String: [String]]) -> Declaration {
    if let c = s.defines { return Declaration(kind: .definition(predicate: c.name), name: s.name, root: s.root) }
    if let names = letters[s.name] { return Declaration(kind: .schema(letters: names), name: s.name, root: s.root) }
    return Declaration(kind: .claim, name: s.name, root: s.root)
}

private func citations(_ statements: [Statement], _ t: Table) throws -> [[Int]] {
    var index = [String: Int]()
    for (k, s) in statements.enumerated() { index[s.name] = k }
    return try statements.map { s in
        var found = [Int]()
        var seen = Set<Int>()
        for name in cited(by: s, in: t) {
            guard let k = index[name] else { throw EmitError.citesNothing(name: s.name, cited: name) }
            if seen.insert(k).inserted { found.append(k) }
        }
        return found
    }
}

private func isTheorem(_ s: Statement) -> Bool {
    s.lemma == nil && s.defines == nil
}

private func theoryOrder(_ statements: [Statement], _ cites: [[Int]]) throws -> [String] {
    var needs = [String: Set<String>]()
    for (k, s) in statements.enumerated() where isTheorem(s) {
        guard let theory = s.theory else { throw EmitError.noTheory(s.name) }
        needs[theory, default: []].formUnion(cites[k].compactMap { c in
            let cited = statements[c]
            return isTheorem(cited) && cited.theory != theory ? cited.theory : nil
        })
    }
    var order = [String]()
    var placed = Set<String>()
    var remaining = needs.keys.sorted()
    while !remaining.isEmpty {
        guard let next = remaining.firstIndex(where: { needs[$0, default: []].isSubset(of: placed) }) else {
            throw EmitError.theoriesCiteEachOther(remaining)
        }
        order.append(remaining[next])
        placed.insert(remaining[next])
        remaining.remove(at: next)
    }
    return order
}

private let uncited = "_uncited"

private func placed(_ statements: [Statement], _ cites: [[Int]], _ theories: [String]) throws -> [Int] {
    var rank = [String: Int]()
    for (k, theory) in theories.enumerated() { rank[theory] = k }
    var citers = Array(repeating: [Int](), count: statements.count)
    for (k, cs) in cites.enumerated() {
        for c in cs { citers[c].append(k) }
    }
    var partOf = Array(repeating: -1, count: statements.count)
    var pending = citers.map(\.count)
    var ready = Array((0..<statements.count).filter { pending[$0] == 0 }.reversed())
    while let k = ready.popLast() {
        let s = statements[k]
        if isTheorem(s), let theory = s.theory, let p = rank[theory] {
            partOf[k] = p
        } else {
            partOf[k] = citers[k].map { partOf[$0] }.min() ?? theories.count
        }
        for c in cites[k] {
            pending[c] -= 1
            if pending[c] == 0 { ready.append(c) }
        }
    }
    if let k = partOf.firstIndex(of: -1) { throw EmitError.citationCycle(statements[k].name) }
    for (k, cs) in cites.enumerated() {
        for c in cs where partOf[c] > partOf[k] {
            throw EmitError.citesLater(name: statements[k].name, cited: statements[c].name)
        }
    }
    return partOf
}

private func inOrder(_ cites: [[Int]], _ partOf: [Int], parts: Int) -> [[Int]] {
    var visited = Array(repeating: false, count: cites.count)
    var sequence = Array(repeating: [Int](), count: parts)
    for start in cites.indices where !visited[start] {
        visited[start] = true
        var stack = [(statement: start, next: 0)]
        while let (k, i) = stack.last {
            if i < cites[k].count {
                stack[stack.count - 1].next += 1
                let c = cites[k][i]
                if !visited[c], partOf[c] == partOf[k] {
                    visited[c] = true
                    stack.append((c, 0))
                }
            } else {
                stack.removeLast()
                sequence[partOf[k]].append(k)
            }
        }
    }
    return sequence
}

private func writesALine(_ id: NodeID, _ t: Table) -> Bool {
    if case .hyp = t[id] { return false }
    if case .isaAllIntro(.o, _) = t[id] { return false }
    return true
}

private func proofChildren(_ id: NodeID, _ t: Table) -> [NodeID] {
    var children = [NodeID]()
    t[id].forEachChild { c, _ in if t.conclusion(of: c) != nil { children.append(c) } }
    return children
}

private func treeSteps(_ id: NodeID, _ t: Table, _ memo: inout [NodeID: Int]) -> Int {
    if let n = memo[id] { return n }
    var total = writesALine(id, t) ? 1 : 0
    for c in proofChildren(id, t) {
        let (sum, overflow) = total.addingReportingOverflow(treeSteps(c, t, &memo))
        total = overflow ? Int.max : sum
    }
    memo[id] = total
    return total
}

private func dagSteps(_ id: NodeID, _ t: Table) -> Int {
    var seen = Set<NodeID>()
    var work = [id]
    var count = 0
    while let x = work.popLast() {
        guard seen.insert(x).inserted else { continue }
        if writesALine(x, t) { count += 1 }
        work += proofChildren(x, t)
    }
    return count
}
