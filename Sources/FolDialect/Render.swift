import IR

@frozen
public enum RenderError: Error, Equatable, Sendable {
    case notClosed(NodeID)
    case sourceKind(NodeID)
    case schema(NodeID)
    case letters(String)
    case notAName(String)
    case notAFormula(NodeID)
    case notAProof(NodeID)
    case proofConcludes(expected: NodeID, found: NodeID)
    case instanceCitation(NodeID)
    case unsurveyed(NodeID?)
    case unboundValue(NodeID)
}

public func render(_ d: Declaration, in t: Table) throws -> String {
    let name = try spelled(d.name)
    guard t.looseBound(of: d.root) == 0 else { throw RenderError.notClosed(d.root) }
    switch d.kind {
    case .claim:
        return "claim \(name): \(try render(formula: d.root, in: t))"
    case .definition(let predicate):
        return "@def(\(try spelled(predicate))) axiom \(name): \(try render(formula: d.root, in: t))"
    case .schema(let letters):
        var w = Writer(t: t, spineLetters: letters)
        let body = try w.formula(d.root, spine: true)
        guard w.lettersBound == letters.count else { throw RenderError.letters(d.name) }
        let declared = zip(letters, w.arities).map { "\($0)(\($1))" }
        return "schema \(name) [\(declared.joined(separator: ", "))]: \(body)"
    }
}

public func render(formula root: NodeID, in t: Table) throws -> String {
    guard t.looseBound(of: root) == 0 else { throw RenderError.notClosed(root) }
    var w = Writer(t: t)
    return try w.formula(root)
}

public func render(
    proof root: NodeID,
    of d: Declaration,
    in t: Table,
    letters: [String: [String]] = [:],
) throws -> String {
    try rendered(proof: root, of: d, in: t, letters: letters).text
}

func rendered(proof root: NodeID, of d: Declaration, in t: Table, letters: [String: [String]]) throws
    -> (text: String, steps: Int)
{
    let name = try spelled(d.name)
    guard t.looseBound(of: root) == 0, t.looseHyps(of: root) == 0 else { throw RenderError.notClosed(root) }
    guard let concluded = t.conclusion(of: root) else { throw RenderError.notAProof(root) }
    guard concluded == d.root else { throw RenderError.proofConcludes(expected: d.root, found: concluded) }
    var spine = [String]()
    if case .schema(let names) = d.kind { spine = names }
    var w = Writer(t: t, letters: letters, spineLetters: spine)
    w.sharing = try Sharing(root, in: t)
    let last = try w.step(root, spine: true)
    guard w.lettersBound == spine.count else { throw RenderError.letters(d.name) }
    return try w.text(name, last)
}

private enum Rendered {
    case formula(String)
    case step(Int)
}

private enum Part: Hashable {
    case text(String)
    case ref(Int)
}

private struct Line {
    let named: Bool
    let parts: [Part]
}

private enum Item {
    case line(Int)
    case block(Block)
}

/// ⚠ A LINE IS WRITTEN AT ITS BLOCK'S CURSOR, BEFORE THE CHILD BLOCK OPEN THERE: written after it, a step placed in an
/// enclosing block would follow the use that cites it.
private final class Block {
    var items = [Item]()
    var cursor = 0
    var said = [[Part]: Int]()
}

private enum Link {
    case letter(NodeID)
    case forall(NodeID)
    case implies(NodeID)
}

private struct Writer {
    init(t: Table, letters: [String: [String]] = [:], spineLetters: [String] = []) {
        self.t = t
        self.letters = letters
        self.spineLetters = spineLetters
        let root = Block()
        path = [root]
        blocks = [0: root]
    }

    let t: Table
    var sharing: Sharing?
    var letters: [String: [String]]
    var spineLetters: [String]
    var lettersBound = 0
    var arities = [Int]()
    var terms = [String]()
    var termOccurrences = [Int32]()
    var hyps = [Int]()
    var hypOccurrences = [Int32]()
    var lines = [Line]()
    var path: [Block]
    var blocks: [Int32: Block]
    var written = [Int32: Int]()
    var closed = [NodeID: Int]()
    var values = [NodeID: (name: String, line: Int)]()

    var level: Int {
        terms.count + values.count
    }

    mutating func formula(_ id: NodeID, operand: Bool = false, spine: Bool = false) throws -> String {
        guard
            t.conclusion(of: id) == nil,
            case .formula(let s) = try render(id, -1, operand: operand, spine: spine)
        else { throw RenderError.notAFormula(id) }
        return s
    }

    /// ⚠ A NODE IS NOT A FACT: the key is the node and the binders its loose indices name, and one node under two keys
    /// is two facts, or one closed over the indices they differ in. A key is written once a proof, in the innermost
    /// block holding its uses, which the survey found: written in the block that first met it, a sibling block after
    /// that one would write it again, and cited outside its block, the checker drops it with the block's scope.
    mutating func step(_ id: NodeID, spine: Bool = false) throws -> Int {
        if case .hyp(let k, _) = t[id] { return hyps[hyps.count - 1 - k] }
        if case .valueFact(let v, _) = t[id] { return try named(v).line }
        let k = try key(id)
        if let done = written[k] { return done }
        guard let s = sharing else { throw RenderError.unsurveyed(id) }
        let result: Int
        if let c = s.closures[id], c.key != k {
            let fact = try closure(id, c)
            result = try at(s.placement[Int(k)]) { $0.instantiated(fact, c) }
        } else {
            result = try at(s.placement[Int(k)]) { w in
                guard case .step(let r) = try w.render(id, k, operand: false, spine: spine) else {
                    throw RenderError.notAProof(id)
                }
                return r
            }
        }
        written[k] = result
        return result
    }

    func text(_ name: String, _ last: Int) throws -> (text: String, steps: Int) {
        var out = ["proof \(name):"]
        var names = [Int: Int]()
        var work = [(path[0], 0)]
        while let (b, i) = work.popLast() {
            guard i < b.items.count else { continue }
            work.append((b, i + 1))
            switch b.items[i] {
            case .block(let inner):
                work.append((inner, 0))

            case .line(let id):
                var s = ""
                for part in lines[id].parts {
                    switch part {
                    case .text(let x): s += x
                    case .ref(let r):
                        guard let n = names[r] else { throw RenderError.unsurveyed(nil) }
                        s += "_\(n)"
                    }
                }
                if lines[id].named {
                    names[id] = names.count
                    s = "_\(names.count - 1) = " + s
                }
                out.append("    " + s)
            }
        }
        guard let n = names[last] else { throw RenderError.unsurveyed(nil) }
        return ((out + ["    qed _\(n)", ""]).joined(separator: "\n"), names.count)
    }

    private mutating func key(_ id: NodeID) throws -> Int32 {
        guard let s = sharing, let l = s.loose[id] else { throw RenderError.unsurveyed(id) }
        let o = l.terms.map { termOccurrences[termOccurrences.count - 1 - Int($0)] }
            + l.hyps.map { hypOccurrences[hypOccurrences.count - 1 - Int($0)] }
        guard let k = s.keys[Key(node: id, occurrences: o)] else { throw RenderError.unsurveyed(id) }
        return k
    }

    private func occurrence(_ o: Occurrence) throws -> Int32 {
        guard let sharing else { throw RenderError.unsurveyed(nil) }
        return sharing.occurrence(o)
    }

    /// `body` writing into `block`, the open blocks below it set aside until it returns.
    private mutating func at<R>(_ block: Int32, _ body: (inout Writer) throws -> R) throws -> R {
        guard let b = blocks[block], let i = path.lastIndex(where: { $0 === b }) else {
            throw RenderError.unsurveyed(nil)
        }
        let aside = Array(path[(i + 1)...])
        path.removeLast(aside.count)
        defer { path.append(contentsOf: aside) }
        return try body(&self)
    }

    private mutating func opening<R>(_ block: Int32, _ body: (inout Writer) throws -> R) throws -> R {
        guard block >= 0 else { throw RenderError.unsurveyed(nil) }
        let inner = Block()
        blocks[block] = inner
        let host = path[path.count - 1]
        host.items.insert(.block(inner), at: host.cursor)
        path.append(inner)
        defer {
            path.removeLast()
            host.cursor += 1
        }
        return try body(&self)
    }

    private mutating func opened(_ k: Int32) throws -> Int32 {
        guard let s = sharing, k >= 0 else { throw RenderError.unsurveyed(nil) }
        return s.opened[Int(k)]
    }

    /// A node met under keys that differ, written once closed over the indices they differ in: a `fix` per term, an
    /// `assume` per hypothesis — its formula the hypothesis node's — the node at their names, and the intros.
    private mutating func closure(_ id: NodeID, _ c: Closure) throws -> Int {
        if let fact = closed[id] { return fact }
        guard let s = sharing, let l = s.loose[id] else { throw RenderError.unsurveyed(id) }
        let names = c.terms.indices.map { "f\(level + $0)" }
        let width = max(terms.count + c.terms.count, t.looseBound(of: id))
        var closedTerms = Array(repeating: "", count: width)
        var closedTermOccurrences = Array(repeating: Int32(-1), count: width)
        for j in l.terms {
            let at = width - 1 - Int(j)
            if let i = c.terms.firstIndex(of: j) {
                closedTerms[at] = names[i]
                closedTermOccurrences[at] = try occurrence(.closed(id, hyp: false, index: j))
            } else {
                closedTerms[at] = terms[terms.count - 1 - Int(j)]
                closedTermOccurrences[at] = termOccurrences[termOccurrences.count - 1 - Int(j)]
            }
        }
        let depth = t.looseHyps(of: id)
        var closedHyps = Array(repeating: -1, count: depth)
        var closedHypOccurrences = Array(repeating: Int32(-1), count: depth)
        for j in l.hyps where !c.hyps.contains(j) {
            closedHyps[depth - 1 - Int(j)] = hyps[hyps.count - 1 - Int(j)]
            closedHypOccurrences[depth - 1 - Int(j)] = hypOccurrences[hypOccurrences.count - 1 - Int(j)]
        }
        let fact = try at(s.parent[Int(c.block)]) { w in
            try w.opening(c.block) { w in
                let outside = (w.terms, w.termOccurrences, w.hyps, w.hypOccurrences)
                defer { (w.terms, w.termOccurrences, w.hyps, w.hypOccurrences) = outside }
                for name in names { _ = w.scoped([.text("fix \(name)")], named: false) }
                (w.terms, w.termOccurrences) = (closedTerms, closedTermOccurrences)
                for j in c.hyps {
                    let (a, below) = try s.hypothesis(id, j)
                    w.terms += Array(repeating: "", count: below)
                    let assumed = try w.formula(a)
                    w.terms.removeLast(below)
                    closedHyps[depth - 1 - Int(j)] = w.scoped([.text("assume \(assumed)")])
                    closedHypOccurrences[depth - 1 - Int(j)] = try w.occurrence(.closed(id, hyp: true, index: j))
                }
                (w.hyps, w.hypOccurrences) = (closedHyps, closedHypOccurrences)
                var proved = try w.step(id)
                for _ in c.hyps { proved = w.scoped([.text("implies_intro "), .ref(proved)]) }
                for _ in c.terms { proved = w.scoped([.text("forall_intro "), .ref(proved)]) }
                return proved
            }
        }
        closed[id] = fact
        return fact
    }

    private mutating func instantiated(_ fact: Int, _ c: Closure) -> Int {
        var current = fact
        for j in c.terms {
            current = line([.text("forall_elim "), .ref(current), .text(", \(terms[terms.count - 1 - Int(j)])")])
        }
        for j in c.hyps {
            current = line([.text("implies_elim "), .ref(current), .text(", "), .ref(hyps[hyps.count - 1 - Int(j)])])
        }
        return current
    }

    private mutating func line(_ parts: [Part]) -> Int {
        for b in path.reversed() {
            if let id = b.said[parts] { return id }
        }
        let id = scoped(parts)
        path[path.count - 1].said[parts] = id
        return id
    }

    /// ⚠ A LINE THAT OPENS OR CLOSES A BLOCK IS NEVER SHARED: its text does not say which block, and a second
    /// `implies_intro _1` cited as the first leaves its own block open.
    private mutating func scoped(_ parts: [Part], named: Bool = true) -> Int {
        let id = lines.count
        lines.append(Line(named: named, parts: parts))
        let b = path[path.count - 1]
        b.items.insert(.line(id), at: b.cursor)
        b.cursor += 1
        return id
    }

    private mutating func emit(_ rule: String, _ premises: Int...) -> Rendered {
        var parts = [Part.text(rule + " ")]
        for (i, p) in premises.enumerated() {
            if i > 0 { parts.append(.text(", ")) }
            parts.append(.ref(p))
        }
        return .step(line(parts))
    }

    private mutating func binding<R>(
        term: String? = nil,
        bound termAt: Int32 = -1,
        hyp: Int? = nil,
        assumed hypAt: Int32 = -1,
        _ body: (inout Writer) throws -> R,
    ) rethrows -> R {
        if let term {
            terms.append(term)
            termOccurrences.append(termAt)
        }
        if let hyp {
            hyps.append(hyp)
            hypOccurrences.append(hypAt)
        }
        defer {
            if term != nil {
                terms.removeLast()
                termOccurrences.removeLast()
            }
            if hyp != nil {
                hyps.removeLast()
                hypOccurrences.removeLast()
            }
        }
        return try body(&self)
    }

    private mutating func nextLetter(_ id: NodeID, spine: Bool, arity: Int = 0) throws -> String {
        guard spine, lettersBound < spineLetters.count else { throw RenderError.schema(id) }
        defer { lettersBound += 1 }
        arities.append(arity)
        return spineLetters[lettersBound]
    }

    private mutating func render(_ id: NodeID, _ k: Int32, operand: Bool, spine: Bool) throws -> Rendered {
        switch t[id] {
        case .folBound(let k), .isaBound(let k, .o):
            return .formula(terms[terms.count - 1 - k])

        case .folPred(let predicate, let xs):
            let p = try spelled(predicate.name)
            if xs.isEmpty { return .formula(p) }
            return .formula("\(p)(\(try xs.map { try formula($0) }.joined(separator: ", ")))")

        case .folAnd(let a, let b): return try binary(a, "&", b)

        case .folOr(let a, let b): return try binary(a, "|", b)

        case .folImplies(let a, let b):
            return .formula("(\(try formula(a, operand: true)) -> \(try formula(b, operand: true, spine: spine)))")

        case .folIff(let a, let b): return try binary(a, "<->", b)

        case .folNot(let a):
            return .formula("~" + (try formula(a, operand: true)))

        case .folBottom:
            return .formula("false")

        case .folForall(let b): return try quantifier("forall", b, operand, spine: spine)

        case .folExists(let b): return try quantifier("exists", b, operand, spine: false)

        case .ifolAll(.o, let body):
            let name = try nextLetter(id, spine: spine)
            return .formula(try binding(term: name) { try $0.formula(body, operand: operand, spine: true) })

        case .folLetterAll(let arity, let body):
            let name = try nextLetter(id, spine: spine, arity: arity)
            return .formula(try binding(term: name) { try $0.formula(body, operand: operand, spine: true) })

        case .folLetter(let head, let xs):
            guard case .folBound(let k) = t[head] else { throw RenderError.schema(id) }
            return .formula("\(terms[terms.count - 1 - k])(\(try xs.map { try formula($0) }.joined(separator: ", ")))")

        case .use(let cited, let types, _):
            guard types.isEmpty else { throw RenderError.instanceCitation(id) }
            return .step(line([.text("use \(try spelled(cited.name))")]))

        case .hyp(let h, _):
            return .step(hyps[hyps.count - 1 - h])

        case .folAndIntro(let p, let q): return emit("and_intro", try step(p), try step(q))

        case .folAndElimL(let p): return emit("and_elim_l", try step(p))

        case .folAndElimR(let p): return emit("and_elim_r", try step(p))

        case .folOrIntroL(let p, let b):
            let proved = try step(p)
            let other = line([.text("let \(try formula(b))")])
            return emit("or_intro_l", proved, other)

        case .folOrIntroR(let a, let q):
            let other = line([.text("let \(try formula(a))")])
            return emit("or_intro_r", other, try step(q))

        case .folOrElim(let p, let q, let r):
            return emit("or_elim", try step(p), try step(q), try step(r))

        case .folImpliesIntro(let a, let body):
            return try discharging("assume \(try formula(a))", body, "implies_intro", k, spine: spine)

        case .folImpliesElim(let p, let q): return emit("implies_elim", try step(p), try step(q))

        case .folNotIntro(let a, let body):
            return try discharging("assume \(try formula(a))", body, "not_intro", k, spine: false)

        case .folNotElim(let p, let q): return emit("not_elim", try step(p), try step(q))

        case .folIffIntro(let p, let q): return emit("iff_intro", try step(p), try step(q))

        case .folIffElimL(let p, let q): return emit("iff_elim_l", try step(p), try step(q))

        case .folIffElimR(let p, let q): return emit("iff_elim_r", try step(p), try step(q))

        case .folForallIntro(let body):
            let fixed = "f\(level)"
            let bound = try occurrence(.bound(key: k, hyp: false))
            return try opening(try opened(k)) { w in
                _ = w.scoped([.text("fix \(fixed)")], named: false)
                let proved = try w.binding(term: fixed, bound: bound) { try $0.step(body, spine: spine) }
                return .step(w.scoped([.text("forall_intro "), .ref(proved)]))
            }

        case .isaAllIntro(.o, let body):
            let name = try nextLetter(id, spine: spine)
            let bound = try occurrence(.bound(key: k, hyp: false))
            return .step(try binding(term: name, bound: bound) { try $0.step(body, spine: true) })

        case .folLetterIntro(let arity, let body):
            let name = try nextLetter(id, spine: spine, arity: arity)
            let bound = try occurrence(.bound(key: k, hyp: false))
            return .step(try binding(term: name, bound: bound) { try $0.step(body, spine: true) })

        case .folForallElim(let p, let v):
            let proved = try step(p)
            return .step(line([.text("forall_elim "), .ref(proved), .text(", \(try formula(v))")]))

        case .folExistsIntro(let p, let v):
            let proved = try step(p)
            return .step(line([.text("exists_intro "), .ref(proved), .text(", \(try formula(v))")]))

        case .folExistsElim(let p, let body):
            let witness = "f\(level)"
            let premise = try step(p)
            let bound = try occurrence(.bound(key: k, hyp: false))
            let assumed = try occurrence(.bound(key: k, hyp: true))
            return try opening(try opened(k)) { w in
                let instance = w.scoped([.text("exists_elim "), .ref(premise), .text(", \(witness)")])
                let proved = try w
                    .binding(term: witness, bound: bound, hyp: instance, assumed: assumed) { try $0.step(body) }
                return .step(w.scoped([.text("exists_intro "), .ref(proved)]))
            }

        case .folCut(let p, let body):
            let fact = try step(p)
            let assumed = try occurrence(.bound(key: k, hyp: true))
            return .step(try binding(hyp: fact, assumed: assumed) { try $0.step(body) })

        case .folBottomElim(let p, let c):
            let proved = try step(p)
            let target = line([.text("let \(try formula(c))")])
            return emit("bottom_elim", proved, target)

        case .folClassicalAbsurd(let a, let body):
            return try discharging(
                "assume ~\(try formula(a, operand: true))",
                body,
                "classical_absurd",
                k,
                spine: false,
            )

        case .valueElim(let v, let p, let body):
            let witness = "f\(level)"
            let premise = try step(p)
            return try opening(try opened(k)) { w in
                let instance = w.scoped([.text("exists_elim "), .ref(premise), .text(", \(witness)")])
                w.values[v] = (witness, instance)
                defer { w.values[v] = nil }
                let proved = try w.step(body)
                return .step(w.scoped([.text("exists_intro "), .ref(proved)]))
            }

        case .value:
            return .formula(try named(id).name)

        case .valueFact(let v, _):
            return .step(try named(v).line)

        case .folSchemaInst:
            return try schemaInstance(id)

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass,
             .isaAllIntro, .isaAllElim, .isaGuard, .isaExIntro, .isaExElim, .isaReflexive, .isaSymmetric,
             .isaTransitive,
             .isaCombination,
             .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound,
             .isaHidden:
            throw Pattern(t[id], in: t).dialects.contains(.fol) ? RenderError.schema(id) : RenderError.sourceKind(id)

        case .folLetterAbs:
            var names = [String]()
            var body = id
            while case .folLetterAbs(let b) = t[body] {
                names.append("b\(level + names.count)")
                body = b
            }
            return .formula("\\" + names.joined(separator: " ") + ". " + (try lambda(names[...], body)))
        }
    }

    private func named(_ v: NodeID) throws -> (name: String, line: Int) {
        guard let n = values[v] else { throw RenderError.unboundValue(v) }
        return n
    }

    private mutating func schemaInstance(_ id: NodeID) throws -> Rendered {
        var links = [Link]()
        var head = id
        while true {
            if case .folSchemaInst(let p, let a) = t[head] {
                links.append(.letter(a))
                head = p
            } else if case .folForallElim(let p, let v) = t[head] {
                links.append(.forall(v))
                head = p
            } else if case .folImpliesElim(let p, let q) = t[head] {
                links.append(.implies(q))
                head = p
            } else {
                break
            }
        }
        guard
            case .use(let cited, [], _) = t[head],
            let names = letters[cited.name]
        else { throw RenderError.schema(id) }
        let schema = try spelled(cited.name)
        let order = Array(links.reversed())
        let instances = order.compactMap { link -> NodeID? in
            if case .letter(let a) = link { return a }
            return nil
        }
        guard names.count == instances.count else { throw RenderError.schema(id) }
        let bindings = try zip(names, instances).map { "\($0): \(try formula($1))" }.joined(separator: ", ")
        var current = line([.text("schema_inst \(schema) { \(bindings) }")])
        for link in order {
            switch link {
            case .letter: continue
            case .forall(let v): current = line([.text("forall_elim "), .ref(current), .text(", \(try formula(v))")])
            case .implies(let q):
                let premise = try step(q)
                current = line([.text("implies_elim "), .ref(current), .text(", "), .ref(premise)])
            }
        }
        return .step(current)
    }

    private mutating func lambda(_ names: ArraySlice<String>, _ body: NodeID) throws -> String {
        guard let first = names.first else { return try formula(body) }
        return try binding(term: first) { try $0.lambda(names.dropFirst(), body) }
    }

    private mutating func binary(_ a: NodeID, _ op: String, _ b: NodeID) throws -> Rendered {
        .formula("(\(try formula(a, operand: true)) \(op) \(try formula(b, operand: true)))")
    }

    private mutating func quantifier(_ q: String, _ body: NodeID, _ operand: Bool, spine: Bool) throws -> Rendered {
        let bound = "b\(level)"
        let s = "\(q) \(bound). \(try binding(term: bound) { try $0.formula(body, spine: spine) })"
        return .formula(operand ? "(\(s))" : s)
    }

    private mutating func discharging(
        _ assumption: String,
        _ body: NodeID,
        _ rule: String,
        _ k: Int32,
        spine: Bool,
    ) throws -> Rendered {
        let assumed = try occurrence(.bound(key: k, hyp: true))
        return try opening(try opened(k)) { w in
            let h = w.scoped([.text(assumption)])
            let proved = try w.binding(hyp: h, assumed: assumed) { try $0.step(body, spine: spine) }
            return .step(w.scoped([.text("\(rule) "), .ref(proved)]))
        }
    }
}

/// ⚠ A COPY OF THE CHECKER'S RESERVED WORDS (`src/parser/formula.l`): `T.use` lexes as `T`, `.`, `use`, so a segment
/// after
/// the first is written quoted, `T."use"`, and a first one refused. `false` is one and `False` is not: `False` lexes as
/// a
/// nullary predicate, silently.
private let keywords: Set = [
    "forall",
    "exists",
    "and",
    "or",
    "not",
    "implies",
    "iff",
    "false",
    "bottom",
    "axiom",
    "claim",
    "theorem",
    "proof",
    "fix",
    "assume",
    "let",
    "qed",
    "use",
    "and_intro",
    "and_elim_l",
    "and_elim_r",
    "or_intro_l",
    "or_intro_r",
    "or_elim",
    "implies_intro",
    "implies_elim",
    "not_intro",
    "not_elim",
    "bottom_elim",
    "iff_intro",
    "iff_elim_l",
    "iff_elim_r",
    "forall_intro",
    "forall_elim",
    "exists_intro",
    "exists_elim",
    "double_neg_elim",
    "excluded_middle",
    "peirce",
    "classical_absurd",
    "eq_subst",
    "eq_sym",
    "iota_elim",
    "iota",
    "include",
    "UNPROVED",
    "schema",
    "schema_inst",
]

func spelled(_ name: String) throws -> String {
    let segments = name.split(separator: ".", omittingEmptySubsequences: false).map(String.init)
    let wellFormed = isSegment(segments[0][...], digitFirst: false) && segments.dropFirst().allSatisfy(isQuotable)
    guard wellFormed, !keywords.contains(segments[0]) else { throw RenderError.notAName(name) }
    let written = segments.dropFirst().map {
        isSegment($0[...], digitFirst: true) && !keywords.contains($0) ? $0 : "\"\($0)\""
    }
    return ([segments[0]] + written).joined(separator: ".")
}

private func isQuotable(_ s: String) -> Bool {
    !s.isEmpty && s.allSatisfy { $0.isASCII && ($0.isLetter || $0.isNumber || $0 == "_" || $0 == "'") }
}

private func isSegment(_ s: Substring, digitFirst: Bool) -> Bool {
    let core = s.prefix { $0 != "'" }
    guard s.dropFirst(core.count).allSatisfy({ $0 == "'" }), let first = core.first else { return false }
    let word: (Character) -> Bool = { $0.isASCII && ($0.isLetter || $0.isNumber || $0 == "_") }
    guard word(first), digitFirst || !first.isNumber else { return false }
    return core.allSatisfy(word)
}
