import IR

@frozen public enum RenderError: Error, Equatable, Sendable {
    case notClosed(NodeID)
    case sourceKind(NodeID)
    case schema(NodeID)
    case letters(String)
    case notAName(String)
    case notAFormula(NodeID)
    case notAProof(NodeID)
    case proofConcludes(expected: NodeID, found: NodeID)
    case instanceCitation(NodeID)
}

public func render(_ d: Declaration, in t: Table) throws -> String {
    let name = try spelled(d.name)
    guard t.looseBound(of: d.root) == 0 else { throw RenderError.notClosed(d.root) }
    switch d.kind {
    case .claim:
        return "claim \(name): \(try render(formula: d.root, in: t))"
    case let .definition(predicate):
        return "@def(\(try spelled(predicate))) axiom \(name): \(try render(formula: d.root, in: t))"
    case let .schema(letters):
        var w = Writer(t: t, spineLetters: letters)
        let body = try w.formula(d.root, spine: true)
        guard w.lettersBound == letters.count else { throw RenderError.letters(d.name) }
        return "schema \(name) [\(letters.map { "\($0)(0)" }.joined(separator: ", "))]: \(body)"
    }
}

public func render(formula root: NodeID, in t: Table) throws -> String {
    guard t.looseBound(of: root) == 0 else { throw RenderError.notClosed(root) }
    var w = Writer(t: t)
    return try w.formula(root)
}

public func render(proof root: NodeID, of d: Declaration, in t: Table, letters: [String: [String]] = [:]) throws -> String {
    try rendered(proof: root, of: d, in: t, letters: letters).text
}

func rendered(proof root: NodeID, of d: Declaration, in t: Table, letters: [String: [String]]) throws
    -> (text: String, steps: Int) {
    let name = try spelled(d.name)
    guard t.looseBound(of: root) == 0, t.looseHyps(of: root) == 0 else { throw RenderError.notClosed(root) }
    guard let concluded = t.conclusion(of: root) else { throw RenderError.notAProof(root) }
    guard concluded == d.root else { throw RenderError.proofConcludes(expected: d.root, found: concluded) }
    var spine: [String] = []
    if case let .schema(names) = d.kind { spine = names }
    var w = Writer(t: t, letters: letters, spineLetters: spine)
    let last = try w.step(root, spine: true)
    guard w.lettersBound == spine.count else { throw RenderError.letters(d.name) }
    return ((["proof \(name):"] + w.lines + ["    qed \(last)", ""]).joined(separator: "\n"), w.steps)
}

private enum Rendered {
    case formula(String)
    case step(String)
}

private struct Written: Hashable {
    let id: NodeID
    let terms: [String]
    let hyps: [String]
}

private enum Link {
    case letter(NodeID)
    case forall(NodeID)
    case implies(NodeID)
}

private struct Writer {
    let t: Table
    var letters: [String: [String]] = [:]
    var spineLetters: [String] = []
    var lettersBound = 0
    var terms: [String] = []
    var hyps: [String] = []
    var lines: [String] = []
    var steps = 0
    var written: [[Written: String]] = [[:]]

    mutating func formula(_ id: NodeID, operand: Bool = false, spine: Bool = false) throws -> String {
        guard case let .formula(s) = try render(id, operand: operand, spine: spine) else { throw RenderError.notAFormula(id) }
        return s
    }

    /// ⚠ A NODE IS NOT A FACT, AND A STEP OUTLIVES ITS BLOCK: the key is the node and the names its loose indices
    /// resolve to. The checker keeps a step derived until a scope it depends on closes (`cleanup_scope`), so a closing
    /// scope drops only the steps naming its variable or its assumption; the rest stay citable outside it.
    mutating func step(_ id: NodeID, spine: Bool = false) throws -> String {
        let key = Written(id: id, terms: Array(terms.suffix(t.looseBound(of: id))), hyps: Array(hyps.suffix(t.looseHyps(of: id))))
        for layer in written.reversed() {
            if let name = layer[key] { return name }
        }
        guard case let .step(s) = try render(id, operand: false, spine: spine) else { throw RenderError.notAProof(id) }
        written[written.count - 1][key] = s
        return s
    }

    private mutating func line(_ rule: String) -> String {
        let name = "_\(steps)"
        steps += 1
        lines.append("    \(name) = \(rule)")
        return name
    }

    private mutating func emit(_ rule: String) -> Rendered { .step(line(rule)) }

    private mutating func binding<R>(term: String?, hyp: String?, _ body: (inout Writer) throws -> R) rethrows -> R {
        if let term { terms.append(term) }
        if let hyp { hyps.append(hyp) }
        written.append([:])
        defer {
            for (key, name) in written.removeLast() {
                if let term, key.terms.contains(term) { continue }
                if let hyp, key.hyps.contains(hyp) { continue }
                written[written.count - 1][key] = name
            }
            if term != nil { terms.removeLast() }
            if hyp != nil { hyps.removeLast() }
        }
        return try body(&self)
    }

    private mutating func nextLetter(_ id: NodeID, spine: Bool) throws -> String {
        guard spine, lettersBound < spineLetters.count else { throw RenderError.schema(id) }
        defer { lettersBound += 1 }
        return spineLetters[lettersBound]
    }

    private mutating func render(_ id: NodeID, operand: Bool, spine: Bool) throws -> Rendered {
        switch t[id] {
        case let .folBound(k), let .isaBound(k, .o):
            return .formula(terms[terms.count - 1 - k])
        case let .folPred(predicate, xs):
            let p = try spelled(predicate.name)
            if xs.isEmpty { return .formula(p) }
            return .formula("\(p)(\(try xs.map { try formula($0) }.joined(separator: ", ")))")
        case let .folAnd(a, b): return try binary(a, "&", b)
        case let .folOr(a, b): return try binary(a, "|", b)
        case let .folImplies(a, b):
            return .formula("(\(try formula(a, operand: true)) -> \(try formula(b, operand: true, spine: spine)))")
        case let .folIff(a, b): return try binary(a, "<->", b)
        case let .folNot(a):
            return .formula("~" + (try formula(a, operand: true)))
        case .folBottom:
            return .formula("false")
        case let .folForall(b): return try quantifier("forall", b, operand, spine: spine)
        case let .folExists(b): return try quantifier("exists", b, operand, spine: false)
        case let .ifolAll(.o, body):
            let name = try nextLetter(id, spine: spine)
            return .formula(try binding(term: name, hyp: nil) { try $0.formula(body, operand: operand, spine: true) })

        case let .use(cited, types, _):
            guard types.isEmpty else { throw RenderError.instanceCitation(id) }
            return emit("use \(try spelled(cited.name))")
        case let .hyp(k, _):
            return .step(hyps[hyps.count - 1 - k])
        case let .folAndIntro(p, q): return emit("and_intro \(try step(p)), \(try step(q))")
        case let .folAndElimL(p): return emit("and_elim_l \(try step(p))")
        case let .folAndElimR(p): return emit("and_elim_r \(try step(p))")
        case let .folOrIntroL(p, b):
            let proved = try step(p)
            let other = line("let \(try formula(b))")
            return emit("or_intro_l \(proved), \(other)")
        case let .folOrIntroR(a, q):
            let other = line("let \(try formula(a))")
            return emit("or_intro_r \(other), \(try step(q))")
        case let .folOrElim(p, q, r):
            return emit("or_elim \(try step(p)), \(try step(q)), \(try step(r))")
        case let .folImpliesIntro(a, body): return try discharging("assume \(try formula(a))", body, "implies_intro", spine: spine)
        case let .folImpliesElim(p, q): return emit("implies_elim \(try step(p)), \(try step(q))")
        case let .folNotIntro(a, body): return try discharging("assume \(try formula(a))", body, "not_intro", spine: false)
        case let .folNotElim(p, q): return emit("not_elim \(try step(p)), \(try step(q))")
        case let .folIffIntro(p, q): return emit("iff_intro \(try step(p)), \(try step(q))")
        case let .folIffElimL(p, q): return emit("iff_elim_l \(try step(p)), \(try step(q))")
        case let .folIffElimR(p, q): return emit("iff_elim_r \(try step(p)), \(try step(q))")
        case let .folForallIntro(body):
            let fixed = "f\(terms.count)"
            lines.append("    fix \(fixed)")
            let proved = try binding(term: fixed, hyp: nil) { try $0.step(body, spine: spine) }
            return emit("forall_intro \(proved)")
        case let .isaAllIntro(.o, body):
            let name = try nextLetter(id, spine: spine)
            return .step(try binding(term: name, hyp: nil) { try $0.step(body, spine: true) })
        case let .folForallElim(p, v): return emit("forall_elim \(try step(p)), \(try formula(v))")
        case let .folExistsIntro(p, v): return emit("exists_intro \(try step(p)), \(try formula(v))")
        case let .folExistsElim(p, body):
            let witness = "f\(terms.count)"
            let instance = line("exists_elim \(try step(p)), \(witness)")
            let proved = try binding(term: witness, hyp: instance) { try $0.step(body) }
            return emit("exists_intro \(proved)")
        case let .folBottomElim(p, c):
            let proved = try step(p)
            let target = line("let \(try formula(c))")
            return emit("bottom_elim \(proved), \(target)")
        case let .folClassicalAbsurd(a, body):
            return try discharging("assume ~\(try formula(a, operand: true))", body, "classical_absurd", spine: false)
        case .folSchemaInst:
            return try schemaInstance(id)

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass,
             .isaAllIntro, .isaAllElim, .isaGuard, .isaExIntro, .isaExElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination,
             .isaAbstract, .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound:
            throw Pattern(t[id], in: t).dialects.contains(.fol) ? RenderError.schema(id) : RenderError.sourceKind(id)
        case .folLetterAll, .folLetter:
            throw RenderError.schema(id)
        case .folLetterAbs:
            var names: [String] = [], body = id
            while case let .folLetterAbs(b) = t[body] {
                names.append("b\(terms.count + names.count)")
                body = b
            }
            return .formula("\\" + names.joined(separator: " ") + ". " + (try lambda(names[...], body)))
        }
    }

    private mutating func schemaInstance(_ id: NodeID) throws -> Rendered {
        var links: [Link] = [], head = id
        while true {
            if case let .folSchemaInst(p, a) = t[head] {
                links.append(.letter(a))
                head = p
            } else if case let .folForallElim(p, v) = t[head] {
                links.append(.forall(v))
                head = p
            } else if case let .folImpliesElim(p, q) = t[head] {
                links.append(.implies(q))
                head = p
            } else {
                break
            }
        }
        guard case let .use(cited, [], _) = t[head], let names = letters[cited.name] else { throw RenderError.schema(id) }
        let schema = try spelled(cited.name)
        let order = Array(links.reversed())
        let instances = order.compactMap { link -> NodeID? in
            if case let .letter(a) = link { return a }
            return nil
        }
        guard names.count == instances.count else { throw RenderError.schema(id) }
        let bindings = try zip(names, instances).map { "\($0): \(try formula($1))" }.joined(separator: ", ")
        var current = line("schema_inst \(schema) { \(bindings) }")
        for link in order {
            switch link {
            case .letter: continue
            case let .forall(v): current = line("forall_elim \(current), \(try formula(v))")
            case let .implies(q): current = line("implies_elim \(current), \(try step(q))")
            }
        }
        return .step(current)
    }

    private mutating func lambda(_ names: ArraySlice<String>, _ body: NodeID) throws -> String {
        guard let first = names.first else { return try formula(body) }
        return try binding(term: first, hyp: nil) { try $0.lambda(names.dropFirst(), body) }
    }

    private mutating func binary(_ a: NodeID, _ op: String, _ b: NodeID) throws -> Rendered {
        .formula("(\(try formula(a, operand: true)) \(op) \(try formula(b, operand: true)))")
    }

    private mutating func quantifier(_ q: String, _ body: NodeID, _ operand: Bool, spine: Bool) throws -> Rendered {
        let bound = "b\(terms.count)"
        let s = "\(q) \(bound). \(try binding(term: bound, hyp: nil) { try $0.formula(body, spine: spine) })"
        return .formula(operand ? "(\(s))" : s)
    }

    private mutating func discharging(_ assumption: String, _ body: NodeID, _ rule: String, spine: Bool) throws -> Rendered {
        let h = line(assumption)
        let proved = try binding(term: nil, hyp: h) { try $0.step(body, spine: spine) }
        return emit("\(rule) \(proved)")
    }
}

/// ⚠ A COPY OF THE CHECKER'S RESERVED WORDS (`src/parser/formula.l`): `T.use` lexes as `T`, `.`, `use`, so a segment after
/// the first is written quoted, `T."use"`, and a first one refused. `false` is one and `False` is not: `False` lexes as a
/// nullary predicate, silently.
private let keywords: Set<String> = [
    "forall", "exists", "and", "or", "not", "implies", "iff", "false", "bottom", "axiom",
    "claim", "theorem", "proof", "fix", "assume", "let", "qed", "use", "and_intro",
    "and_elim_l", "and_elim_r", "or_intro_l", "or_intro_r", "or_elim", "implies_intro",
    "implies_elim", "not_intro", "not_elim", "bottom_elim", "iff_intro", "iff_elim_l",
    "iff_elim_r", "forall_intro", "forall_elim", "exists_intro", "exists_elim",
    "double_neg_elim", "excluded_middle", "peirce", "classical_absurd", "eq_subst", "eq_sym",
    "iota_elim", "iota", "include", "UNPROVED", "schema", "schema_inst",
]

func spelled(_ name: String) throws -> String {
    let segments = name.split(separator: ".", omittingEmptySubsequences: false).map(String.init)
    let wellFormed = isSegment(segments[0][...], digitFirst: false)
        && segments.dropFirst().allSatisfy { isSegment($0[...], digitFirst: true) }
    guard wellFormed, !keywords.contains(segments[0]) else { throw RenderError.notAName(name) }
    return ([segments[0]] + segments.dropFirst().map { keywords.contains($0) ? "\"\($0)\"" : $0 }).joined(separator: ".")
}

private func isSegment(_ s: Substring, digitFirst: Bool) -> Bool {
    let core = s.prefix { $0 != "'" }
    guard s.dropFirst(core.count).allSatisfy({ $0 == "'" }), let first = core.first else { return false }
    let word: (Character) -> Bool = { $0.isASCII && ($0.isLetter || $0.isNumber || $0 == "_") }
    guard word(first), digitFirst || !first.isNumber else { return false }
    return core.allSatisfy(word)
}
