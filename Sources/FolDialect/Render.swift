import IR

@frozen public enum RenderError: Error, Equatable, Sendable {
    case notClosed(NodeID)
    case sourceKind(NodeID)
    case schema(NodeID)
    case notAName(String)
    case notAFormula(NodeID)
    case notAProof(NodeID)
    case proofConcludes(expected: NodeID, found: NodeID)
    case instanceCitation(NodeID)
}

public func render(_ d: Declaration, in t: Table) throws -> String {
    try checkName(d.name)
    let body = try render(formula: d.root, in: t)
    switch d.kind {
    case .claim:
        return "claim \(d.name): \(body)"
    case let .definition(predicate):
        try checkName(predicate)
        return "@def(\(predicate)) axiom \(d.name): \(body)"
    }
}

public func render(formula root: NodeID, in t: Table) throws -> String {
    guard t.looseBound(of: root) == 0 else { throw RenderError.notClosed(root) }
    var w = Writer(t: t)
    return try w.formula(root)
}

public func render(proof root: NodeID, of d: Declaration, in t: Table) throws -> String {
    try checkName(d.name)
    guard t.looseBound(of: root) == 0, t.looseHyps(of: root) == 0 else { throw RenderError.notClosed(root) }
    guard let concluded = t.conclusion(of: root) else { throw RenderError.notAProof(root) }
    guard concluded == d.root else { throw RenderError.proofConcludes(expected: d.root, found: concluded) }
    var w = Writer(t: t)
    let last = try w.step(root)
    return (["proof \(d.name):"] + w.lines + ["    qed \(last)", ""]).joined(separator: "\n")
}

private enum Rendered {
    case formula(String)
    case step(String)
}

private struct Writer {
    let t: Table
    var terms: [String] = []
    var hyps: [String] = []
    var lines: [String] = []
    var steps = 0

    mutating func formula(_ id: NodeID, operand: Bool = false) throws -> String {
        guard case let .formula(s) = try render(id, operand: operand) else { throw RenderError.notAFormula(id) }
        return s
    }

    mutating func step(_ id: NodeID) throws -> String {
        guard case let .step(s) = try render(id, operand: false) else { throw RenderError.notAProof(id) }
        return s
    }

    private mutating func emit(_ rule: String) -> Rendered {
        let name = "_\(steps)"
        steps += 1
        lines.append("    \(name) = \(rule)")
        return .step(name)
    }

    private mutating func binding<R>(term: String?, hyp: String?, _ body: (inout Writer) throws -> R) rethrows -> R {
        if let term { terms.append(term) }
        if let hyp { hyps.append(hyp) }
        defer {
            if term != nil { terms.removeLast() }
            if hyp != nil { hyps.removeLast() }
        }
        return try body(&self)
    }

    private mutating func render(_ id: NodeID, operand: Bool) throws -> Rendered {
        switch t[id] {
        case let .folBound(k):
            return .formula(terms[terms.count - 1 - k])
        case let .folPred(predicate, xs):
            let p = predicate.name
            try checkName(p)
            if xs.isEmpty { return .formula(p) }
            return .formula("\(p)(\(try xs.map { try formula($0) }.joined(separator: ", ")))")
        case let .folAnd(a, b): return try binary(a, "&", b)
        case let .folOr(a, b): return try binary(a, "|", b)
        case let .folImplies(a, b): return try binary(a, "->", b)
        case let .folIff(a, b): return try binary(a, "<->", b)
        case let .folNot(a):
            return .formula("~" + (try formula(a, operand: true)))
        case .folBottom:
            return .formula("false")
        case let .folForall(b): return try quantifier("forall", b, operand)
        case let .folExists(b): return try quantifier("exists", b, operand)

        case let .use(cited, types, _):
            guard types.isEmpty else { throw RenderError.instanceCitation(id) }
            try checkName(cited.name)
            return emit("use \(cited.name)")
        case let .hyp(k, _):
            return .step(hyps[hyps.count - 1 - k])
        case let .folAndIntro(p, q): return emit("and_intro \(try step(p)), \(try step(q))")
        case let .folAndElimL(p): return emit("and_elim_l \(try step(p))")
        case let .folAndElimR(p): return emit("and_elim_r \(try step(p))")
        case let .folOrIntroL(p, b):
            let proved = try step(p)
            guard case let .step(other) = emit("let \(try formula(b))") else { throw RenderError.notAProof(id) }
            return emit("or_intro_l \(proved), \(other)")
        case let .folOrIntroR(a, q):
            guard case let .step(other) = emit("let \(try formula(a))") else { throw RenderError.notAProof(id) }
            return emit("or_intro_r \(other), \(try step(q))")
        case let .folOrElim(p, q, r):
            return emit("or_elim \(try step(p)), \(try step(q)), \(try step(r))")
        case let .folImpliesIntro(a, body): return try discharging("assume \(try formula(a))", body, "implies_intro")
        case let .folImpliesElim(p, q): return emit("implies_elim \(try step(p)), \(try step(q))")
        case let .folNotIntro(a, body): return try discharging("assume \(try formula(a))", body, "not_intro")
        case let .folNotElim(p, q): return emit("not_elim \(try step(p)), \(try step(q))")
        case let .folIffIntro(p, q): return emit("iff_intro \(try step(p)), \(try step(q))")
        case let .folIffElimL(p, q): return emit("iff_elim_l \(try step(p)), \(try step(q))")
        case let .folIffElimR(p, q): return emit("iff_elim_r \(try step(p)), \(try step(q))")
        case let .folForallIntro(body):
            let fixed = "f\(terms.count)"
            lines.append("    fix \(fixed)")
            let proved = try binding(term: fixed, hyp: nil) { try $0.step(body) }
            return emit("forall_intro \(proved)")
        case let .folForallElim(p, v): return emit("forall_elim \(try step(p)), \(try formula(v))")
        case let .folExistsIntro(p, v): return emit("exists_intro \(try step(p)), \(try formula(v))")
        case let .folExistsElim(p, body):
            let witness = "f\(terms.count)"
            guard case let .step(instance) = emit("exists_elim \(try step(p)), \(witness)") else {
                throw RenderError.notAProof(id)
            }
            let proved = try binding(term: witness, hyp: instance) { try $0.step(body) }
            return emit("exists_intro \(proved)")
        case let .folBottomElim(p, c):
            let proved = try step(p)
            guard case let .step(target) = emit("let \(try formula(c))") else { throw RenderError.notAProof(id) }
            return emit("bottom_elim \(proved), \(target)")
        case let .folClassicalAbsurd(a, body):
            return try discharging("assume ~\(try formula(a, operand: true))", body, "classical_absurd")

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass,
             .isaAllIntro, .isaAllElim, .isaGuard, .isaExIntro, .isaExElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination,
             .isaAbstract:
            throw Pattern(t[id], in: t).dialects.contains(.fol) ? RenderError.schema(id) : RenderError.sourceKind(id)
        case .folSchemaInst:
            throw RenderError.schema(id)
        }
    }

    private mutating func binary(_ a: NodeID, _ op: String, _ b: NodeID) throws -> Rendered {
        .formula("(\(try formula(a, operand: true)) \(op) \(try formula(b, operand: true)))")
    }

    private mutating func quantifier(_ q: String, _ body: NodeID, _ operand: Bool) throws -> Rendered {
        let bound = "b\(terms.count)"
        let s = "\(q) \(bound). \(try binding(term: bound, hyp: nil) { try $0.formula(body) })"
        return .formula(operand ? "(\(s))" : s)
    }

    private mutating func discharging(_ assumption: String, _ body: NodeID, _ rule: String) throws -> Rendered {
        guard case let .step(h) = emit(assumption) else { throw RenderError.notAProof(body) }
        let proved = try binding(term: nil, hyp: h) { try $0.step(body) }
        return emit("\(rule) \(proved)")
    }
}

/// ⚠ A COPY OF THE CHECKER'S RESERVED WORDS (`src/parser/formula.l`). `false` is one and
/// `False` is not: `False` lexes as a nullary predicate, silently.
private let keywords: Set<String> = [
    "forall", "exists", "and", "or", "not", "implies", "iff", "false", "bottom", "axiom",
    "claim", "theorem", "proof", "fix", "assume", "let", "qed", "use", "and_intro",
    "and_elim_l", "and_elim_r", "or_intro_l", "or_intro_r", "or_elim", "implies_intro",
    "implies_elim", "not_intro", "not_elim", "bottom_elim", "iff_intro", "iff_elim_l",
    "iff_elim_r", "forall_intro", "forall_elim", "exists_intro", "exists_elim",
    "double_neg_elim", "excluded_middle", "peirce", "classical_absurd", "eq_subst", "eq_sym",
    "iota_elim", "iota", "include", "UNPROVED", "schema", "schema_inst",
]

func checkName(_ name: String) throws {
    let segments = name.split(separator: ".", omittingEmptySubsequences: false)
    let wellFormed = isSegment(segments[0], digitFirst: false)
        && segments.dropFirst().allSatisfy { isSegment($0, digitFirst: true) }
    guard wellFormed, !keywords.contains(name) else { throw RenderError.notAName(name) }
}

private func isSegment(_ s: Substring, digitFirst: Bool) -> Bool {
    let core = s.prefix { $0 != "'" }
    guard s.dropFirst(core.count).allSatisfy({ $0 == "'" }), let first = core.first else { return false }
    let word: (Character) -> Bool = { $0.isASCII && ($0.isLetter || $0.isNumber || $0 == "_") }
    guard word(first), digitFirst || !first.isNumber else { return false }
    return core.allSatisfy(word)
}
