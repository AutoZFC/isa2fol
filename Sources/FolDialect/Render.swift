import IR

@frozen public enum RenderError: Error, Equatable, Sendable {
    case notClosed(NodeID)
    case sourceKind(NodeID)
    case notAName(String)
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
    return try text(root, depth: 0, operand: false, t)
}

private func text(_ id: NodeID, depth: Int, operand: Bool, _ t: Table) throws -> String {
    switch t[id] {
    case let .folBound(k):
        return "b\(depth - 1 - k)"
    case let .folPred(p, xs):
        try checkName(p)
        if xs.isEmpty { return p }
        return "\(p)(\(try xs.map { try text($0, depth: depth, operand: false, t) }.joined(separator: ", ")))"
    case let .folAnd(a, b): return try binary(a, "&", b, depth, t)
    case let .folOr(a, b): return try binary(a, "|", b, depth, t)
    case let .folImplies(a, b): return try binary(a, "->", b, depth, t)
    case let .folIff(a, b): return try binary(a, "<->", b, depth, t)
    case let .folNot(a):
        return "~" + (try text(a, depth: depth, operand: true, t))
    case .folBottom:
        return "false"
    case let .folForall(b): return try quantifier("forall", b, depth, operand, t)
    case let .folExists(b): return try quantifier("exists", b, depth, operand, t)
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs:
        throw RenderError.sourceKind(id)
    }
}

private func binary(_ a: NodeID, _ op: String, _ b: NodeID, _ depth: Int, _ t: Table) throws -> String {
    "(\(try text(a, depth: depth, operand: true, t)) \(op) \(try text(b, depth: depth, operand: true, t)))"
}

private func quantifier(_ q: String, _ body: NodeID, _ depth: Int, _ operand: Bool, _ t: Table) throws -> String {
    let s = "\(q) b\(depth). \(try text(body, depth: depth + 1, operand: false, t))"
    return operand ? "(\(s))" : s
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
