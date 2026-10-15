import Foundation
import Testing
import IR
import FolDialect

private let o = IRType.o

private struct Formulas {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func v(_ k: Int) throws -> NodeID { try n(.isaBound(k, o)) }
    mutating func letters(_ k: Int, _ body: NodeID) throws -> NodeID {
        k == 0 ? body : try n(.ifolAll(o, body: try letters(k - 1, body)))
    }
}

/// A schema's letters are its own binders, the first outermost: `cong_and`'s `A A2 B B2` are `⋀A A2 B B2::o`.
@Test func aSchemaLineParsesToItsLettersBinders() throws {
    var f = Formulas()
    let line = "schema cong_and [A(0), A2(0), B(0), B2(0)]: ((A <-> A2) -> ((B <-> B2) -> ((A & B) <-> (A2 & B2))))"
    let (name, root) = try parse(schema: line, in: &f.t)
    let (A, A2, B, B2) = (try f.v(3), try f.v(2), try f.v(1), try f.v(0))
    let body = try f.n(.folImplies(try f.n(.folIff(A, A2)), try f.n(.folImplies(try f.n(.folIff(B, B2)),
        try f.n(.folIff(try f.n(.folAnd(A, B)), try f.n(.folAnd(A2, B2))))))))
    #expect(name == "cong_and")
    #expect(root == (try f.letters(4, body)))
}

/// Every connective base's propositional schemas use: `~`, `|`, `->`, `<->`, `&`, and `false`.
@Test func everyConnectiveParses() throws {
    var f = Formulas()
    let (_, root) = try parse(schema: "schema s [A(0), B(0)]: (((~ A) | (A & B)) -> ((A <-> B) -> false))", in: &f.t)
    let (A, B) = (try f.v(1), try f.v(0))
    let left = try f.n(.folOr(try f.n(.folNot(A)), try f.n(.folAnd(A, B))))
    let right = try f.n(.folImplies(try f.n(.folIff(A, B)), try f.n(.folBottom)))
    #expect(root == (try f.letters(2, try f.n(.folImplies(left, right)))))
}

@Test func aMalformedLineIsRefused() throws {
    var t = Table()
    #expect(throws: ParseError.self) { try parse(schema: "schema s [A(0)]: ((A <-> A)", in: &t) }
    #expect(throws: ParseError.self) { try parse(schema: "schema s [A(0)]: (A <-> C)", in: &t) }
    #expect(throws: ParseError.self) { try parse(schema: "schema s [P(1)]: (P(x) <-> P(x))", in: &t) }
    #expect(throws: ParseError.self) { try parse(schema: "claim s: (A <-> A)", in: &t) }
    #expect(throws: ParseError.self) { try parse(schema: "schema s [A(0)]: (A <-> A) trailing", in: &t) }
}

/// The schemas Logic cites parse from base's own files.
@Test func theSchemasLogicCitesParseFromBase() throws {
    let tiers = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
        .deletingLastPathComponent().appendingPathComponent("base/tiers")
    let texts = try ["cong.fol.def", "logic.fol.def"].map { try String(contentsOf: tiers.appendingPathComponent($0), encoding: .utf8) }
    var f = Formulas()
    let names = ["iff_refl", "iff_symm", "iff_trans", "cong_not", "cong_and", "cong_or", "cong_imp", "cong_iff"]
    let parsed = try parse(statements: names, from: texts, in: &f.t)
    #expect(Set(parsed.keys) == Set(names))
    let A = try f.v(0)
    #expect(parsed["iff_refl"] == (try f.letters(1, try f.n(.folIff(A, A)))))
    #expect(throws: ParseError.self) { try parse(statements: ["no_such_schema"], from: texts, in: &f.t) }
}

private struct Claims {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func b(_ k: Int) throws -> NodeID { try n(.folBound(k)) }
    mutating func p(_ name: String, _ xs: NodeID...) throws -> NodeID { try n(.folPred(.base(name), args: xs)) }
    mutating func all(_ body: NodeID) throws -> NodeID { try n(.folForall(body: body)) }
}

/// A claim's variables are its quantifiers' own, the innermost `folBound(0)`; its atoms are base's predicates.
@Test func aClaimLineParsesToItsQuantifiersAndAtoms() throws {
    var c = Claims()
    let line = "claim cong_elem_l: forall a. forall b. forall t. (eq(a,b) -> (elem(a,t) <-> elem(b,t)))"
    let (name, root) = try parse(claim: line, in: &c.t)
    let (a, b, t) = (try c.b(2), try c.b(1), try c.b(0))
    let body = try c.n(.folImplies(try c.p("eq", a, b), try c.n(.folIff(try c.p("elem", a, t), try c.p("elem", b, t)))))
    #expect(name == "cong_elem_l")
    #expect(root == (try c.all(try c.all(try c.all(body)))))
}

/// A guarded `∃` and a quantifier under a connective, as `apply_EX` has them.
@Test func aGuardedExistentialParses() throws {
    var c = Claims()
    let (_, root) = try parse(claim: "claim apply_EX: forall F. (forall t. (set(t) -> (exists r. (set(r) & apply(t,r,F)))))", in: &c.t)
    let witness = try c.n(.folExists(body: try c.n(.folAnd(try c.p("set", try c.b(0)), try c.p("apply", try c.b(1), try c.b(0), try c.b(2))))))
    #expect(root == (try c.all(try c.all(try c.n(.folImplies(try c.p("set", try c.b(0)), witness))))))
}

/// A primitive's class predicate is that constant's, typed, as Reify writes it.
@Test func aPrimitivesClassPredicateParsesAsItsConstant() throws {
    var c = Claims()
    let (_, root) = try parse(claim: "claim ZF_Base.zero_EX: exists v. (set(v) & ZF_Base.zero(v))", in: &c.t)
    let zero = try c.n(.folPred(.constant(.primitive(.zf(.zero))), args: [try c.b(0)]))
    #expect(root == (try c.n(.folExists(body: try c.n(.folAnd(try c.p("set", try c.b(0)), zero))))))
}

@Test func aMalformedClaimIsRefused() throws {
    var t = Table()
    #expect(throws: ParseError.self) { try parse(claim: "claim s: forall a. elem(a,b)", in: &t) }
    #expect(throws: ParseError.self) { try parse(claim: "claim s: forall a. (elem(a,a)", in: &t) }
    #expect(throws: ParseError.self) { try parse(claim: "schema s [A(0)]: (A <-> A)", in: &t) }
}

/// The claims Reify cites parse from base's own files, axioms and claims alike.
@Test func theClaimsReifyCitesParseFromBase() throws {
    let directory = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
        .deletingLastPathComponent().appendingPathComponent("base")
    var c = Claims()
    let names = ["eq_refl", "eq_symm", "cong_elem_l", "cong_elem_r", "cong_eq_l", "cong_eq_r", "cong_snoc_v", "apply_EX",
                 "apply_UNIQ"]
    let parsed = try parse(statements: names, from: try baseTexts(directory), in: &c.t)
    #expect(Set(parsed.keys) == Set(names))
    #expect(parsed["eq_refl"] == (try c.all(try c.p("eq", try c.b(0), try c.b(0)))))
}
