import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func mimp(_ a: String, _ b: String) -> String {
    app(const("Pure.imp"), a, b)
}

private func mall(_ x: String, _ T: String, _ body: String) -> String {
    app(const("Pure.all", T), lam(x, T, body))
}

private func meq(_ T: String, _ a: String, _ b: String) -> String {
    app(const("Pure.eq", T), a, b)
}

private func conj(_ a: String, _ b: String) -> String {
    app(const("IFOL.conj"), a, b)
}

private func disj(_ a: String, _ b: String) -> String {
    app(const("IFOL.disj"), a, b)
}

private func imp(_ a: String, _ b: String) -> String {
    app(const("IFOL.imp"), a, b)
}

private func not(_ a: String) -> String {
    app(const("IFOL.Not"), a)
}

private func iff(_ a: String, _ b: String) -> String {
    app(const("IFOL.iff"), a, b)
}

private func eq(_ T: String, _ a: String, _ b: String) -> String {
    app(const("IFOL.eq", T), a, b)
}

private func forall(_ x: String, _ T: String, _ body: String) -> String {
    app(const("IFOL.All", T), lam(x, T, body))
}

private func exists(_ x: String, _ T: String, _ body: String) -> String {
    app(const("IFOL.Ex", T), lam(x, T, body))
}

private let falsum = const("IFOL.False")
private let classed = ofclass(typeA, "IFOL.term")
private let b0 = bound(0)
private let b1 = bound(1)
private let b2 = bound(2)
private let A = free("A")
private let B = free("B")
private let C = free("C")
private let R = free("R")
private let P = free("P")
private let a = free("a")
private let f = free("f")
private let b = free("b")
private let Pi = fn(i, o)

/// The rules of `IFOL.thy` and `FOL.thy` as the export states them: closed by `⋀`, a rule over `'a :: term` with the
/// class
/// as its first premise.
private let logicAxioms = [
    axiomEntity(
        "IFOL.conjI",
        prop: mall("P", o, mall("Q", o, mimp(trueprop(b1), mimp(trueprop(b0), trueprop(conj(b1, b0)))))),
    ),
    axiomEntity("IFOL.conjunct1", prop: mall("P", o, mall("Q", o, mimp(trueprop(conj(b1, b0)), trueprop(b1))))),
    axiomEntity("IFOL.conjunct2", prop: mall("P", o, mall("Q", o, mimp(trueprop(conj(b1, b0)), trueprop(b0))))),
    axiomEntity("IFOL.disjI1", prop: mall("P", o, mall("Q", o, mimp(trueprop(b1), trueprop(disj(b1, b0)))))),
    axiomEntity("IFOL.disjI2", prop: mall("P", o, mall("Q", o, mimp(trueprop(b0), trueprop(disj(b1, b0)))))),
    axiomEntity("IFOL.disjE", prop: mall("P", o, mall("Q", o, mall("R", o, mimp(
        trueprop(disj(b2, b1)),
        mimp(
            mimp(trueprop(b2), trueprop(b0)),
            mimp(
                mimp(
                    trueprop(b1),
                    trueprop(b0),
                ),
                trueprop(b0),
            ),
        ),
    ))))),
    axiomEntity(
        "IFOL.impI",
        prop: mall("P", o, mall("Q", o, mimp(mimp(trueprop(b1), trueprop(b0)), trueprop(imp(b1, b0))))),
    ),
    axiomEntity(
        "IFOL.mp",
        prop: mall("P", o, mall("Q", o, mimp(trueprop(imp(b1, b0)), mimp(trueprop(b1), trueprop(b0))))),
    ),
    axiomEntity("IFOL.FalseE", prop: mall("P", o, mimp(trueprop(falsum), trueprop(b0)))),
    axiomEntity("IFOL.iff_reflection", prop: mall("P", o, mall("Q", o, mimp(trueprop(iff(b1, b0)), meq(o, b1, b0))))),
    axiomEntity("IFOL.refl", tfrees: ["'a"], prop: mimp(classed, mall("a", typeA, trueprop(eq(typeA, b0, b0))))),
    axiomEntity(
        "IFOL.subst",
        tfrees: ["'a"],
        prop: mimp(classed, mall("a", typeA, mall("b", typeA, mall(
            "P",
            fn(typeA, o),
            mimp(
                trueprop(eq(
                    typeA,
                    b2,
                    b1,
                )),
                mimp(
                    trueprop(app(
                        b0,
                        b2,
                    )),
                    trueprop(app(
                        b0,
                        b1,
                    )),
                ),
            ),
        )))),
    ),
    axiomEntity("IFOL.allI", tfrees: ["'a"], prop: mimp(classed, mall(
        "P",
        fn(typeA, o),
        mimp(
            mall("x", typeA, trueprop(app(b1, b0))),
            trueprop(forall("x", typeA, app(b1, b0))),
        ),
    ))),
    axiomEntity("IFOL.spec", tfrees: ["'a"], prop: mimp(classed, mall("P", fn(typeA, o), mall(
        "x",
        typeA,
        mimp(
            trueprop(forall(
                "xa",
                typeA,
                app(b2, b0),
            )),
            trueprop(app(b1, b0)),
        ),
    )))),
    axiomEntity("IFOL.exI", tfrees: ["'a"], prop: mimp(classed, mall("P", fn(typeA, o), mall(
        "x",
        typeA,
        mimp(
            trueprop(app(b1, b0)),
            trueprop(exists(
                "xa",
                typeA,
                app(b2, b0),
            )),
        ),
    )))),
    axiomEntity("IFOL.exE", tfrees: ["'a"], prop: mimp(classed, mall("P", fn(typeA, o), mall(
        "R",
        o,
        mimp(
            trueprop(exists(
                "x",
                typeA,
                app(b2, b0),
            )),
            mimp(
                mall(
                    "x",
                    typeA,
                    mimp(
                        trueprop(app(
                            b2,
                            b0,
                        )),
                        trueprop(b1),
                    ),
                ),
                trueprop(b0),
            ),
        ),
    )))),
    axiomEntity("IFOL.eq_reflection", tfrees: ["'a"], prop: mimp(classed, mall("x", typeA, mall(
        "y",
        typeA,
        mimp(
            trueprop(eq(
                typeA,
                b1,
                b0,
            )),
            meq(typeA, b1, b0),
        ),
    )))),
].joined()

private func at(_ p: String, _ terms: String...) -> String {
    terms.reduce(p, pappt)
}

private func atI(_ rule: String, _ discharge: String, _ terms: String...) -> String {
    terms.reduce(pappp(paxiom(rule, i), discharge), pappt)
}

private let sortAlgebra = pofclass(i, "IFOL.term")

/// One theorem per rule, each applying it to the theorem's own hypotheses. A rule over `'a :: term` is discharged by
/// `sortAlgebra`, which the reader refuses wherever it reads it, or by box 95, which it reads.
private func logicReader() throws -> Reader {
    let theorems: [(String, Int, String)] = [
        (
            "T.conjI",
            10,
            proofFile(
                frees: [("A", o), ("B", o)],
                prop: mimp(trueprop(A), mimp(trueprop(B), trueprop(conj(A, B)))),
                proof: pabsp("a", trueprop(A), pabsp(
                    "b",
                    trueprop(B),
                    pappp(
                        at(paxiom("IFOL.conjI"), A, B),
                        pbound(1),
                        pbound(0),
                    ),
                )),
            ),
        ),
        (
            "T.conjIFact",
            11,
            proofFile(
                frees: [("A", o), ("B", o)],
                prop: mimp(trueprop(A), mimp(trueprop(B), trueprop(conj(A, B)))),
                proof: at(paxiom("IFOL.conjI"), A, B),
            ),
        ),
        ("T.conjunct1", 12, proofFile(
            frees: [("A", o), ("B", o)],
            prop: mimp(trueprop(conj(A, B)), trueprop(A)),
            proof: pabsp(
                "h",
                trueprop(conj(A, B)),
                pappp(at(paxiom("IFOL.conjunct1"), A, B), pbound(0)),
            ),
        )),
        ("T.conjunct2", 13, proofFile(
            frees: [("A", o), ("B", o)],
            prop: mimp(trueprop(conj(A, B)), trueprop(B)),
            proof: pabsp(
                "h",
                trueprop(conj(A, B)),
                pappp(at(paxiom("IFOL.conjunct2"), A, B), pbound(0)),
            ),
        )),
        ("T.disjI1", 14, proofFile(
            frees: [("A", o), ("B", o)],
            prop: mimp(trueprop(A), trueprop(disj(A, B))),
            proof: pabsp("h", trueprop(A), pappp(at(paxiom("IFOL.disjI1"), A, B), pbound(0))),
        )),
        ("T.disjI2", 15, proofFile(
            frees: [("B", o), ("A", o)],
            prop: mimp(trueprop(B), trueprop(disj(A, B))),
            proof: pabsp("h", trueprop(B), pappp(at(paxiom("IFOL.disjI2"), A, B), pbound(0))),
        )),
        ("T.disjE", 16, proofFile(
            frees: [("A", o), ("B", o), ("C", o)],
            prop: mimp(
                trueprop(disj(A, B)),
                mimp(
                    mimp(trueprop(A), trueprop(C)),
                    mimp(mimp(trueprop(B), trueprop(C)), trueprop(C)),
                ),
            ),
            proof: pabsp("h", trueprop(disj(A, B)), pabsp(
                "k",
                mimp(trueprop(A), trueprop(C)),
                pabsp(
                    "l",
                    mimp(trueprop(B), trueprop(C)),
                    pappp(
                        at(
                            paxiom("IFOL.disjE"),
                            A,
                            B,
                            C,
                        ),
                        pbound(2),
                        pbound(1),
                        pbound(0),
                    ),
                ),
            )),
        )),
        (
            "T.impI",
            17,
            proofFile(
                frees: [("A", o), ("B", o)],
                prop: mimp(mimp(trueprop(A), trueprop(B)), trueprop(imp(A, B))),
                proof: pabsp(
                    "h",
                    mimp(trueprop(A), trueprop(B)),
                    pappp(at(paxiom("IFOL.impI"), A, B), pbound(0)),
                ),
            ),
        ),
        (
            "T.mp",
            18,
            proofFile(
                frees: [("A", o), ("B", o)],
                prop: mimp(trueprop(imp(A, B)), mimp(trueprop(A), trueprop(B))),
                proof: pabsp("h", trueprop(imp(A, B)), pabsp(
                    "a",
                    trueprop(A),
                    pappp(
                        at(paxiom("IFOL.mp"), A, B),
                        pbound(1),
                        pbound(0),
                    ),
                )),
            ),
        ),
        ("T.FalseE", 19, proofFile(
            frees: [("A", o)],
            prop: mimp(trueprop(falsum), trueprop(A)),
            proof: pabsp(
                "h",
                trueprop(falsum),
                pappp(at(paxiom("IFOL.FalseE"), A), pbound(0)),
            ),
        )),
        ("T.classical", 20, proofFile(
            frees: [("A", o)],
            prop: mimp(mimp(trueprop(not(A)), trueprop(A)), trueprop(A)),
            proof: pabsp(
                "h",
                mimp(trueprop(not(A)), trueprop(A)),
                pappp(at(paxiom("FOL.classical"), A), pbound(0)),
            ),
        )),
        ("T.iffReflection", 21, proofFile(
            frees: [("A", o), ("B", o)],
            prop: mimp(trueprop(iff(A, B)), meq(o, A, B)),
            proof: pabsp(
                "h",
                trueprop(iff(A, B)),
                pappp(at(paxiom("IFOL.iff_reflection"), A, B), pbound(0)),
            ),
        )),
        (
            "T.allI",
            22,
            proofFile(
                frees: [("P", Pi)],
                prop: mimp(mall("x", i, trueprop(app(P, b0))), trueprop(forall("x", i, app(P, b0)))),
                proof: pabsp(
                    "h",
                    mall("x", i, trueprop(app(P, b0))),
                    pappp(atI("IFOL.allI", sortAlgebra, P), pbound(0)),
                ),
            ),
        ),
        (
            "T.spec",
            23,
            proofFile(
                frees: [("P", Pi), ("a", i)],
                prop: mimp(trueprop(forall("x", i, app(P, b0))), trueprop(app(P, a))),
                proof: pabsp(
                    "h",
                    trueprop(forall("x", i, app(P, b0))),
                    pappp(atI("IFOL.spec", sortAlgebra, P, a), pbound(0)),
                ),
            ),
        ),
        (
            "T.refl",
            24,
            proofFile(frees: [("a", i)], prop: trueprop(eq(i, a, a)), proof: atI("IFOL.refl", sortAlgebra, a)),
        ),
        ("T.eqReflection", 25, proofFile(
            frees: [("a", i), ("b", i)],
            prop: mimp(trueprop(eq(i, a, b)), meq(i, a, b)),
            proof: pabsp(
                "h",
                trueprop(eq(i, a, b)),
                pappp(atI("IFOL.eq_reflection", sortAlgebra, a, b), pbound(0)),
            ),
        )),
        ("T.exE", 26, proofFile(
            frees: [("P", Pi), ("R", o)],
            prop: mimp(
                trueprop(exists("x", i, app(P, b0))),
                mimp(mall("x", i, mimp(trueprop(app(P, b0)), trueprop(R))), trueprop(R)),
            ),
            proof: pabsp(
                "h",
                trueprop(exists("x", i, app(P, b0))),
                pabsp(
                    "k",
                    mall("x", i, mimp(trueprop(app(P, b0)), trueprop(R))),
                    pappp(
                        atI(
                            "IFOL.exE",
                            sortAlgebra,
                            P,
                            R,
                        ),
                        pbound(1),
                        pbound(0),
                    ),
                ),
            ),
        )),
        (
            "T.exI",
            27,
            proofFile(
                frees: [("P", Pi), ("a", i)],
                prop: mimp(trueprop(app(P, a)), trueprop(exists("x", i, app(P, b0)))),
                proof: pabsp("h", trueprop(app(P, a)), pappp(atI("IFOL.exI", pcite(95, "ZF.T"), P, a), pbound(0))),
            ),
        ),
        (
            "T.exIAtTerm",
            30,
            proofFile(
                frees: [("P", Pi), ("f", fn(i, i)), ("a", i)],
                prop: mimp(trueprop(app(P, app(f, a))), trueprop(exists("x", i, app(P, b0)))),
                proof: pabsp(
                    "h",
                    trueprop(app(P, app(f, a))),
                    pappp(atI("IFOL.exI", pcite(95, "ZF.T"), P, app(f, a)), pbound(0)),
                ),
            ),
        ),
        ("T.subst", 28, proofFile(
            frees: [("a", i), ("b", i), ("P", Pi)],
            prop: mimp(trueprop(eq(i, a, b)), mimp(trueprop(app(P, a)), trueprop(app(P, b)))),
            proof: pabsp("h", trueprop(eq(i, a, b)), pabsp(
                "k",
                trueprop(app(P, a)),
                pappp(
                    atI(
                        "IFOL.subst",
                        pcite(95, "ZF.T"),
                        a,
                        b,
                        P,
                    ),
                    pbound(1),
                    pbound(0),
                ),
            )),
        )),
        (
            "T.missingTerm",
            29,
            proofFile(
                frees: [("A", o)],
                prop: mall("Q", o, mimp(trueprop(A), mimp(trueprop(b0), trueprop(conj(A, b0))))),
                proof: at(paxiom("IFOL.conjI"), A),
            ),
        ),
    ]
    var files: [String: String] = [
        "IFOL/theory/axioms": logicAxioms,
        "FOL/theory/axioms": axiomEntity(
            "FOL.classical",
            prop: mall("P", o, mimp(mimp(trueprop(not(b0)), trueprop(b0)), trueprop(b0))),
        ),
        "ZF.T/theory/axioms": axiomEntity("T.termI", prop: ofclass(i, "IFOL.term")),
        "ZF.T/theory/thms": thmsFile(theorems.map { ($0.0, $0.1) }),
        "ZF.T/proofs/95": proofFile(frees: [], prop: ofclass(i, "IFOL.term"), proof: paxiom("T.termI")),
    ]
    for (_, serial, text) in theorems { files["ZF.T/proofs/\(serial)"] = text }
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    return try Reader(try Export(root: root))
}

private func proof(_ r: inout Reader, _ name: String) throws -> NodeID {
    let theorem = try #require(r.population.first { r.name(of: $0) == name })
    guard case .proved(_, let proof) = try r.read(theorem) else { throw Unread(name: name) }
    return proof
}

private struct Unread: Error {
    let name: String
}

/// The proof's nodes, interned in a copy of the reader's table: equal to the read proof only when it is that node.
private struct Expected {
    var t: Table

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func v(_ k: Int, _ T: IRType = .o) throws -> NodeID {
        try n(.isaBound(k, T))
    }

    mutating func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID {
        try n(.folImpliesIntro(a, body: body))
    }

    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID {
        try n(.hyp(k, a))
    }

    mutating func fix(_ Ts: [IRType], _ body: NodeID) throws -> NodeID {
        try Ts.reversed().reduce(body) { try n(.isaAllIntro($1, body: $0)) }
    }

    mutating func applied(_ P: NodeID, _ x: NodeID) throws -> NodeID {
        try n(.isaVarApp(head: P, args: [x]))
    }
}

/// Each propositional rule applied is its step; one missing its premises is its closed proof, so `conjI` at its terms
/// alone is the same node as `conjI` applied.
@Test
func aPropositionalRuleAppliedIsItsStep() throws {
    var r = try logicReader()
    let names = [
        "T.conjI",
        "T.conjIFact",
        "T.conjunct1",
        "T.conjunct2",
        "T.disjI1",
        "T.disjI2",
        "T.disjE",
        "T.impI",
        "T.mp",
        "T.FalseE",
    ]
    let read = try Dictionary(uniqueKeysWithValues: names.map { ($0, try proof(&r, $0)) })
    var e = Expected(t: r.table)
    let A2 = try e.v(1)
    let B2 = try e.v(0)
    let and = try e.n(.folAnd(A2, B2))
    let ab = try e.n(.folImplies(A2, B2))
    let both = try e.fix(
        [.o, .o],
        try e.assume(A2, try e.assume(B2, try e.n(.folAndIntro(try e.hyp(1, A2), try e.hyp(0, B2))))),
    )
    #expect(read["T.conjI"] == both)
    #expect(read["T.conjIFact"] == both)
    #expect(read["T.conjunct1"] == (try e.fix([.o, .o], try e.assume(and, try e.n(.folAndElimL(try e.hyp(0, and)))))))
    #expect(read["T.conjunct2"] == (try e.fix([.o, .o], try e.assume(and, try e.n(.folAndElimR(try e.hyp(0, and)))))))
    #expect(read["T.disjI1"] == (try e.fix([.o, .o], try e.assume(A2, try e.n(.folOrIntroL(try e.hyp(0, A2), B2))))))
    let B1st = try e.v(1)
    let A2nd = try e.v(0)
    #expect(read["T.disjI2"] == (try e.fix(
        [.o, .o],
        try e.assume(B1st, try e.n(.folOrIntroR(A2nd, try e.hyp(0, B1st)))),
    )))
    #expect(read["T.impI"] == (try e.fix([.o, .o], try e.assume(ab, try e.hyp(0, ab)))))
    #expect(read["T.mp"] == (try e.fix(
        [.o, .o],
        try e.assume(ab, try e.assume(A2, try e.n(.folImpliesElim(try e.hyp(1, ab), try e.hyp(0, A2))))),
    )))
    let A3 = try e.v(2)
    let B3 = try e.v(1)
    let C3 = try e.v(0)
    let or3 = try e.n(.folOr(A3, B3))
    let ac = try e.n(.folImplies(A3, C3))
    let bc = try e.n(.folImplies(B3, C3))
    let cases = try e.n(.folOrElim(try e.hyp(2, or3), try e.hyp(1, ac), try e.hyp(0, bc)))
    #expect(read["T.disjE"] == (try e.fix([.o, .o, .o], try e.assume(or3, try e.assume(ac, try e.assume(bc, cases))))))
    let A1 = try e.v(0)
    let bottom = try e.n(.folBottom)
    #expect(read["T.FalseE"] == (try e.fix(
        [.o],
        try e.assume(bottom, try e.n(.folBottomElim(try e.hyp(0, bottom), A1))),
    )))
}

/// A rule over `'a :: term`, applied at `i`, is its step past its class's discharge, which is never read: `sortAlgebra`
/// would be refused.
@Test
func aQuantifierOrEqualityRuleAtIIsItsStepPastItsClassDischarge() throws {
    var r = try logicReader()
    let allI = try proof(&r, "T.allI")
    let spec = try proof(&r, "T.spec")
    let refl = try proof(&r, "T.refl")
    let reflection = try proof(&r, "T.eqReflection")
    var e = Expected(t: r.table)
    let F = IRType.fn(.i, .o)
    let every = try e.n(.ifolAll(.i, body: try e.applied(try e.v(1, F), try e.v(0, .i))))
    #expect(allI == (try e.fix([F], try e.assume(every, try e.hyp(0, every)))))
    let everyUnderA = try e.n(.ifolAll(.i, body: try e.applied(try e.v(2, F), try e.v(0, .i))))
    #expect(spec == (try e.fix(
        [F, .i],
        try e.assume(everyUnderA, try e.n(.isaAllElim(try e.hyp(0, everyUnderA), try e.v(0, .i)))),
    )))
    #expect(refl == (try e.fix([.i], try e.n(.isaReflexive(try e.v(0, .i))))))
    let ab = try e.t.equation(.i, try e.v(1, .i), try e.v(0, .i))
    #expect(reflection == (try e.fix([.i, .i], try e.assume(ab, try e.hyp(0, ab)))))
}

/// `exE` binds its witness over its minor premise: its step is its closed proof applied to its premises, an `isaExElim`
/// with no citation left.
@Test
func exEAtIIsAnExistentialEliminationWithNoCitation() throws {
    var r = try logicReader()
    let read = try proof(&r, "T.exE")
    let found = patterns(under: [read], in: r.table)
    #expect(found.contains(.isaExElim(.i, .o, body: .o)))
    #expect(!found.contains { if case .use = $0 { true } else { false } })
}

/// `classical` and `iff_reflection` hold IFOL's defined `¬` and `⟷`: each is read as its isa step, Logic's after
/// Expand.
@Test
func classicalAndIffReflectionAreReadAsTheirIsaSteps() throws {
    var r = try logicReader()
    let classical = try proof(&r, "T.classical")
    let reflection = try proof(&r, "T.iffReflection")
    var e = Expected(t: r.table)
    let A1 = try e.v(0)
    let notA = try e.n(.isaConst(.defined(Defined(.ifol, "IFOL.Not", .object)), .fn(.o, .o), args: [A1]))
    let premise = try e.n(.folImplies(notA, A1))
    #expect(classical == (try e.fix([.o], try e.assume(premise, try e.n(.isaClassical(A1, try e.hyp(0, premise)))))))
    let A2 = try e.v(1)
    let B2 = try e.v(0)
    let iffAB = try e.n(.isaConst(.defined(Defined(.ifol, "IFOL.iff", .object)), .fn(.o, .fn(.o, .o)), args: [A2, B2]))
    #expect(reflection == (try e.fix(
        [.o, .o],
        try e.assume(iffAB, try e.n(.isaIffReflection(A2, B2, try e.hyp(0, iffAB)))),
    )))
}

/// `exI` is an ∃-intro given its body, its λ's, past its class's discharge, at a variable and at a compound term alike
/// (DESIGN "An ∃-intro carrying its body"); `subst` stays a citation, its class's discharge an ordinary premise.
@Test
func exIIsAnExistentialIntroGivenItsBodyAndSubstStaysACitation() throws {
    var r = try logicReader()
    let exI = try proof(&r, "T.exI")
    let atTerm = try proof(&r, "T.exIAtTerm")
    let subst = try proof(&r, "T.subst")
    var e = Expected(t: r.table)
    let F = IRType.fn(.i, .o)
    let G = IRType.fn(.i, .i)
    let atA = try e.applied(try e.v(1, F), try e.v(0, .i))
    let some = try e.applied(try e.v(2, F), try e.v(0, .i))
    #expect(exI == (try e.fix(
        [F, .i],
        try e.assume(atA, try e.n(.isaExIntro(try e.hyp(0, atA), try e.v(0, .i), body: some))),
    )))
    let fa = try e.applied(try e.v(1, G), try e.v(0, .i))
    let atFA = try e.applied(try e.v(2, F), fa)
    let someF = try e.applied(try e.v(3, F), try e.v(0, .i))
    #expect(atTerm == (try e.fix(
        [F, G, .i],
        try e.assume(atFA, try e.n(.isaExIntro(try e.hyp(0, atFA), fa, body: someF))),
    )))
    #expect(patterns(under: [subst], in: r.table).contains(.use(.axiom(.ifol(.subst)), [.i], .o)))
    #expect(patterns(under: [subst], in: r.table).contains(.use(.theoryAxiom, [], .o)))
}

/// A rule missing a term stops the read, as Pure's does.
@Test
func aRuleMissingATermStopsTheRead() throws {
    var r = try logicReader()
    let theorem = try #require(r.population.first { r.name(of: $0) == "T.missingTerm" })
    do {
        let outcome = try r.read(theorem)
        Issue.record("read as \(outcome)")
    } catch let f as ReadFailure {
        #expect(f.error as? MalformedExport == .applicationArity("IFOL.conjI", expected: 2, found: 1))
    }
}
