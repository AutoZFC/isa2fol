import Foundation
import IR
import Testing
import YXML
@testable import Reader

private let falsum = trueprop(const("IFOL.False"))
private let termClass = { (T: String) in ofclass(T, "IFOL.term") }
private func imp(_ a: String, _ b: String) -> String { app(const("Pure.imp"), a, b) }
private func all(_ x: String, _ T: String, _ body: String) -> String { app(const("Pure.all", T), lam(x, T, body)) }
private func eq(_ T: String, _ a: String) -> String { trueprop(app(const("IFOL.eq", T), a, a)) }
private let ballT = fn(i, fn(fn(i, o), o))
private let ballA = trueprop(app(const("ZF_Base.Ball"), free("A"), lam("x", i, app(const("ZF_Base.mem"), bound(0), free("A")))))
private let ballDef = app(const("Pure.eq", ballT), const("ZF_Base.Ball"),
    lam("A", i, lam("P", fn(i, o), app(const("IFOL.All", i), lam("x", i,
        app(const("IFOL.imp"), app(const("ZF_Base.mem"), bound(0), bound(2)), app(bound(1), bound(0))))))))

/// A miniature export; every proof concludes its statement, as the reader checks:
///   T.M  (named)   False                 axiom T.onlyInM, a theory's own axiom
///   T.N  (named)   False                 cite T.M: N's closure holds M's
///   box 30         OFCLASS(i, term)      axiom T.termI
///   T.Q  (named)   b = b                 reflAx[i] %% box 30 % b, a theory's own axiom
///   T.B  (named)   Ball(A, λx. x ∈ A)    axiom T.ballAx % A: Ball OCCURS, so its definition is in the closure
///   T.D  (named)   Ball ≡ λA P. …        axiom ZF_Base.Ball_def_raw: the definition CITED
///   T.O  (named)   False                 oracle: refused, not followed
///   T.P  (named)   OFCLASS('a, term) ⟹ x = x   polymorphic, restricted to term, so read at i: λH. reflAx['a] %% H % x
private func census() throws -> Census {
    let theorems: [(String, Int, String)] = [
        ("T.N", 10, proofFile(frees: [], prop: falsum, proof: pcite(20, "ZF.T", "T.M"))),
        ("T.M", 20, proofFile(frees: [], prop: falsum, proof: paxiom("T.onlyInM"))),
        ("T.Q", 40, proofFile(frees: [("b", i)], prop: eq(i, free("b")),
                              proof: pappt(pappp(paxiom("T.reflAx", i), pcite(30, "ZF.T")), free("b")))),
        ("T.B", 50, proofFile(frees: [("A", i)], prop: ballA, proof: pappt(paxiom("T.ballAx"), free("A")))),
        ("T.D", 60, proofFile(frees: [], prop: ballDef, proof: paxiom("ZF_Base.Ball_def_raw"))),
        ("T.O", 70, proofFile(frees: [], prop: falsum, proof: poracle("skip_proof"))),
        ("T.P", 80, proofFile(tfrees: ["'a"], frees: [("x", typeA)], prop: imp(termClass(typeA), eq(typeA, free("x"))),
                              proof: pabsp("H", termClass(typeA), pappt(pappp(paxiom("T.reflAx", typeA), pbound(0)), free("x"))))),
    ]
    var files: [String: String] = [
        "IFOL/theory/axioms": termClassDef,
        "ZF.ZF_Base/theory/axioms": axiomEntity("ZF_Base.Ball_def_raw", prop: ballDef),
        "ZF.T/theory/axioms": axiomEntity("T.onlyInM", prop: falsum) + axiomEntity("T.termI", prop: termClass(i))
            + axiomEntity("T.ballAx", frees: [("A", i)], prop: ballA)
            + axiomEntity("T.reflAx", tfrees: ["'a"], prop: imp(termClass(typeA), all("a", typeA, eq(typeA, bound(0))))),
        "ZF.T/theory/thms": thmsFile(theorems.map { ($0.0, $0.1) }),
        "ZF.T/proofs/30": proofFile(frees: [], prop: termClass(i), proof: paxiom("T.termI")),
    ]
    for (_, serial, text) in theorems { files["ZF.T/proofs/\(serial)"] = text }
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    var reader = try Reader(try Export(root: root))
    return try reader.census()
}

private let ballType = IRType.fn(.i, .fn(.fn(.i, .o), .o))

@Test func thePopulationIsTheNamedTheoremsOfTheZFSessions() throws {
    let c = try census()
    #expect(c.named == ["ZF": 7])
    #expect(c.polymorphic == 1, "T.P")
    #expect(c.refused == [.oracle("skip_proof"): 1], "T.O is counted, and not followed")
}

/// A citation is counted by what the reader types it as, never by its name.
@Test func aCitationIsCountedOncePerTheoremWhoseClosureHoldsIt() throws {
    let c = try census()
    #expect(c.citations[.theoryAxiom("T.onlyInM")] == 2, "M, and N through the named M")
    #expect(c.citations[.theoryAxiom("T.reflAx")] == 2, "Q, and P read at i")
    #expect(c.citations[.theoryAxiom("T.termI")] == 1, "Q, through the unnamed box 30")
    #expect(c.definitions[CitedDefinition(axiom: "ZF_Base.Ball_def_raw", defines: .constant(Defined(.zf, "ZF_Base.Ball", .object)))] == 1,
            "D cites the definition; B only uses the constant")
}

/// A pattern is a primitive at its type; the closure holds the definition of every constant that occurs.
@Test func aPatternIsCountedThroughCitationsBoxesAndDefinitions() throws {
    let c = try census()
    #expect(c.patterns[.isaOfClass(.i)] == 2, "box 30's statement in Q's proof, and P's premise read at i")
    #expect(c.patterns[.isaPropAll] == 2, "Q and P, through the class's definition, as a constant's")
    #expect(c.patterns[.use(.theoryAxiom, [.i], .o)] == 2, "Q, and P read at i")
    #expect(c.patterns[.use(.theoryAxiom, [.variable("'a")], .o)] == nil, "no theorem is read at 'a")
    let ball = Pattern.isaConst(.defined(.zf, .object), ballType, args: [.i, .fn(.i, .o)])
    #expect(c.patterns[ball] == 2, "B's statement and D's")
    let definitionEquality = Pattern.isaConst(.primitive(.pure(.eq)), .fn(ballType, .fn(ballType, .o)), args: [ballType, ballType])
    #expect(c.patterns[definitionEquality] == 2, "D's statement, and B through Ball's definition")
}
