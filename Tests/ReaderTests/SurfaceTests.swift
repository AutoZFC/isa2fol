import Foundation
import Testing
import YXML
@testable import Reader

/// A miniature export, one fixture per rule of the cut:
///   IFOL.refl        OFCLASS('a, IFOL.term) ⟹ a = a   a logic-layer rule with ONE class premise
///   T.N  (named)     refl %% cite 40 %% cite 30         40 discharges refl's class premise; 30 is a real premise
///   T.M  (named)     axiom T.onlyInM                    cited by box 30: the cut stops at it
///   box 30           statement A &&& A; proof: Pure.reflexive %% cite T.M
///   box 40           OFCLASS(i, IFOL.term); proof: axiom T.classMachinery
///   T.P  (named)     cite 30                            box 30 shared with N
///   T.arity (named)  OFCLASS('a, IFOL.term)             a statement with a class and a type variable
///   box 70           OFCLASS('a, IFOL.term) ⟹ x = x     polymorphic; its proof binds the class hypothesis H
///                    and discharges refl's class premise with it: λH. refl['a] %% H
///   T.Q  (named)     cite 70 at i %% cite 40            the instance at i; 40 discharges 70's class premise
private func miniExport() throws -> String {
    let root = FileManager.default.temporaryDirectory.appendingPathComponent("isa2fol-surface-\(UUID())").path
    func write(_ path: String, _ text: String) throws {
        let full = "\(root)/\(path)"
        try FileManager.default.createDirectory(atPath: (full as NSString).deletingLastPathComponent, withIntermediateDirectories: true)
        try text.write(toFile: full, atomically: true, encoding: .utf8)
    }
    func thms(_ entries: [(String, Int)]) -> String {
        entries.map { element("entity", [("name", $0.0), ("serial", String($0.1))], []) }.joined()
    }
    let falsum = trueprop(const("IFOL.False"))
    try write("IFOL/theory/thms", thms([("IFOL.refl", 222)]))
    try write("IFOL/proofs/222", proofFile(tfrees: ["'a"], frees: [("a", typeA)],
        prop: app(const("Pure.imp"), ofclass(typeA, "IFOL.term"), trueprop(app(const("IFOL.eq", typeA), free("a"), free("a"))))))
    try write("ZF.T/theory/thms", thms([("T.N", 10), ("T.M", 20), ("T.P", 50), ("T.arity", 60), ("T.Q", 80)]))
    try write("ZF.T/proofs/10", proofFile(frees: [], prop: falsum,
        proof: pappp(pcite(222, "IFOL", "IFOL.refl", i), pcite(40, "ZF.T"), pcite(30, "ZF.T"))))
    try write("ZF.T/proofs/20", proofFile(frees: [], prop: falsum, proof: paxiom("T.onlyInM")))
    try write("ZF.T/proofs/30", proofFile(frees: [], prop: app(const("Pure.conjunction"), falsum, falsum),
        proof: pappp(paxiom("Pure.reflexive"), pcite(20, "ZF.T", "T.M"))))
    try write("ZF.T/proofs/40", proofFile(frees: [], prop: ofclass(i, "IFOL.term"), proof: paxiom("T.classMachinery")))
    try write("ZF.T/proofs/50", proofFile(frees: [], prop: falsum, proof: pcite(30, "ZF.T")))
    try write("ZF.T/proofs/60", proofFile(tfrees: ["'a"], frees: [], prop: ofclass(typeA, "IFOL.term")))
    try write("ZF.T/proofs/70", proofFile(tfrees: ["'a"], frees: [("x", typeA)],
        prop: app(const("Pure.imp"), ofclass(typeA, "IFOL.term"), trueprop(app(const("IFOL.eq", typeA), free("x"), free("x")))),
        proof: pabsp("H", ofclass(typeA, "IFOL.term"), pappp(pcite(222, "IFOL", "IFOL.refl", typeA), pbound(0)))))
    try write("ZF.T/proofs/80", proofFile(frees: [], prop: falsum, proof: pappp(pcite(70, "ZF.T", "", i), pcite(40, "ZF.T"))))
    return root
}

private func survey() throws -> Surface {
    let root = try miniExport()
    defer { try? FileManager.default.removeItem(atPath: root) }
    var export = try Export(root: root)
    return try export.surface()
}

@Test func thePopulationIsTheNamedTheoremsOfTheZFSessions() throws {
    #expect(try survey().named == ["ZF": 5])
}

@Test func aProofInlinesTheUnnamedBoxesItReachesAndStopsAtNamedTheorems() throws {
    let s = try survey()
    #expect(s.proof[Item(.axiom, "Pure.reflexive")] == 2, "N and P reach it through box 30")
    #expect(s.proof[Item(.axiom, "T.onlyInM")] == 1, "only M: N's proof stops at the named M")
    #expect(s.citedZF == 1, "M, reached through box 30")
}

/// A class discharge is a proof argument like any other (DESIGN §4.3a 5c).
@Test func aClassDischargeIsWalkedLikeAnyArgument() throws {
    let s = try survey()
    #expect(s.proof[Item(.theorem, "IFOL.refl")] == 2, "N directly, Q through box 70")
    #expect(s.proof[Item(.axiom, "T.classMachinery")] == 2, "box 40 discharges a class premise in N and in Q")
    #expect(s.proof[Item(.ofclass, "IFOL.term")] == 2, "box 40's statement in N and Q, box 70's hypothesis in Q")
}

@Test func aBoxStatementIsPartOfItsCitersProof() throws {
    let s = try survey()
    #expect(s.proof[Item(.constant, "Pure.conjunction")] == 2)
    #expect(s.statement[Item(.constant, "Pure.conjunction")] == nil)
}

@Test func statementsCountEveryConstructNotOnlyConstants() throws {
    let s = try survey()
    #expect(s.statement[Item(.constant, "IFOL.False")] == 4, "N, M, P, Q")
    #expect(s.statement[Item(.ofclass, "IFOL.term")] == 1)
    #expect(s.statement[Item(.typeVariable, "")] == 1)
}

@Test func aPolymorphicBoxEntersItsCitersProofAsTheInstanceUsed() throws {
    let s = try survey()
    #expect(s.proof[Item(.typeVariable, "")] == nil, "box 70 is cited at i")
    #expect(s.proof[Item(.constant, "IFOL.eq")] == 1, "box 70's statement, in Q's proof")
    #expect(s.proof[Item(.calculus, "⟹-intro")] == 1, "Q, through box 70 binding its class hypothesis")
}
