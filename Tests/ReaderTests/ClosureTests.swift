import Foundation
import Testing
import YXML
@testable import Reader

/// A miniature export for the closure — every citation followed down to axioms and oracles:
///   IFOL.impI  (named)   axiom IFOL.impI                      an axiom restated
///   IFOL.D     (named)   impI %% cite box 5                   a derived rule
///   box 5      (IFOL)    axiom IFOL.not_def                   a definition, under the derived rule
///   IFOL.refl  (named)   OFCLASS('a, IFOL.term) ⟹ a = a; its proof: axiom IFOL.refl at 'a
///   T.N        (named)   refl[i] %% cite 40 %% D %% cite T.M  40 discharges refl's class premise
///   T.M        (named)   axiom ZF_Base.extension              reached by N through a NAMED theorem
///   box 40               axiom T.classMachinery               only ever a class discharge
///   T.P        (named)   cite box 60
///   box 60               oracle skip_proof
///   T.Q        (named)   axiom Pure.reflexive at 'b           'b is bound by nothing: Q has no type variables
private func miniExport() throws -> String {
    let root = FileManager.default.temporaryDirectory.appendingPathComponent("isa2fol-closure-\(UUID())").path
    func write(_ path: String, _ text: String) throws {
        let full = "\(root)/\(path)"
        try FileManager.default.createDirectory(atPath: (full as NSString).deletingLastPathComponent, withIntermediateDirectories: true)
        try text.write(toFile: full, atomically: true, encoding: .utf8)
    }
    func thms(_ entries: [(String, Int)]) -> String {
        entries.map { element("entity", [("name", $0.0), ("serial", String($0.1))], []) }.joined()
    }
    let falsum = trueprop(const("IFOL.False"))
    try write("IFOL/theory/thms", thms([("IFOL.impI", 1), ("IFOL.D", 2), ("IFOL.refl", 222)]))
    try write("IFOL/proofs/1", proofFile(frees: [], prop: falsum, proof: paxiom("IFOL.impI")))
    try write("IFOL/proofs/2", proofFile(frees: [], prop: falsum, proof: pappp(pcite(1, "IFOL", "IFOL.impI"), pcite(5, "IFOL"))))
    try write("IFOL/proofs/5", proofFile(frees: [], prop: falsum, proof: paxiom("IFOL.not_def")))
    try write("IFOL/proofs/222", proofFile(tfrees: ["'a"], frees: [("a", typeA)],
        prop: app(const("Pure.imp"), ofclass(typeA, "IFOL.term"), trueprop(app(const("IFOL.eq", typeA), free("a"), free("a")))),
        proof: paxiom("IFOL.refl", typeA)))
    try write("ZF.T/theory/thms", thms([("T.N", 10), ("T.M", 20), ("T.P", 50), ("T.Q", 70)]))
    try write("ZF.T/proofs/10", proofFile(frees: [], prop: falsum,
        proof: pappp(pcite(222, "IFOL", "IFOL.refl", i), pcite(40, "ZF.T"), pcite(2, "IFOL", "IFOL.D"), pcite(20, "ZF.T", "T.M"))))
    try write("ZF.T/proofs/20", proofFile(frees: [], prop: falsum, proof: paxiom("ZF_Base.extension")))
    try write("ZF.T/proofs/40", proofFile(frees: [], prop: ofclass(i, "IFOL.term"), proof: paxiom("T.classMachinery")))
    try write("ZF.T/proofs/50", proofFile(frees: [], prop: falsum, proof: pcite(60, "ZF.T")))
    try write("ZF.T/proofs/60", proofFile(frees: [], prop: falsum, proof: poracle("skip_proof")))
    try write("ZF.T/proofs/70", proofFile(frees: [], prop: falsum, proof: paxiom("Pure.reflexive", tfree("'b"))))
    return root
}

private func closure() throws -> Closure {
    let root = try miniExport()
    defer { try? FileManager.default.removeItem(atPath: root) }
    var export = try Export(root: root)
    return try export.closure()
}

@Test func theClosureFollowsEveryCitationDownToAxioms() throws {
    let c = try closure()
    #expect(c.leaves[Item(.axiom, "IFOL.impI")] == 1, "N, through the derived rule D")
    #expect(c.leaves[Item(.axiom, "IFOL.not_def")] == 1, "N, through D's box")
    #expect(c.leaves[Item(.axiom, "IFOL.refl")] == 1)
    #expect(c.leaves[Item(.axiom, "ZF_Base.extension")] == 2, "M, and N through the named M")
}

@Test func theClosureKeepsClassPremiseDischargesAbsorbed() throws {
    #expect(try closure().leaves[Item(.axiom, "T.classMachinery")] == nil)
}

@Test func theClosureReportsOracles() throws {
    #expect(try closure().leaves[Item(.oracle, "skip_proof")] == 1)
}

@Test func aCitationAtATypeVariableNothingBindsIsReported() throws {
    let c = try closure()
    #expect(c.unboundTypeVariables == ["ZF.T/proofs/70 cites Pure.reflexive at 'b"])
    #expect(c.named == ["ZF": 4])
}
