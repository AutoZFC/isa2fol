import Foundation
import IR
import Testing
import YXML
@testable import Reader

private let falsum = trueprop(const("IFOL.False"))
private func imp(_ a: String, _ b: String) -> String { app(const("Pure.imp"), a, b) }
private func iff(_ a: String, _ b: String) -> String { app(const("IFOL.iff"), a, b) }
private func not(_ a: String) -> String { app(const("IFOL.Not"), a) }
private func implies(_ a: String, _ b: String) -> String { app(const("IFOL.imp"), a, b) }
private func all(_ x: String, _ T: String, _ body: String) -> String { app(const("Pure.all", T), lam(x, T, body)) }
private let iffDef = app(const("Pure.eq", fn(o, fn(o, o))), const("IFOL.iff"),
                         lam("P", o, lam("Q", o, not(implies(bound(1), not(bound(0)))))))
private let notDef = app(const("Pure.eq", fn(o, o)), const("IFOL.Not"), lam("P", o, implies(bound(0), const("IFOL.False"))))
private let splitType = fn(fn(i, fn(i, typeA)), fn(i, typeA))
private let splitDef = app(const("Pure.eq", splitType), const("ZF_Base.split", typeA),
                           lam("c", fn(i, fn(i, typeA)), lam("p", i, app(bound(1), bound(0), bound(0)))))
private let aIffA = trueprop(iff(free("A"), free("A")))
private let splitAtO = trueprop(app(const("ZF_Base.split", o), lam("x", i, lam("y", i, app(const("ZF_Base.mem"), bound(1), bound(0)))),
                                    free("A")))
private let inlA = app(const("Sum.Inl"), free("a"))
private let inlInInl = trueprop(app(const("ZF_Base.mem"), inlA, inlA))
private func vacuous(_ T: String) -> String { all("x", T, falsum) }

/// A miniature export:
///   T.U  (named)   False ⟹ False           cites IFOL.selfImp, outside the ZF sessions, at no type arguments
///   T.V  (named)   A ↔ A ⟹ A ↔ A           uses ↔ without citing its definition, whose body uses ¬
///   T.W  (named)   split(λx y. x ∈ y, A) ⟹ …  uses split at 'a := o
///   T.O  (named)   False                    an oracle: the reader refuses it
///   T.X  (named)   Inl(a) ∈ Inl(a) ⟹ …     Inl defined applied, as primrec writes it: Inl(a) ≡ a
///   T.Y  (named)   (⋀x::i. False) ⟹ …      cites IFOL.vacuous at i, its class premise discharged by box 70
///   T.Z  (named)   False ⟹ False           IFOL's box 92 at False: a box binding a proposition, a statement of IFOL
///   IFOL.selfImp   False ⟹ False           λH. H
///   IFOL.vacuous   OFCLASS('a, term) ⟹ (⋀x::'a. False) ⟹ (⋀x::'a. False)   λC H. H
///   box 92 (IFOL)  P ⟹ P                   λH. H
private func readUnit() throws -> IR.Unit {
    let theorems: [(String, Int, String)] = [
        ("T.U", 10, proofFile(frees: [], prop: imp(falsum, falsum), proof: pcite(90, "IFOL", "IFOL.selfImp"))),
        ("T.V", 20, proofFile(frees: [("A", o)], prop: imp(aIffA, aIffA), proof: pabsp("H", aIffA, pbound(0)))),
        ("T.W", 30, proofFile(frees: [("A", i)], prop: imp(splitAtO, splitAtO), proof: pabsp("H", splitAtO, pbound(0)))),
        ("T.O", 40, proofFile(frees: [], prop: falsum, proof: poracle("skip_proof"))),
        ("T.X", 50, proofFile(frees: [("a", i)], prop: imp(inlInInl, inlInInl), proof: pabsp("H", inlInInl, pbound(0)))),
        ("T.Y", 60, proofFile(frees: [], prop: imp(vacuous(i), vacuous(i)),
                              proof: pappp(pcite(91, "IFOL", "IFOL.vacuous", i), pcite(70, "ZF.T")))),
        ("T.Z", 80, proofFile(frees: [], prop: imp(falsum, falsum), proof: pappt(pcite(92, "IFOL"), const("IFOL.False")))),
    ]
    var files: [String: String] = [
        "IFOL/theory/axioms": axiomEntity("IFOL.iff_def_raw", prop: iffDef) + axiomEntity("IFOL.not_def_raw", prop: notDef),
        "ZF.ZF_Base/theory/axioms": axiomEntity("ZF_Base.split_def_raw", tfrees: ["'a"], prop: splitDef),
        "ZF.T/theory/axioms": axiomEntity("Sum.Inl_def", frees: [("a", i)], prop: app(const("Pure.eq", i), inlA, free("a")))
            + axiomEntity("T.termI", prop: ofclass(i, "IFOL.term")),
        "IFOL/theory/thms": thmsFile([("IFOL.selfImp", 90), ("IFOL.vacuous", 91)]),
        "IFOL/proofs/90": proofFile(frees: [], prop: imp(falsum, falsum), proof: pabsp("H", falsum, pbound(0))),
        "IFOL/proofs/91": proofFile(tfrees: ["'a"], frees: [],
                                    prop: imp(ofclass(typeA, "IFOL.term"), imp(vacuous(typeA), vacuous(typeA))),
                                    proof: pabsp("C", ofclass(typeA, "IFOL.term"), pabsp("H", vacuous(typeA), pbound(0)))),
        "IFOL/proofs/92": proofFile(frees: [("P", o)], prop: imp(trueprop(free("P")), trueprop(free("P"))),
                                    proof: pabsp("H", trueprop(free("P")), pbound(0))),
        "ZF.T/proofs/70": proofFile(frees: [], prop: ofclass(i, "IFOL.term"), proof: paxiom("T.termI")),
        "ZF.T/theory/thms": thmsFile(theorems.map { ($0.0, $0.1) }),
    ]
    for (_, serial, text) in theorems { files["ZF.T/proofs/\(serial)"] = text }
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    var reader = try Reader(try Export(root: root))
    return try reader.unit()
}

/// Box 92's proof, `⋀P. λH. H`, and the name it is cited by: its theory's and its content's.
private func box92(_ t: inout Table) throws -> (name: String, proof: NodeID) {
    let p = try t.intern(.isaBound(0, .o))
    let proof = try t.intern(.isaAllIntro(.o, body: try t.intern(.folImpliesIntro(p, body: try t.intern(.hyp(0, p))))))
    return ("IFOL.BOX_" + fingerprint(proof, t), proof)
}

@Test func theUnitHoldsEachTheoremItsTheoremsCiteAtNoTypeArguments() throws {
    var unit = try readUnit()
    let box = try box92(&unit.table).name
    #expect(unit.statements.map(\.name) == ["T.U", "T.V", "T.W", "T.X", "T.Y", "T.Z", "IFOL.selfImp", "IFOL.vacuous", box])
    #expect(unit.refused.map(\.name) == ["T.O"])
    #expect(unit.refused.map(\.refusal) == [.unread])
}

/// `IFOL.vacuous`, restricted to `term` and cited at `i`, is a statement of the unit read at `i`: the citation's root.
@Test func theUnitHoldsATheoremRestrictedToTermReadAtI() throws {
    var unit = try readUnit()
    let vacuous = try #require(unit.statements.first { $0.name == "IFOL.vacuous" })
    let user = try #require(unit.statements.first { $0.name == "T.Y" })
    let member = try unit.table.intern(.isaOfClass(.i, "IFOL.term"))
    let bottom = try unit.table.intern(.folBottom)
    let every = try unit.table.intern(.ifolAll(.i, body: bottom))
    #expect(vacuous.root == (try unit.table.intern(.folImplies(member, try unit.table.intern(.folImplies(every, every))))))
    #expect(cited(by: user, in: unit.table) == ["IFOL.vacuous"])
    #expect(reaches(try #require(user.proof), try unit.table.intern(.use(.theorem("IFOL.vacuous"), [], vacuous.root)), unit.table))
}

/// IFOL's box 92 binds a proposition: a statement of IFOL, proved by its own proof, and `T.Z` cites it at `False`.
@Test func theUnitHoldsABoxBindingAPropositionInItsTheory() throws {
    var unit = try readUnit()
    let (name, proof) = try box92(&unit.table)
    let box = try #require(unit.statements.first { $0.name == name })
    let user = try #require(unit.statements.first { $0.name == "T.Z" })
    #expect(box.theory == "IFOL")
    #expect(box.proof == proof)
    #expect(cited(by: user, in: unit.table) == [name])
}

private func reaches(_ root: NodeID, _ target: NodeID, _ t: Table) -> Bool {
    var seen: Set<NodeID> = [], work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if n == target { return true }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return false
}

/// `↔` is reached from `T.V`, `¬` from `↔`'s body, `split` at the type `T.W` uses it at, and `Inl`'s applied
/// definition abstracts its arguments.
@Test func theUnitHoldsTheDefinitionOfEachConstantItsTheoremsReachAtEachType() throws {
    var unit = try readUnit()
    let splitAtOType = IRType.fn(.fn(.i, .fn(.i, .o)), .fn(.i, .o))
    #expect(Set(unit.definitions.map { "\($0.constant.name) \($0.type)" }) == [
        "IFOL.iff \(IRType.fn(.o, .fn(.o, .o)))", "IFOL.Not \(IRType.fn(.o, .o))", "ZF_Base.split \(splitAtOType)",
        "Sum.Inl \(IRType.fn(.i, .i))",
    ])
    let a = try unit.table.intern(.isaBound(0, .i))
    #expect(unit.definitions.first { $0.constant.name == "Sum.Inl" }?.definiens == (try unit.table.intern(.isaAbs(.i, body: a))))
    let p = try unit.table.intern(.isaBound(0, .o))
    let bottom = try unit.table.intern(.folBottom)
    let notDefiniens = try unit.table.intern(.isaAbs(.o, body: try unit.table.intern(.folImplies(p, bottom))))
    #expect(unit.definitions.first { $0.constant.name == "IFOL.Not" }?.definiens == notDefiniens)
    let c = try unit.table.intern(.isaBound(1, .fn(.i, .fn(.i, .o))))
    let q = try unit.table.intern(.isaBound(0, .i))
    let applied = try unit.table.intern(.isaVarApp(head: c, args: [q, q]))
    let splitDefiniens = try unit.table.intern(.isaAbs(.fn(.i, .fn(.i, .o)), body: try unit.table.intern(.isaAbs(.i, body: applied))))
    #expect(unit.definitions.first { $0.constant.name == "ZF_Base.split" }?.definiens == splitDefiniens)
}

/// `IFOL.Not ≡ λP. P ⟶ ⊥` names no argument; `Inl(a) ≡ a` names one; `split`'s definition is cited at `'a := o`.
@Test func aDefinitionCarriesItsAxiomsTypeArgumentsAndItsParameters() throws {
    let unit = try readUnit()
    let definition = { (name: String) in try #require(unit.definitions.first { $0.constant.name == name }) }
    let not = try definition("IFOL.Not"), inl = try definition("Sum.Inl"), split = try definition("ZF_Base.split")
    #expect([not.axiomTypes, inl.axiomTypes, split.axiomTypes] == [[], [], [IRType.o]])
    #expect([not.parameters, inl.parameters, split.parameters] == [0, 1, 0] as [Int])
}
