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

/// A miniature export:
///   T.U  (named)   False ⟹ False           cites IFOL.selfImp, outside the ZF sessions, at no type arguments
///   T.V  (named)   A ↔ A ⟹ A ↔ A           uses ↔ without citing its definition, whose body uses ¬
///   T.W  (named)   split(λx y. x ∈ y, A) ⟹ …  uses split at 'a := o
///   T.O  (named)   False                    an oracle: the reader refuses it
///   T.X  (named)   Inl(a) ∈ Inl(a) ⟹ …     Inl defined applied, as primrec writes it: Inl(a) ≡ a
///   IFOL.selfImp   False ⟹ False           λH. H
private func readUnit() throws -> IR.Unit {
    let theorems: [(String, Int, String)] = [
        ("T.U", 10, proofFile(frees: [], prop: imp(falsum, falsum), proof: pcite(90, "IFOL", "IFOL.selfImp"))),
        ("T.V", 20, proofFile(frees: [("A", o)], prop: imp(aIffA, aIffA), proof: pabsp("H", aIffA, pbound(0)))),
        ("T.W", 30, proofFile(frees: [("A", i)], prop: imp(splitAtO, splitAtO), proof: pabsp("H", splitAtO, pbound(0)))),
        ("T.O", 40, proofFile(frees: [], prop: falsum, proof: poracle("skip_proof"))),
        ("T.X", 50, proofFile(frees: [("a", i)], prop: imp(inlInInl, inlInInl), proof: pabsp("H", inlInInl, pbound(0)))),
    ]
    var files: [String: String] = [
        "IFOL/theory/axioms": axiomEntity("IFOL.iff_def_raw", prop: iffDef) + axiomEntity("IFOL.not_def_raw", prop: notDef),
        "ZF.ZF_Base/theory/axioms": axiomEntity("ZF_Base.split_def_raw", tfrees: ["'a"], prop: splitDef),
        "ZF.T/theory/axioms": axiomEntity("Sum.Inl_def", frees: [("a", i)], prop: app(const("Pure.eq", i), inlA, free("a"))),
        "IFOL/theory/thms": thmsFile([("IFOL.selfImp", 90)]),
        "IFOL/proofs/90": proofFile(frees: [], prop: imp(falsum, falsum), proof: pabsp("H", falsum, pbound(0))),
        "ZF.T/theory/thms": thmsFile(theorems.map { ($0.0, $0.1) }),
    ]
    for (_, serial, text) in theorems { files["ZF.T/proofs/\(serial)"] = text }
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    var reader = try Reader(try Export(root: root))
    return try reader.unit()
}

@Test func theUnitHoldsEachTheoremItsTheoremsCiteAtNoTypeArguments() throws {
    let unit = try readUnit()
    #expect(unit.statements.map(\.name) == ["T.U", "T.V", "T.W", "T.X", "IFOL.selfImp"])
    #expect(unit.refused.map(\.name) == ["T.O"])
    #expect(unit.refused.map(\.refusal) == [.unread])
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
