import FolDialect
import Foundation
import IR
import Testing
@testable import Lowering

/// `∀y y′. eq(y, y′) → (φₙ(y) ↔ φₙ(y′))`, `φₙ(z) = ∃x₁ … ∃xₙ. elem(xₙ, z)`, by the replacement walk, its hole at the
/// atom `cong_elem_r`.
private func congruence(depth n: Int, in t: inout Table) throws -> (root: NodeID, proof: NodeID) {
    let base = try LoweringTests.base(in: &t)
    var top = Frame()
    let y = top.fix(.i)
    let y2 = top.fix(.i)
    let eq = top.assume(try t.intern(.folPred(
        .base("eq"),
        args: [try top.variable(y, in: &t), try top.variable(y2, in: &t)],
    )))
    let phi = { (z: Int, t: inout Table) throws -> NodeID in
        var body = try t.intern(.folPred(.base("elem"), args: [
            try t.intern(.isaBound(0, .i)),
            try shift(try top.variable(z, in: &t), by: n, in: &t),
        ]))
        for _ in 0..<n { body = try t.intern(.ifolEx(.i, body: body)) }
        return body
    }
    let l = try phi(y, &t)
    let r = try phi(y2, &t)
    let walk = try Replacement(base: base) { _, l, r, s, t in
        guard case .folPred(_, let ls) = t[l], case .folPred(_, let rs) = t[r], l != r else { return nil }
        return try base.claimed(.congElemR, [ls[0], ls[1], rs[1]], [try s.hypothesis(eq, in: &t)], in: &t)
    }.proof(l, l, r, in: top.scope, &t)
    let proof = try top.close(walk, in: &t)
    return (t.conclusion(of: proof)!, proof)
}

/// ⚠ A WALK IS LINEAR IN ITS BINDERS: each binder's equivalence is proved once and carried by its schema. Proved in
/// both directions under each direction's witness, the checker derived it twice per binder (`_FUNC`, `_AGREE`: 10¹²).
@Test
func aQuantifierCongruenceIsLinearInItsBinders() throws {
    let base = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
        .deletingLastPathComponent().appendingPathComponent("base")
    let letters = schemaLetters(from: try baseTexts(base))
    var written = [Int]()
    for n in 1...6 {
        var t = Table()
        let (root, proof) = try congruence(depth: n, in: &t)
        let fol = Fol(base: try LoweringTests.base(in: &t))
        let lowered = try run(fol, [root, proof], in: &t)
        let text = try render(
            proof: lowered[1],
            of: Declaration(kind: .claim, name: "walk", root: lowered[0]),
            in: t,
            letters: letters,
        )
        written.append(text.split(separator: "\n").count(where: { $0.hasPrefix("    _") }))
    }
    let growth = zip(written.dropFirst(), written).map { $0 - $1 }
    #expect(Set(growth).count == 1, "steps by depth: \(written)")
    var t = Table()
    let (root, proof) = try congruence(depth: 3, in: &t)
    try kernelChecks([("walk", root, proof)], in: &t)
}
