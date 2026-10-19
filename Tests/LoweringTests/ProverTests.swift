import IR
import Testing
@testable import Lowering

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

/// `0`: EX and UNIQ from base's, and the real checker proves both.
@Test
func exAndUniqOfASetPrimitiveAreBases() throws {
    var r = Terms()
    let (proved, unbuilt) = try proveAll(try r.requests(try r.zero()), [], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).count == 2)
    try kernelChecks(proved, in: &r.t)
}

/// `f(0)`, `f` a function variable: EX by `apply_EX` with the tuple's EX, UNIQ by `apply_at` under `f`'s guard with the
/// tuple's UNIQ, all kernel-checked.
@Test
func exAndUniqOfAnAppliedFunctionVariable() throws {
    var r = Terms()
    let applied = try r.n(.isaVarApp(head: try r.n(.isaBound(0, fn(i, i))), args: [try r.zero()]))
    let (proved, unbuilt) = try proveAll(try r.requests(applied), [], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["TUPLE_EX_1", "TUPLE_UNIQ_1"]))
    try kernelChecks(proved, in: &r.t)
}

/// `T.s ≡ λx. Pow(x)` at `a`: UNIQ by `T.s_AGREE`, `T.s_FUNC` and, under them, `Pow`'s from base; EX by `T.s_CLASS`,
/// which
/// opens `Pow`'s — proved to the end, nothing unbuilt.
@Test
func exAndUniqOfAConstantAtAVariableAreProvedToTheEnd() throws {
    var r = Terms()
    let s = Defined(.zf, "T.s", .object)
    let d = Definition(
        defines: .constant(s),
        type: fn(i, i),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.pow(try r.x(0))),
    )
    let term = try r.n(.isaConst(.defined(s), fn(i, i), args: [try r.x(0)]))
    let (proved, unbuilt) = try proveAll(try r.requests(term), [d], in: &r.t)
    let names = Set(proved.map(\.name))
    #expect(names.isSuperset(of: [
        "T.s_AGREE",
        "T.s_FUNC",
        "ZF_Base.Pow_AGREE",
        "ZF_Base.Pow_FUNC",
        "TUPLE_INJ_1",
        "TUPLE_UNIQ_1",
        "T.s_CLASS",
        "ZF_Base.Pow_CLASS",
    ]))
    #expect(unbuilt.isEmpty)
    #expect(names.contains { $0.hasPrefix("UNIQ_") } && names.contains { $0.hasPrefix("EX_") })
    try kernelChecks(proved, definitions: [(s, try atDefinition(s, [d], in: &r.t))], in: &r.t)
}

/// `T.s ≡ λx. Pow(x)`: its unfolding, `∀x. T.s(x) = Pow(x)` named universally, from its `@def` at the naming's pieces,
/// fixed, and the tuple's injectivity — no existence cited — proved to the end and kernel-checked.
@Test
func aFunctionsUnfoldingIsProvedFromItsDef() throws {
    var r = Terms()
    let s = Defined(.zf, "T.s", .object)
    let d = Definition(
        defines: .constant(s),
        type: fn(i, i),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.pow(try r.x(0))),
    )
    let eta = try r.lam(i, try r.n(.isaConst(.defined(s), fn(i, i), args: [try r.x(0)])))
    let base = try LoweringTests.base(in: &r.t)
    let stated = try formula(try r.t.equation(fn(i, i), eta, d.definiens), .statement, in: &r.t)
    let request = Unfolding(constant: s, statement: stated)
    let (proved, unbuilt) = try proveAll([(Lemma(request), stated)], [d], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)) == ["T.s_UNFOLD", "TUPLE_INJ_1"])
    try kernelChecks(proved, definitions: [(s, try atDefinition(s, [d], in: &r.t))], in: &r.t)
}

/// `T.e ≡ Pow(0)`, a set constant: its UNIQ by UNIQ of its body, its EX by EX of its body.
@Test
func aDefinedSetConstantsFactsComeFromItsBody() throws {
    var r = Terms()
    let e = Defined(.zf, "T.e", .object)
    let d = Definition(
        defines: .constant(e),
        type: i,
        axiomTypes: [],
        parameters: 0,
        definiens: try r.pow(try r.zero()),
    )
    let term = try r.n(.isaConst(.defined(e), i, args: []))
    let (proved, unbuilt) = try proveAll(try r.requests(term), [d], in: &r.t)
    #expect(Set(proved.map(\.name)).isSuperset(of: [
        "T.e_UNIQ",
        "T.e_EX",
        "ZF_Base.Pow_FUNC",
        "ZF_Base.Pow_AGREE",
        "ZF_Base.Pow_CLASS",
    ]))
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, definitions: [(e, try atDefinition(e, [d], in: &r.t))], in: &r.t)
}

/// `T.ap ≡ λF x. F(x)` at `λy. Pow(y)` and `a`: a function class parameter. UNIQ needs the λ's guard, `FUNC ⟨λ⟩`, and
/// `T.ap`'s facts carry `F`'s: its `_AGREE` walks `apply` atoms by `apply_class_cong`, its `_FUNC` assumes
/// `function(F)`.
@Test
func uniqAtAFunctionClassParameterCitesTheLambdasGuard() throws {
    var r = Terms()
    let ap = Defined(.zf, "T.ap", .object)
    let F = fn(i, i)
    let body = try r.n(.isaVarApp(head: try r.n(.isaBound(1, F)), args: [try r.x(0)]))
    let d = Definition(
        defines: .constant(ap),
        type: fn(F, fn(i, i)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(F, try r.lam(i, body)),
    )
    let lambda = try r.lam(i, try r.pow(try r.x(0)))
    let term = try r.n(.isaConst(.defined(ap), fn(F, fn(i, i)), args: [lambda, try r.x(0)]))
    let (proved, unbuilt) = try proveAll(try r.requests(term), [d], in: &r.t)
    let names = Set(proved.map(\.name))
    #expect(names.isSuperset(of: ["T.ap_AGREE", "T.ap_FUNC", "T.ap_CLASS"]))
    #expect(names.contains { $0.hasPrefix("FUNC_") } && names.contains { $0.hasPrefix("CLASS_") })
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, definitions: [(ap, try atDefinition(ap, [d], in: &r.t))], in: &r.t)
}

/// `PrimReplace(a, λx y. x = y)`: UNIQ by `PrimReplace`'s two branches — extensionality where `P` is functional,
/// `zero_UNIQ`
/// where not — and its `_AGREE` at the class argument; EX by its class, the λ's, and its `_TOTAL` from base's value.
@Test
func exAndUniqOfPrimReplaceAreProvedToTheEnd() throws {
    var r = Terms()
    let P = fn(i, fn(i, o))
    let eq = try r.n(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [try r.x(1), try r.x(0)]))
    let lambda = try r.lam(i, try r.lam(i, eq))
    let term = try r.n(.isaConst(.primitive(.zf(.primReplace)), fn(i, fn(P, i)), args: [try r.x(0), lambda]))
    let (proved, unbuilt) = try proveAll(try r.requests(term), [], in: &r.t)
    let names = Set(proved.map(\.name))
    #expect(names.isSuperset(of: [
        "ZF_Base.PrimReplace_AGREE",
        "ZF_Base.PrimReplace_FUNC",
        "ZF_Base.PrimReplace_CLASS",
        "ZF_Base.PrimReplace_TOTAL",
        "TUPLE_INJ_1",
    ]))
    #expect(names.contains { $0.hasPrefix("CLASS_") })
    #expect(unbuilt.isEmpty)
    try kernelChecks(proved, in: &r.t)
}

/// A base schema's letter with arguments is cited at a λ and the real checker proves the instance through Fol:
/// `forall_as_nexists` at `\z. elem(z, A)`.
@Test
func aSchemaLetterWithArgumentsIsCitedAndProved() throws {
    var t = Table()
    let base = try LoweringTests.base(in: &t)
    let n = { (node: Node, t: inout Table) throws -> NodeID in try t.intern(node) }
    let atom = try n(.folPred(.base("elem"), args: [try n(.isaBound(0, i), &t), try n(.folBound(1), &t)]), &t)
    let some = try n(.ifolEx(i, body: try n(.folNot(atom), &t)), &t)
    let root = try n(
        .folForall(body: try n(.folIff(try n(.folNot(some), &t), try n(.ifolAll(i, body: atom), &t)), &t)),
        &t,
    )
    let instance = try n(
        .folSchemaInst(try base.cite(.forallAsNexists, in: &t), try n(.folLetterAbs(body: atom), &t)),
        &t,
    )
    let proof = try n(.folForallIntro(body: instance), &t)
    #expect(t.conclusion(of: proof) == root)
    try kernelChecks([(name: "T.letter", root: root, proof: proof)], in: &t)
}
