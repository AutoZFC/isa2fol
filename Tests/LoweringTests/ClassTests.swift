import IR
import Testing
@testable import Lowering

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private func classOf(_ c: Constant, _ T: IRType, in t: inout Table) throws -> [(Lemma, NodeID)] {
    let f = ConstantFact(constant: c, type: T, fact: .classExists)
    return [(Lemma(f), try statement(f, in: &t))]
}

private func classOf(lambda: NodeID, in t: inout Table) throws -> [(Lemma, NodeID)] {
    let (f, _) = try lambdaFact(lambda, .classExists, in: &t)
    return [(Lemma(f), try statement(f, base: try base(in: &t), in: &t))]
}

/// ⚠ A λ'S CLASS DEFINITION IS ITS BODY AS LOGIC'S WALK REWRITES IT: `λx. ⋀P. P ⟶ x ∈ y`, built from the λ as stated,
/// reads `⋀P` a truth set, as the walked λ does. A second rewrite of the body diverged from the walk silently.
@Test
func aLambdasClassDefinitionIsItsBodyAsTheWalkRewritesIt() throws {
    var r = Terms()
    let mem = try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(1), try r.x(3)]))
    let lambda = try r.lam(i, try r.n(.isaPropAll(body: try r.n(.folImplies(try r.n(.isaPropBound(0)), mem)))))
    let K = try r.n(.folBound(0))
    let stated = try classDefinition(lambda, K: K, in: &r.t)
    let walkedLambda = try walked(lambda, base: try base(in: &r.t), in: &r.t)
    let fromWalked = try classDefinition(walkedLambda, K: K, in: &r.t)
    #expect(stated == fromWalked)
    #expect(!patterns(under: [stated], in: r.t).contains(.isaPropAll))
}

/// ⚠ THE FORMULA WALK REFUSES EVERY STEP, WHATEVER ITS PIECE: a hypothesis, an instance at `i`, a definition — no piece
/// of Logic's — passed through it unconverted, and failed in Fol at a compound term, or not at all.
@Test
func theFormulaWalkRefusesAStepWhateverItsPiece() throws {
    var r = Terms()
    let mem = try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.x(1)]))
    let h = try r.n(.hyp(0, mem))
    #expect(throws: LogicError.notAFormula(h)) { _ = try walked(formula: h, in: &r.t) }
}

/// `CLASS ⟨λx. x ∈ y⟩`: `∃` by `row_ex`, the tuple's atoms read through `cls_zero`'s and `cls_snoc4`'s classes, `x ∈ y`
/// through `B1`'s, and the class named by `member_class` at the record `⟨y⟩`.
@Test
func aLambdasClassIsItsRecordsSectionAtItsFreeVariables() throws {
    var r = Terms()
    let mem = try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.x(1)]))
    let (proved, unbuilt) = try proveAll(try classOf(lambda: try r.lam(i, mem), in: &r.t), [], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(proved.count == 1)
    try kernelChecks(proved, in: &r.t)
}

/// `CLASS ⟨λx. f(x)⟩`, `f` a function variable: `apply(τ, r, f)` read through `cls_apply`'s class, the graph named by
/// `graph_class` at the empty record.
@Test
func aFunctionVariablesApplicationIsReadThroughItsApplicationClass() throws {
    var r = Terms()
    let applied = try r.n(.isaVarApp(head: try r.n(.isaBound(1, fn(i, i))), args: [try r.x(0)]))
    let (proved, unbuilt) = try proveAll(try classOf(lambda: try r.lam(i, applied), in: &r.t), [], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(proved.count == 1)
    try kernelChecks(proved, in: &r.t)
}

/// `ZF_Base.Pow_CLASS` and `ZF_Base.Union_CLASS`, from base's definitions: `Pow(A, r)` and `Union(A, r)` read through
/// `Pow_def` and `Union_def`, a `∀` as `¬∃¬`, `↔` by `B_iff`, `→` as `¬(A ∧ ¬B)`.
@Test
func thePrimitivesClassesAreBuiltFromBasesDefinitions() throws {
    var t = Table()
    let requests = try classOf(.primitive(.zf(.pow)), fn(i, i), in: &t) + classOf(
        .primitive(.zf(.union)),
        fn(i, i),
        in: &t,
    )
    let (proved, unbuilt) = try proveAll(requests, [], in: &t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)) == ["ZF_Base.Pow_CLASS", "ZF_Base.Union_CLASS"])
    try kernelChecks(proved, in: &t)
}

/// `T.s ≡ λx. Pow(x)`: `T.s_CLASS` opens `Pow`'s class and reads `pmem(τ, r, C)` at it, joined by `ZF_Base.Pow_AGREE`.
@Test
func aConstantsClassOpensTheClassesItsBodyNames() throws {
    var r = Terms()
    let s = Defined(.zf, "T.s", .object)
    let d = Definition(
        defines: .constant(s),
        type: fn(i, i),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.pow(try r.x(0))),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(s), fn(i, i), in: &r.t), [d], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)) == ["T.s_CLASS", "ZF_Base.Pow_CLASS", "ZF_Base.Pow_AGREE"])
    try kernelChecks(proved, definitions: [(s, try atDefinition(s, [d], in: &r.t))], in: &r.t)
}

/// `T.e ≡ Pow(0)`, a set constant: its class is the singleton of its value, by `upair_ex` from `T.e_EX`, read back by
/// `T.e_UNIQ` and, the other way, `T.e`'s `@def` carried along the equation.
@Test
func aSetConstantsClassIsTheSingletonOfItsValue() throws {
    var r = Terms()
    let e = Defined(.zf, "T.e", .object)
    let d = Definition(
        defines: .constant(e),
        type: i,
        axiomTypes: [],
        parameters: 0,
        definiens: try r.pow(try r.zero()),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(e), i, in: &r.t), [d], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["T.e_CLASS", "T.e_EX", "T.e_UNIQ"]))
    try kernelChecks(proved, definitions: [(e, try atDefinition(e, [d], in: &r.t))], in: &r.t)
}

private func ball(_ r: inout Terms) throws -> Definition {
    let P = fn(i, o)
    let member = try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.x(2)]))
    let holds = try r.n(.isaVarApp(head: try r.n(.isaBound(1, P)), args: [try r.x(0)]))
    let body = try r.n(.ifolAll(i, body: try r.n(.folImplies(member, holds))))
    return Definition(
        defines: .constant(Defined(.zf, "T.ball", .object)),
        type: fn(i, fn(P, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(P, body)),
    )
}

/// `sub ≡ λA B. ball(A, λx. x ∈ B)`: the λ mentions `B`, an entry, so `ball`'s class at it is lifted — `ball_LIFT` at
/// the
/// site's record, the λ's bundle its argument — and `ball_LIFT` is proved once, uniform in the record's length,
/// re-keyed
/// by `REKEY_1`.
@Test
func aClassTakingConstantAtALambdaOfTheRecordIsLifted() throws {
    var r = Terms()
    let b = try ball(&r)
    let sub = Defined(.zf, "T.sub", .object)
    let lambda = try r.lam(
        i,
        try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.x(1)])),
    )
    let applied = try r.n(.isaConst(.defined(b.constant), b.type, args: [try r.x(1), lambda]))
    let d = Definition(
        defines: .constant(sub),
        type: fn(i, fn(i, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(i, applied)),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(sub), d.type, in: &r.t), [b, d], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["T.sub_CLASS", "T.ball_LIFT", "T.ball_CLASS", "REKEY_1"]))
    try kernelChecks(proved, definitions: [
        (b.constant, try atDefinition(b.constant, [b, d], in: &r.t)),
        (sub, try atDefinition(sub, [b, d], in: &r.t)),
    ], in: &r.t)
}

/// `T.two ≡ λA B. ball(A, λx. x ∈ B) ∧ ball(B, λx. x ∈ A)`: two λs at different arguments, each site its own class from
/// ONE
/// `ball_LIFT` — no bundle widened.
@Test
func twoLambdasAtDifferentArgumentsShareOneLift() throws {
    var r = Terms()
    let b = try ball(&r)
    let two = Defined(.zf, "T.two", .object)
    let site = { (set: Int, other: Int, r: inout Terms) throws -> NodeID in
        let lambda = try r.lam(
            i,
            try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.x(other + 1)])),
        )
        return try r.n(.isaConst(.defined(b.constant), b.type, args: [try r.x(set), lambda]))
    }
    let body = try r.n(.folAnd(try site(1, 0, &r), try site(0, 1, &r)))
    let d = Definition(
        defines: .constant(two),
        type: fn(i, fn(i, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(i, body)),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(two), d.type, in: &r.t), [b, d], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(proved.filter { $0.name.hasSuffix("_LIFT") }.map(\.name) == ["T.ball_LIFT"])
    try kernelChecks(proved, definitions: [
        (b.constant, try atDefinition(b.constant, [b, d], in: &r.t)),
        (two, try atDefinition(two, [b, d], in: &r.t)),
    ], in: &r.t)
}

/// `T.rep ≡ λA P. PrimReplace(A, λx y. P(x, y))` used at `λx y. x ∈ B`: `T.rep_LIFT` reads `P` through its section, and
/// the λ there mentions it, so `PrimReplace`'s class at it is lifted in turn — `PrimReplace_LIFT`, from base's
/// definition,
/// both function constants, re-keyed by `REKEY_2`.
@Test
func aLiftInsideALiftsBodyIsCited() throws {
    var r = Terms()
    let P = fn(i, fn(i, o))
    let replaceT = fn(i, fn(P, i))
    let rep = Defined(.zf, "T.rep", .object)
    let use = Defined(.zf, "T.uses", .object)
    let held = try r.n(.isaVarApp(head: try r.n(.isaBound(2, P)), args: [try r.x(1), try r.x(0)]))
    let inner = try r.n(.isaConst(
        .primitive(.zf(.primReplace)),
        replaceT,
        args: [try r.x(1), try r.lam(i, try r.lam(i, held))],
    ))
    let repD = Definition(
        defines: .constant(rep),
        type: replaceT,
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(P, inner)),
    )
    let mem = try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(1), try r.x(2)]))
    let atB = try r.n(.isaConst(.defined(rep), replaceT, args: [try r.x(1), try r.lam(i, try r.lam(i, mem))]))
    let equal = try r.n(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [try r.x(0), atB]))
    let useD = Definition(
        defines: .constant(use),
        type: fn(i, fn(i, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(i, try r.n(.ifolEx(i, body: equal)))),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(use), useD.type, in: &r.t), [repD, useD], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: [
        "T.uses_CLASS",
        "T.rep_LIFT",
        "ZF_Base.PrimReplace_LIFT",
        "REKEY_2",
    ]))
    try kernelChecks(proved, definitions: [
        (rep, try atDefinition(rep, [repD, useD], in: &r.t)),
        (use, try atDefinition(use, [repD, useD], in: &r.t)),
    ], in: &r.t)
}

/// `T.ap ≡ λF x. F(x)` at `λy. Pow(B)`, a function λ mentioning `B`: its bundle a class of records `a ++ [t, r]`, its
/// section by `lam_class`; in `T.ap_LIFT` the function parameter's `apply` is read through `apply_def` and its section.
@Test
func aFunctionLambdaInAClassSlotIsLifted() throws {
    var r = Terms()
    let F = fn(i, i)
    let apT = fn(F, fn(i, i))
    let ap = Defined(.zf, "T.ap", .object)
    let use = Defined(.zf, "T.useAp", .object)
    let applied = try r.n(.isaVarApp(head: try r.n(.isaBound(1, F)), args: [try r.x(0)]))
    let apD = Definition(
        defines: .constant(ap),
        type: apT,
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(F, try r.lam(i, applied)),
    )
    let site = try r.n(.isaConst(.defined(ap), apT, args: [try r.lam(i, try r.pow(try r.x(1))), try r.x(1)]))
    let equal = try r.n(.isaConst(.primitive(.ifol(.eq)), fn(i, fn(i, o)), args: [try r.x(0), site]))
    let useD = Definition(
        defines: .constant(use),
        type: fn(i, fn(i, o)),
        axiomTypes: [],
        parameters: 0,
        definiens: try r.lam(i, try r.lam(i, equal)),
    )
    let (proved, unbuilt) = try proveAll(try classOf(.defined(use), useD.type, in: &r.t), [apD, useD], in: &r.t)
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["T.useAp_CLASS", "T.ap_LIFT", "REKEY_2"]))
    try kernelChecks(proved, definitions: [
        (ap, try atDefinition(ap, [apD, useD], in: &r.t)),
        (use, try atDefinition(use, [apD, useD], in: &r.t)),
    ], in: &r.t)
}

/// `λx. x ∈ 0` and `λx. x ∈ Inf`: a primitive set constant's class is the singleton of its value from base's EX and
/// UNIQ,
/// read back along `ZF_Base`'s definitions and base's own (`zero_def`, `Inf_def`, `ind_def`) down to membership.
@Test
func aPrimitiveSetConstantsClassIsTheSingletonOfItsValue() throws {
    var r = Terms()
    let inf = try r.n(.isaConst(.primitive(.zf(.inf)), i, args: []))
    let atZero = try r.lam(
        i,
        try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), try r.zero()])),
    )
    let atInf = try r.lam(i, try r.n(.isaConst(.primitive(.zf(.mem)), fn(i, fn(i, o)), args: [try r.x(0), inf])))
    let (proved, unbuilt) = try proveAll(
        try classOf(lambda: atZero, in: &r.t) + classOf(lambda: atInf, in: &r.t),
        [],
        in: &r.t,
    )
    #expect(unbuilt.isEmpty)
    #expect(Set(proved.map(\.name)).isSuperset(of: ["ZF_Base.zero_CLASS", "ZF_Base.Inf_CLASS"]))
    try kernelChecks(proved, in: &r.t)
}
