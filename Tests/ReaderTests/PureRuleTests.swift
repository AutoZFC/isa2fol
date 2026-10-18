import Foundation
import IR
import Testing
import YXML
@testable import Reader

private let typeB = tfree("'b")
private func eq(_ T: String, _ a: String, _ b: String) -> String {
    app(const("Pure.eq", T), a, b)
}

private func imp(_ a: String, _ b: String) -> String {
    app(const("Pure.imp"), a, b)
}

private func all(_ x: String, _ T: String, _ body: String) -> String {
    app(const("Pure.all", T), lam(x, T, body))
}

private let A = free("A")
private let B = free("B")
private let C = free("C")
private let TA = trueprop(A)
private let TB = trueprop(B)
private let TC = trueprop(C)
private let trueprop = const("IFOL.Trueprop")

/// Pure's equality rules, as `Pure.thy` states them.
private let pureAxioms = [
    axiomEntity("Pure.reflexive", tfrees: ["'a"], frees: [("x", typeA)], prop: eq(typeA, free("x"), free("x"))),
    axiomEntity(
        "Pure.symmetric",
        tfrees: ["'a"],
        frees: [("x", typeA), ("y", typeA)],
        prop: imp(eq(typeA, free("x"), free("y")), eq(typeA, free("y"), free("x"))),
    ),
    axiomEntity(
        "Pure.transitive",
        tfrees: ["'a"],
        frees: [("x", typeA), ("y", typeA), ("z", typeA)],
        prop: imp(
            eq(typeA, free("x"), free("y")),
            imp(eq(typeA, free("y"), free("z")), eq(typeA, free("x"), free("z"))),
        ),
    ),
    axiomEntity(
        "Pure.combination",
        tfrees: ["'a", "'b"],
        frees: [("f", fn(typeA, typeB)), ("g", fn(typeA, typeB)), ("x", typeA), ("y", typeA)],
        prop: imp(
            eq(fn(typeA, typeB), free("f"), free("g")),
            imp(
                eq(typeA, free("x"), free("y")),
                eq(typeB, app(free("f"), free("x")), app(free("g"), free("y"))),
            ),
        ),
    ),
    axiomEntity(
        "Pure.abstract_rule",
        tfrees: ["'a", "'b"],
        frees: [("f", fn(typeA, typeB)), ("g", fn(typeA, typeB))],
        prop: imp(
            all("x", typeA, eq(typeB, app(free("f"), bound(0)), app(free("g"), bound(0)))),
            eq(
                fn(typeA, typeB),
                lam("x", typeA, app(free("f"), bound(0))),
                lam("x", typeA, app(free("g"), bound(0))),
            ),
        ),
    ),
    axiomEntity(
        "Pure.equal_intr",
        frees: [("A", prop), ("B", prop)],
        prop: imp(imp(free("A"), free("B")), imp(imp(free("B"), free("A")), eq(prop, free("A"), free("B")))),
    ),
    axiomEntity(
        "Pure.equal_elim",
        frees: [("A", prop), ("B", prop)],
        prop: imp(eq(prop, free("A"), free("B")), imp(free("A"), free("B"))),
    ),
].joined()

private func ax(_ name: String, _ types: String...) -> String {
    tagged(7, [name], types.map { node($0) })
}

private func at(_ p: String, _ terms: String...) -> String {
    terms.reduce(p, pappt)
}

private let ballType = fn(i, fn(fn(i, o), o))
private let ball = const("ZF_Base.Ball")
private let defines = eq(ballType, free("Balla"), ball)
private let balla = trueprop(app(free("Balla"), free("A"), free("P")))
private let atBall = trueprop(app(ball, free("a"), free("B")))

/// The definition command's box at a constant taking a class, `⋀Balla A P. Balla ≡ Ball ⟹ Balla(A, P) ⟹ Balla(A, P)`.
private let definitionBox = proofFile(
    frees: [("Balla", ballType), ("A", i), ("P", fn(i, o))],
    prop: imp(defines, imp(balla, balla)),
    proof: pabsp("h", defines, pabsp("H", balla, pbound(0))),
)

/// One theorem per rule:
///   T.refl        P ≡ P                            reflexive % P
///   T.symI        a ≡ b ⟹ b ≡ a  at i              λH. symmetric % a % b %% H
///   T.trans       A ≡ B ⟹ B ≡ C ⟹ A ≡ C            λH K. transitive % A % B % C %% H %% K
///   T.rewrite     A ≡ B ⟹ B ⟹ A                    the simplifier's: equal_elim (symmetric (combination (reflexive
/// Trueprop) q)) fact
///   T.intr        (A ⟹ B) ⟹ (B ⟹ A) ⟹ A ≡ B        λh k. equal_intr %% h %% k
///   T.elimPartial A ≡ B ⟹ (A ⟹ B)                  λh. equal_elim %% h, its last premise missing
///   T.abs         (⋀x. P x ≡ Q x) ⟹ (λx. P x) ≡ (λx. Q x)   λH. abstract_rule % P % Q %% H
///   T.elimImp     (A ≡ (B ⟹ C)) ⟹ A ⟹ B ⟹ C       λh a b. equal_elim % A % (B ⟹ C) %% h %% a %% b: its `B` an
/// implication
///   box 400       ⋀Balla A P. Balla ≡ Ball ⟹ Balla(A, P) ⟹ Balla(A, P)   λh H. H, `Balla :: i ⇒ (i ⇒ o) ⇒ o`
///   T.atBall      Ball(a, B) ⟹ Ball(a, B)          box400 % Ball % a % B %% (reflexive % Ball)
private func pureReader() throws -> Reader {
    let rewrite = pabsp("q", eq(o, A, B), pabsp(
        "fact",
        TB,
        pappp(
            at(ax("Pure.equal_elim"), TB, TA),
            pappp(
                at(ax("Pure.symmetric", prop), TA, TB),
                pappp(
                    at(
                        ax("Pure.combination", o, prop),
                        trueprop,
                        trueprop,
                        A,
                        B,
                    ),
                    at(ax("Pure.reflexive", fn(o, prop)), trueprop),
                    pbound(1),
                ),
            ),
            pbound(0),
        ),
    ))
    let theorems: [(String, Int, String)] = [
        (
            "T.refl",
            10,
            proofFile(
                frees: [("P", o)],
                prop: eq(o, free("P"), free("P")),
                proof: at(ax("Pure.reflexive", o), free("P")),
            ),
        ),
        (
            "T.symI",
            20,
            proofFile(
                frees: [("a", i), ("b", i)],
                prop: imp(eq(i, free("a"), free("b")), eq(i, free("b"), free("a"))),
                proof: pabsp(
                    "H",
                    eq(i, free("a"), free("b")),
                    pappp(at(ax("Pure.symmetric", i), free("a"), free("b")), pbound(0)),
                ),
            ),
        ),
        (
            "T.trans",
            30,
            proofFile(
                frees: [("A", o), ("B", o), ("C", o)],
                prop: imp(eq(o, A, B), imp(eq(o, B, C), eq(o, A, C))),
                proof: pabsp("H", eq(o, A, B), pabsp(
                    "K",
                    eq(o, B, C),
                    pappp(
                        at(ax("Pure.transitive", o), A, B, C),
                        pbound(1),
                        pbound(0),
                    ),
                )),
            ),
        ),
        ("T.rewrite", 40, proofFile(frees: [("A", o), ("B", o)], prop: imp(eq(o, A, B), imp(TB, TA)), proof: rewrite)),
        (
            "T.intr",
            50,
            proofFile(
                frees: [("A", o), ("B", o)],
                prop: imp(imp(TA, TB), imp(imp(TB, TA), eq(prop, TA, TB))),
                proof: pabsp("h", imp(TA, TB), pabsp(
                    "k",
                    imp(TB, TA),
                    pappp(
                        at(ax("Pure.equal_intr"), TA, TB),
                        pbound(1),
                        pbound(0),
                    ),
                )),
            ),
        ),
        ("T.elimPartial", 60, proofFile(
            frees: [("A", o), ("B", o)],
            prop: imp(eq(prop, TA, TB), imp(TA, TB)),
            proof: pabsp(
                "h",
                eq(prop, TA, TB),
                pappp(at(ax("Pure.equal_elim"), TA, TB), pbound(0)),
            ),
        )),
        ("T.abs", 70, proofFile(
            frees: [("P", fn(i, o)), ("Q", fn(i, o))],
            prop: imp(
                all("x", i, eq(o, app(free("P"), bound(0)), app(free("Q"), bound(0)))),
                eq(
                    fn(i, o),
                    lam("x", i, app(free("P"), bound(0))),
                    lam("x", i, app(free("Q"), bound(0))),
                ),
            ),
            proof: pabsp(
                "H",
                all("x", i, eq(o, app(free("P"), bound(0)), app(free("Q"), bound(0)))),
                pappp(at(ax("Pure.abstract_rule", i, o), free("P"), free("Q")), pbound(0)),
            ),
        )),
        (
            "T.elimImp",
            80,
            proofFile(
                frees: [("A", o), ("B", o), ("C", o)],
                prop: imp(eq(prop, TA, imp(TB, TC)), imp(TA, imp(TB, TC))),
                proof: pabsp("h", eq(prop, TA, imp(TB, TC)), pabsp("a", TA, pabsp(
                    "b",
                    TB,
                    pappp(
                        at(
                            ax("Pure.equal_elim"),
                            TA,
                            imp(
                                TB,
                                TC,
                            ),
                        ),
                        pbound(2),
                        pbound(1),
                        pbound(0),
                    ),
                ))),
            ),
        ),
    ]
    let citing: [(String, Int, String)] = [("T.atBall", 410, proofFile(
        frees: [("a", i), ("B", fn(i, o))],
        prop: imp(atBall, atBall),
        proof: pappp(
            at(pcite(400, "ZF.T"), ball, free("a"), free("B")),
            at(ax("Pure.reflexive", ballType), ball),
        ),
    ))]
    var files = ["Pure/theory/axioms": pureAxioms]
    files["ZF.T/theory/thms"] = thmsFile((theorems + citing).map { ($0.0, $0.1) })
    for (_, serial, text) in theorems + citing { files["ZF.T/proofs/\(serial)"] = text }
    files["ZF.T/proofs/400"] = definitionBox
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    return try Reader(try Export(root: root))
}

private func proof(_ r: inout Reader, _ name: String) throws -> NodeID {
    let theorem = try #require(r.population.first { r.name(of: $0) == name })
    guard case .proved(_, let proof) = try r.read(theorem) else { throw ReadFailed(name: name) }
    return proof
}

private struct ReadFailed: Error {
    let name: String
}

/// The proof's own nodes, interned in a copy of the reader's table: equal to the read proof only when it is that node.
private struct Expected {
    var t: Table
    let o = IRType.o

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func v(_ k: Int, _ T: IRType = .o) throws -> NodeID {
        try n(.isaBound(k, T))
    }

    mutating func iff(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folIff(a, b))
    }

    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.folImplies(a, b))
    }

    mutating func assume(_ a: NodeID, _ body: NodeID) throws -> NodeID {
        try n(.folImpliesIntro(a, body: body))
    }

    mutating func hyp(_ k: Int, _ a: NodeID) throws -> NodeID {
        try n(.hyp(k, a))
    }

    mutating func fix(_ T: IRType, _ body: NodeID) throws -> NodeID {
        try n(.isaAllIntro(T, body: body))
    }
}

/// `reflexive`, `symmetric` and `transitive` are steps, their conclusions read by the type of `≡`: `↔` at `o`,
/// `IFOL.eq` at `i`.
@Test
func reflexiveSymmetricAndTransitiveAreReadAsSteps() throws {
    var r = try pureReader()
    let refl = try proof(&r, "T.refl")
    let sym = try proof(&r, "T.symI")
    let trans = try proof(&r, "T.trans")
    var e = Expected(t: r.table)
    #expect(refl == (try e.fix(.o, try e.n(.isaReflexive(try e.v(0))))))
    let a = try e.v(1, .i)
    let b = try e.v(0, .i)
    let ab = try e.t.equation(.i, a, b)
    #expect(sym == (try e.fix(.i, try e.fix(.i, try e.assume(ab, try e.n(.isaSymmetric(.i, try e.hyp(0, ab))))))))
    let A = try e.v(2)
    let B = try e.v(1)
    let C = try e.v(0)
    let AB = try e.iff(A, B)
    let BC = try e.iff(B, C)
    let step = try e.n(.isaTransitive(.o, try e.hyp(1, AB), try e.hyp(0, BC)))
    #expect(trans == (try e.fix(.o, try e.fix(.o, try e.fix(.o, try e.assume(AB, try e.assume(BC, step)))))))
}

/// The simplifier's rewrite: `Trueprop` erased, `reflexive Trueprop` is the step at the identity, and `combination`
/// takes it and `q` as its children.
@Test
func theSimplifiersRewriteIsReadAsStepsWithTheirPremisesAsChildren() throws {
    var r = try pureReader()
    let read = try proof(&r, "T.rewrite")
    var e = Expected(t: r.table)
    let A = try e.v(1)
    let B = try e.v(0)
    let AB = try e.iff(A, B)
    let identity = try e.n(.isaAbs(.o, body: try e.v(0)))
    let combined = try e.n(.isaCombination(.fn(.o, .o), try e.n(.isaReflexive(identity)), try e.hyp(1, AB)))
    let body = try e.n(.folIffElimL(try e.n(.isaSymmetric(.o, combined)), try e.hyp(0, B)))
    #expect(read == (try e.fix(.o, try e.fix(.o, try e.assume(AB, try e.assume(B, body))))))
}

/// `equal_intr` and `equal_elim` are fol-zfc's `iff_intro` and `iff_elim_l`; an `equal_elim` missing its last premise
/// is η-expanded by the closed proof of the rule, applied to the premise it has.
@Test
func equalIntrAndEqualElimAreTheKernelsIffSteps() throws {
    var r = try pureReader()
    let intr = try proof(&r, "T.intr")
    let partial = try proof(&r, "T.elimPartial")
    var e = Expected(t: r.table)
    let A = try e.v(1)
    let B = try e.v(0)
    let AB = try e.imp(A, B)
    let BA = try e.imp(B, A)
    let iff = try e.iff(A, B)
    let introduced = try e.n(.folIffIntro(try e.hyp(1, AB), try e.hyp(0, BA)))
    #expect(intr == (try e.fix(.o, try e.fix(.o, try e.assume(AB, try e.assume(BA, introduced))))))
    let rule = try e.assume(iff, try e.assume(A, try e.n(.folIffElimL(try e.hyp(1, iff), try e.hyp(0, A)))))
    let applied = try e.n(.folImpliesElim(rule, try e.hyp(0, iff)))
    #expect(partial == (try e.fix(.o, try e.fix(.o, try e.assume(iff, applied)))))
}

/// `abstract_rule` is a step from the pointwise equation to the equation of the λs.
@Test
func abstractRuleIsReadAsAStep() throws {
    var r = try pureReader()
    let read = try proof(&r, "T.abs")
    var e = Expected(t: r.table)
    let F = IRType.fn(.i, .o)
    let x = try e.v(0, .i)
    let Px = try e.n(.isaVarApp(head: try e.v(2, F), args: [x]))
    let Qx = try e.n(.isaVarApp(head: try e.v(1, F), args: [x]))
    let pointwise = try e.n(.ifolAll(.i, body: try e.iff(Px, Qx)))
    #expect(read == (try e.fix(
        F,
        try e.fix(F, try e.assume(pointwise, try e.n(.isaAbstract(F, try e.hyp(0, pointwise))))),
    )))
}

/// A rule takes as many premises as it has, whatever its instance: `equal_elim` at `B := B ⟹ C` takes two, and the
/// third argument applies its conclusion.
@Test
func aRuleTakesItsOwnPremisesWhateverItsInstance() throws {
    var r = try pureReader()
    let read = try proof(&r, "T.elimImp")
    var e = Expected(t: r.table)
    let A = try e.v(2)
    let B = try e.v(1)
    let C = try e.v(0)
    let BC = try e.imp(B, C)
    let h = try e.iff(A, BC)
    let body = try e.n(.folImpliesElim(try e.n(.folIffElimL(try e.hyp(2, h), try e.hyp(1, A))), try e.hyp(0, B)))
    #expect(read == (try e.fix(
        .o,
        try e.fix(.o, try e.fix(.o, try e.assume(h, try e.assume(A, try e.assume(B, body))))),
    )))
}

/// A box binding a variable whose type takes a function is read at its citation: `T.atBall`'s proof is box 400's at
/// `Ball`, `a` and `B`, with no binder or instance at `Ball`'s type, and its hypothesis `Ball ≡ Ball`.
@Test
func aBoxBindingAVariableTakingAFunctionIsReadAtItsCitation() throws {
    var r = try pureReader()
    let cited = try proof(&r, "T.atBall")
    let T = IRType.fn(.i, .fn(.fn(.i, .o), .o))
    let held = patterns(under: [cited], in: r.table)
    #expect(!held.contains(.isaAllIntro(T, body: .o)))
    #expect(!held.contains(.isaAllElim(.o, T)))
    var seen = Set<NodeID>()
    var work = [cited]
    var assumed = [NodeID]()
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .folImpliesIntro(let a, _) = r.table[n] { assumed.append(a) }
        r.table[n].forEachChild { c, _ in work.append(c) }
    }
    #expect(assumed.contains { a in
        r.table.sides(ofEquation: a).map { $0.type == T && $0.left == $0.right } ?? false
    })
}
