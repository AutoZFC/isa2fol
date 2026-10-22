import Foundation
import IR
import Testing
import YXML
@testable import Reader

private func mem(_ a: String, _ b: String) -> String {
    trueprop(app(const("ZF_Base.mem"), a, b))
}

private func imp(_ a: String, _ b: String) -> String {
    app(const("Pure.imp"), a, b)
}

private func all(_ x: String, _ T: String, _ body: String) -> String {
    app(const("Pure.all", T), lam(x, T, body))
}

private let c = const("P.c")
private func F(_ x: String) -> String {
    app(const("P.F"), x)
}

private let d = const("P.d")
private let axiom = mem(F(c), c)

/// A miniature theory above the foundation, `ZF.P`, declaring `P.c :: i` and `P.F :: i ⇒ i` and never defining them
/// (DESIGN "A theory's own parameter, a variable of what reaches it"):
///   P.d_def    P.d ≡ P.F(P.c)                       a definition reaching both
///   P.ax       P.F(P.c) ∈ P.c                       the theory's axiom about them
///   P.axThm    P.F(P.c) ∈ P.c                       P.ax                    the axiom, as Isabelle names it a theorem
///   P.own      x ∈ x ⟹ P.F(P.c) ∈ P.c               λH. P.ax                its own variable after its parameters
///   P.cites    y ∈ y ⟹ P.F(P.c) ∈ P.c               P.own % y               a citation, at the citer's own
///   P.partial  ⋀y. y ∈ y ⟹ P.F(P.c) ∈ P.c           P.own                   cited with fewer arguments than variables
///   P.viaDef   P.d ∈ P.d ⟹ P.d ∈ P.d                λH. H                   reaching both through P.d
///   P.useDef   P.d ≡ P.F(P.c)                       P.d_def                 the definition at its terms
///   P.none     x ∈ x ⟹ x ∈ x                        λH. H                   reaching none
///   box 80     P.F(x) ∈ x ⟹ P.F(x) ∈ x              λH. H
///   P.viaBox   ⋀y. P.F(y) ∈ y ⟹ P.F(y) ∈ y          box 80                  an inlined box, cited with no argument
///   P.through  y ∈ y ⟹ y ∈ y                        λH. (λK. H) %% P.ax     reaching both through its proof alone
///   AC.AC      A ∈ A, stated here as `ZF.AC` states the real one, above the foundation
///   P.choice   a ∈ a                                AC.AC % a               an axiom of the dialect, no premise
private func parameterReader() throws -> Reader {
    let theorems: [(String?, Int, String)] = [
        ("P.axThm", 10, proofFile(frees: [], prop: axiom, proof: paxiom("P.ax"))),
        ("P.own", 20, proofFile(
            frees: [("x", i)],
            prop: imp(mem(free("x"), free("x")), axiom),
            proof: pabsp("H", mem(free("x"), free("x")), paxiom("P.ax")),
        )),
        ("P.cites", 30, proofFile(
            frees: [("y", i)],
            prop: imp(mem(free("y"), free("y")), axiom),
            proof: pappt(pcite(20, "ZF.P", "P.own"), free("y")),
        )),
        ("P.partial", 40, proofFile(
            frees: [],
            prop: all("y", i, imp(mem(bound(0), bound(0)), axiom)),
            proof: pcite(20, "ZF.P", "P.own"),
        )),
        (
            "P.viaDef",
            50,
            proofFile(frees: [], prop: imp(mem(d, d), mem(d, d)), proof: pabsp("H", mem(d, d), pbound(0))),
        ),
        ("P.useDef", 60, proofFile(
            frees: [],
            prop: app(const("Pure.eq", i), d, F(c)),
            proof: paxiom("P.d_def"),
        )),
        ("P.none", 70, proofFile(
            frees: [("x", i)],
            prop: imp(mem(free("x"), free("x")), mem(free("x"), free("x"))),
            proof: pabsp("H", mem(free("x"), free("x")), pbound(0)),
        )),
        (nil, 80, proofFile(
            frees: [("x", i)],
            prop: imp(mem(F(free("x")), free("x")), mem(F(free("x")), free("x"))),
            proof: pabsp("H", mem(F(free("x")), free("x")), pbound(0)),
        )),
        ("P.viaBox", 90, proofFile(
            frees: [],
            prop: all("y", i, imp(mem(F(bound(0)), bound(0)), mem(F(bound(0)), bound(0)))),
            proof: pcite(80, "ZF.P"),
        )),
        ("P.through", 100, proofFile(
            frees: [("y", i)],
            prop: imp(mem(free("y"), free("y")), mem(free("y"), free("y"))),
            proof: pabsp(
                "H",
                mem(free("y"), free("y")),
                pappp(pabsp("K", axiom, pbound(1)), paxiom("P.ax")),
            ),
        )),
        ("P.choice", 110, proofFile(
            frees: [("a", i)],
            prop: mem(free("a"), free("a")),
            proof: pappt(paxiom("AC.AC"), free("a")),
        )),
    ]
    var files: [String: String] = [
        "ZF.P/theory/parents": "ZF.ZF_Base\n",
        "ZF.P/theory/consts": constEntity("P.c", parameters: [], scheme: i)
            + constEntity("P.F", parameters: [], scheme: fn(i, i)) + constEntity("P.d", parameters: [], scheme: i),
        "ZF.P/theory/constdefs": constdefsFile([("P.d", "P.d_def")]),
        "ZF.P/theory/axioms": axiomEntity("P.d_def", prop: app(const("Pure.eq", i), d, F(c)))
            + axiomEntity("P.ax", prop: axiom)
            + axiomEntity("AC.AC", frees: [("A", i)], prop: mem(tagged(1, ["A"], [i]), tagged(1, ["A"], [i]))),
        "ZF.P/theory/thms": thmsFile(theorems.compactMap { f in f.0.map { ($0, f.1) } }),
    ]
    for (_, serial, text) in theorems { files["ZF.P/proofs/\(serial)"] = text }
    let root = try writeExport(files)
    defer { try? FileManager.default.removeItem(atPath: root) }
    return try Reader(try Export(root: root))
}

private func theorem(_ r: Reader, _ name: String) throws -> Theorem {
    try #require(r.population.first { r.name(of: $0) == name })
}

private func proved(_ r: inout Reader, _ name: String) throws -> (statement: NodeID, proof: NodeID)? {
    let outcome = try r.read(try theorem(r, name))
    guard case .proved(let statement, let proof) = outcome else {
        Issue.record("\(name): \(outcome)")
        return nil
    }
    return (statement, proof)
}

private let fT = IRType.fn(.i, .i)
private let memT = IRType.fn(.i, .fn(.i, .o))
private let dDefined = Defined(.zf, "P.d", .object)

/// The nodes a reading under `P.c` and `P.F` is made of, `c` at level 0 and `F` at level 1 of the closure.
private struct Expected {
    var t: Table

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func c(_ depth: Int) throws -> NodeID {
        try n(.isaBound(depth - 1, .i))
    }

    mutating func F(_ depth: Int, at x: NodeID) throws -> NodeID {
        try n(.isaVarApp(head: try n(.isaBound(depth - 2, fT)), args: [x]))
    }

    mutating func etaF(_ depth: Int) throws -> NodeID {
        try n(.isaAbs(.i, body: try F(depth + 1, at: try n(.isaBound(0, .i)))))
    }

    mutating func mem(_ a: NodeID, _ b: NodeID) throws -> NodeID {
        try n(.isaConst(.primitive(.zf(.mem)), memT, args: [a, b]))
    }

    /// `P.F(P.c) ∈ P.c` under `depth` binders, the first two `c` and `F`.
    mutating func axiom(_ depth: Int) throws -> NodeID {
        try mem(try F(depth, at: try c(depth)), try c(depth))
    }

    mutating func d(_ depth: Int) throws -> NodeID {
        try n(.isaConst(.defined(dDefined), .fn(.i, .fn(fT, .i)), args: [try c(depth), try etaF(depth)]))
    }

    mutating func parameters(_ body: NodeID, _ binder: (IRType, NodeID) -> Node) throws -> NodeID {
        try n(binder(.i, try n(binder(fT, body))))
    }
}

/// `P.ax` is no axiom of the unit: `P.axThm`, Isabelle's name for it, reads `⋀c F. A(c, F) ⟹ A(c, F)`, its proof
/// the premise's hypothesis.
@Test
func aConstantATheoryNeverDefinesIsAVariableAndItsAxiomAPremise() throws {
    var r = try parameterReader()
    guard let (statement, proof) = try proved(&r, "P.axThm") else { return }
    var e = Expected(t: r.table)
    let A = try e.axiom(2)
    #expect(statement == (try e.parameters(try e.n(.folImplies(A, A)), Node.ifolAll)))
    #expect(proof == (try e.parameters(try e.n(.folImpliesIntro(A, body: try e.n(.hyp(0, A)))), Node.isaAllIntro)))
    #expect(try r.reach(of: try theorem(r, "P.axThm")) == Reach(parameters: ["P.c", "P.F"], premises: ["P.ax"]))
}

/// DESIGN decision 3: `⋀letters. ⋀p⃗. A⃗ ⟹ ⋀frees. φ` — the parameters and the premise in front of `x`, and the
/// axiom's citation under `H` the premise's hypothesis, one hypothesis further out.
@Test
func theParametersAndPremisesStandInFrontOfTheStatementsOwnVariables() throws {
    var r = try parameterReader()
    guard let (statement, proof) = try proved(&r, "P.own") else { return }
    var e = Expected(t: r.table)
    let A2 = try e.axiom(2)
    let A3 = try e.axiom(3)
    let x = try e.n(.isaBound(0, .i))
    let xx = try e.mem(x, x)
    let own = try e.n(.ifolAll(.i, body: try e.n(.folImplies(xx, A3))))
    #expect(statement == (try e.parameters(try e.n(.folImplies(A2, own)), Node.ifolAll)))
    let body = try e.n(.isaAllIntro(.i, body: try e.n(.folImpliesIntro(xx, body: try e.n(.hyp(1, A3))))))
    #expect(proof == (try e.parameters(try e.n(.folImpliesIntro(A2, body: body)), Node.isaAllIntro)))
}

/// A citation of a statement with parameters takes the citer's own, and the citer's hypothesis of each premise, then
/// Isabelle's arguments: `P.own % y` reads `P.own % c % F %% A % y`.
@Test
func aCitationTakesTheCitersOwnParametersAndHypothesesThenIsabellesArguments() throws {
    var r = try parameterReader()
    guard let (own, _) = try proved(&r, "P.own"), let (statement, proof) = try proved(&r, "P.cites") else { return }
    #expect(statement == own)
    var e = Expected(t: r.table)
    let A2 = try e.axiom(2)
    let A3 = try e.axiom(3)
    let cited = try e.n(.use(.theorem("P.own"), [], own))
    let atParameters = try e.n(.isaAllElim(try e.n(.isaAllElim(cited, try e.c(3))), try e.etaF(3)))
    let discharged = try e.n(.folImpliesElim(atParameters, try e.n(.hyp(0, A3))))
    let atY = try e.n(.isaAllElim(discharged, try e.n(.isaBound(0, .i))))
    let expected = try e.parameters(
        try e.n(.folImpliesIntro(A2, body: try e.n(.isaAllIntro(.i, body: atY)))),
        Node.isaAllIntro,
    )
    #expect(proof == expected)
}

/// Isabelle's proof may cite a theorem with fewer arguments than its variables: in front of them, the citer's own
/// parameters and hypotheses still conclude what Isabelle's citation does — `P.own` alone, and box 80 alone, inlined.
@Test
func aCitationGivingFewerArgumentsThanItsTheoremsVariablesReadsAsIsabellesDoes() throws {
    var r = try parameterReader()
    guard
        let (own, _) = try proved(&r, "P.own"), let (partial, proof) = try proved(&r, "P.partial"),
        let (_, viaBox) = try proved(&r, "P.viaBox")
    else { return }
    #expect(partial == own)
    var e = Expected(t: r.table)
    let A2 = try e.axiom(2)
    let cited = try e.n(.use(.theorem("P.own"), [], own))
    let atParameters = try e.n(.isaAllElim(try e.n(.isaAllElim(cited, try e.c(2))), try e.etaF(2)))
    let discharged = try e.n(.folImpliesElim(atParameters, try e.n(.hyp(0, A2))))
    #expect(proof == (try e.parameters(try e.n(.folImpliesIntro(A2, body: discharged)), Node.isaAllIntro)))
    guard
        case .isaAllIntro(let T, let inlined) = r.table[viaBox],
        case .isaAllElim(_, let atF) = r.table[inlined]
    else {
        Issue.record("P.viaBox: \(r.table[viaBox])")
        return
    }
    #expect(T == fT)
    #expect(atF == (try e.n(.isaAbs(.i, body: try e.n(.isaVarApp(
        head: try e.n(.isaBound(1, fT)),
        args: [try e.n(.isaBound(0, .i))],
    ))))))
    #expect(try r.reach(of: try theorem(r, "P.viaBox")) == Reach(parameters: ["P.F"]))
}

/// A definition reaching a parameter takes it as a leading argument: `P.d` is `P.d(c, F)`, its definiens `λc F. F(c)`,
/// and its definition at its terms is applied at the citer's own.
@Test
func aDefinitionReachingAParameterTakesItAsALeadingArgument() throws {
    var r = try parameterReader()
    guard let (statement, _) = try proved(&r, "P.viaDef"), let (_, useDef) = try proved(&r, "P.useDef") else {
        return
    }
    var e = Expected(t: r.table)
    let D = try e.mem(try e.d(2), try e.d(2))
    #expect(statement == (try e.parameters(try e.n(.folImplies(D, D)), Node.ifolAll)))
    #expect(try r.reach(of: try theorem(r, "P.viaDef")) == Reach(parameters: ["P.c", "P.F"]))
    let definition = try r.definition(of: dDefined, at: .fn(.i, .fn(fT, .i)))
    #expect(definition.parameters == 2)
    var f = Expected(t: r.table)
    #expect(definition.definiens == (try f.parameters(try f.F(2, at: try f.c(2)), Node.isaAbs)))
    guard
        case .isaAllIntro(.i, let inner) = r.table[useDef], case .isaAllIntro(_, let at) = r.table[inner],
        case .isaDefinition(let axiom, .constant(dDefined), [], _, let args) = r.table[at]
    else {
        Issue.record("P.useDef: \(r.table[useDef])")
        return
    }
    #expect(axiom == "P.d_def")
    #expect(args == [try f.c(2), try f.etaF(2)])
}

/// A statement reaching no parameter reads as it did: no binder before its own, no premise.
@Test
func aStatementReachingNoParameterReadsUnchanged() throws {
    var r = try parameterReader()
    guard let (statement, _) = try proved(&r, "P.none") else { return }
    var e = Expected(t: r.table)
    let x = try e.n(.isaBound(0, .i))
    #expect(statement == (try e.n(.ifolAll(.i, body: try e.n(.folImplies(try e.mem(x, x), try e.mem(x, x)))))))
    #expect(try r.reach(of: try theorem(r, "P.none")) == Reach())
}

/// DESIGN decision 4: what the proof cites counts, not only what the statement says — `P.through` states nothing of
/// `P.c` or `P.F`, and its proof cites `P.ax`.
@Test
func aParameterTheProofAloneReachesIsTheStatementsToo() throws {
    var r = try parameterReader()
    guard let (statement, _) = try proved(&r, "P.through") else { return }
    var e = Expected(t: r.table)
    let A2 = try e.axiom(2)
    let y = try e.n(.isaBound(0, .i))
    let own = try e.n(.ifolAll(.i, body: try e.n(.folImplies(try e.mem(y, y), try e.mem(y, y)))))
    #expect(statement == (try e.parameters(try e.n(.folImplies(A2, own)), Node.ifolAll)))
    #expect(try r.reach(of: try theorem(r, "P.through")) == Reach(parameters: ["P.c", "P.F"], premises: ["P.ax"]))
}

/// An axiom of the dialect is cited as itself wherever its theory stands — `AC.AC` is stated by `ZF.AC`, above the
/// foundation — and is never a premise: derived from NBG's Choice, it is no theory's own.
@Test
func anAxiomOfTheDialectAboveTheFoundationIsCitedNeverAPremise() throws {
    var r = try parameterReader()
    guard let (statement, proof) = try proved(&r, "P.choice") else { return }
    #expect(try r.reach(of: try theorem(r, "P.choice")) == Reach())
    var e = Expected(t: r.table)
    let a = try e.n(.isaBound(0, .i))
    let aa = try e.mem(a, a)
    #expect(statement == (try e.n(.ifolAll(.i, body: aa))))
    let choice = try e.n(.use(.axiom(.zf(.choice)), [], try e.n(.ifolAll(.i, body: aa))))
    #expect(proof == (try e.n(.isaAllIntro(.i, body: try e.n(.isaAllElim(choice, a))))))
}

private func contains(_ root: NodeID, _ t: Table, where holds: (NodeID) -> Bool) -> Bool {
    var seen = Set<NodeID>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if holds(n) { return true }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return false
}

/// On the export (DESIGN "A theory's own parameter", Tests): ZF-IMP's `loc` and ZF-Coind's `Const` read as variables of
/// what reaches them, in front of a statement's own; `constNEE` a premise, its citation the premise's hypothesis and a
/// citation of a theorem resting on it at the citer's own; ZF's theorems reach none.
/// ⚠ It loads every proof of the export, 571 s in a debug build:
/// `ISA2FOL_SCALE=1 swift test -c release --filter theExportsParametersReadAsVariablesOfWhatReachesThem`.
@Test(.enabled(if: ProcessInfo.processInfo.environment["ISA2FOL_SCALE"] != nil))
func theExportsParametersReadAsVariablesOfWhatReachesThem() throws {
    let root = "data/zf_export"
    try #require(FileManager.default.fileExists(atPath: root), "export missing at \(root) — run from the repo root")
    var r = try Reader(try Export(root: root))
    func named(_ name: String) throws -> Theorem {
        try #require(r.population.first { r.name(of: $0) == name })
    }
    let aexp = Defined(.zf, "Com.aexp", .object)

    let intro = try named("Com.aexp.intros(1)")
    #expect(try r.reach(of: intro) == Reach(parameters: ["Com.loc"]))
    guard
        case .proved(let statement, _) = try r.read(intro), case .ifolAll(.i, let afterLoc) = r.table[statement],
        case .ifolAll(.i, _) = r.table[afterLoc]
    else {
        Issue.record("Com.aexp.intros(1) is not closed over loc, then n")
        return
    }
    #expect(contains(statement, r.table) { n in
        guard case .isaConst(.defined(aexp), .fn(.i, .i), let args) = r.table[n], args.count == 1 else { return false }
        return true
    })
    let definition = try r.definition(of: aexp, at: .fn(.i, .i))
    #expect(definition.parameters == 1)
    guard case .isaAbs(.i, _) = r.table[definition.definiens] else {
        Issue.record("aexp's definiens takes no leading λ: \(r.table[definition.definiens])")
        return
    }

    let nee = try named("Language.constNEE")
    #expect(try r.reach(of: nee) == Reach(parameters: ["Language.Const"], premises: ["Language.constNEE"]))
    guard
        case .proved(let neeStatement, _) = try r.read(nee), case .ifolAll(.i, let premised) = r.table[neeStatement],
        case .folImplies(let axiom, let own) = r.table[premised]
    else {
        Issue.record("Language.constNEE is not ⋀Const. constNEE ⟹ …")
        return
    }
    #expect(axiom == own)

    let valNEE = try named("Values.ValNEE")
    let reach = try r.reach(of: valNEE)
    #expect(reach.parameters.contains("Language.Const"))
    #expect(reach.premises == ["Language.constNEE"])
    guard case .proved(_, let valProof) = try r.read(valNEE) else {
        Issue.record("Values.ValNEE is not read")
        return
    }
    #expect(contains(valProof, r.table) { n in
        guard
            case .folImpliesElim(let p, let h) = r.table[n], case .isaAllElim(let u, let v) = r.table[p],
            case .use(.theorem("Language.constNEE"), _, _) = r.table[u], case .isaBound(_, .i) = r.table[v],
            case .hyp = r.table[h]
        else { return false }
        return true
    })

    #expect(try r.reach(of: try named("ZF_Base.subsetI")) == Reach())
}
