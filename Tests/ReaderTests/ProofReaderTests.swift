import Foundation
import IR
import Testing
import YXML
@testable import Reader

private let P = trueprop(free("P"))
private let Q = trueprop(free("Q"))
private func mem(_ a: String, _ b: String) -> String {
    trueprop(app(const("ZF_Base.mem"), a, b))
}

private func eq(_ T: String, _ a: String) -> String {
    trueprop(app(const("IFOL.eq", T), a, a))
}

private func imp(_ a: String, _ b: String) -> String {
    app(const("Pure.imp"), a, b)
}

private func all(_ x: String, _ T: String, _ body: String) -> String {
    app(const("Pure.all", T), lam(x, T, body))
}

private let termClass = { (T: String) in ofclass(T, "IFOL.term") }
private let falsum = trueprop(const("IFOL.False"))
private let dummy = typeT("dummy")
private let typeB = tfree("'b")

/// A miniature export, one fixture per rule of the proof reader:
///   T.imp        P ⟹ P                     λH. H
///   T.fix        ⋀x. x ∈ A ⟹ x ∈ A         ⋀x. λH. H
///   T.outer      Q ⟹ (⋀x. Q)               λH. ⋀x. H          the hypothesis is used under a ⋀
///   T.cite       a ∈ A ⟹ a ∈ A             T.fix % A % a     a named theorem is a `use`
///   box 50       x ∈ B ⟹ x ∈ B             λH. H
///   T.inline     a ∈ A ⟹ a ∈ A             box50 % a % A     an unnamed box is inlined
///   box 250      P ⟹ P                     λH. H             binds a proposition: a statement, named by its content
///   box 255      as box 250, at another serial
///   T.viaBox     Q ⟹ Q                     box250 % Q;       T.viaTwin  Q ⟹ Q   box255 % Q
///   T.boundPremise  (⋀P. P ⟹ P) ⟹ Q ⟹ Q     λH q. H % Q %% q     Pure's ⋀ over a proposition in a formula
///   T.introProp     Q ⟹ Q                   (⋀P. λh. h) % Q      Pure's ⋀ over a proposition introduced in a proof
///   T.reflAx     OFCLASS('a, term) ⟹ ⋀a. a = a, a theorem cited, never read
///   T.termI      OFCLASS(i, term), a theorem cited, never read
///   T.arity      OFCLASS(i, term)          T.termI           as arity_term_i
///   box 95       OFCLASS(i, term)          T.arity           as box 1792: how a proof discharges at i
///   T.axiom      b = b                     reflAx[i] %% box95 % b
///   box 80       OFCLASS('a, term) ⟹ x = x   λH. reflAx['a] %% H % x
///   T.poly       c = c                     box80[i] % c %% box95     terms first: the ∀-closure is outermost
///   T.polyNamed  OFCLASS('a, term) ⟹ y = y   as box 80, read at i: every type variable restricted to term; cited by
/// T.usesPoly at i
///   T.polyPartial  OFCLASS('a, term) ⟹ (⋀h::'b. Q) ⟹ (⋀h::'b. Q)   'b unrestricted: read as stated; cited by
/// T.usesPartial and T.usesPartialAgain at i, i
///   T.defax      a theory's own axiom with a typed free: A ∈ A;   T.useDef  a ∈ a   T.defax % a, its premise
///   T.vacAx      (⋀h::'a. Q) ⟹ Q, a theorem cited;   T.hidden  Q ⟹ Q   λH. vacAx[dummy] % Q %% (⋀h::dummy. H)
///   T.hiddenTerm (⋀x::i. ⋀R::o. Q) ⟹ Q        λH. H % dummy_pattern::i % dummy_pattern::o   variables only the proof
///                uses
///   T.hiddenFunctions  (⋀x y::i. ⋀R::o. Q) ⟹ P(a) ⟹ Q   λH K. H % F(λx. P x, Q) % g(c) % C(c), each of F, g, c, C
///                a dummy_pattern, at (i ⇒ o) ⇒ o ⇒ i, i ⇒ i, i and i ⇒ o
///   IFOL.not_def_raw  a definition;  T.useNotDef cites it.   IFOL.bogus  an unlisted IFOL axiom;  T.useBogus cites it
///   Pure.prop_def  an applied definition;  T.useProp  PROP Q ≡ Q   prop_def % Q
///   IFOL.term_class_def  OFCLASS('a, term) ≡ (⋀P. P ⟹ P);  T.useClassDef  its statement at i   term_class_def[i]
///   T.anyType    A(x) ⟹ A(x)   'a unrestricted, λH. H;  T.usesAny  B(b) ⟹ B(b)   anyType[i] % B % b
///   T.sortAlgebra  OFCLASS(i, term) by ZClassp — 0 in the export, refused
///   T.nop, T.oracle, T.wrong, T.freeHyp, T.unbound, T.notAll, T.undeclared, T.header
private let notDef = app(
    const("Pure.eq", fn(o, o)),
    const("IFOL.Not"),
    lam("P", o, app(const("IFOL.imp"), bound(0), const("IFOL.False"))),
)

private let propDef = app(
    const("Pure.eq", prop),
    app(const("Pure.prop"), tagged(1, ["A"], [prop])),
    tagged(1, ["A"], [prop]),
)

private func classDefAt(_ T: String) -> String {
    app(const("Pure.eq", prop), termClass(T), app(const("Pure.all", prop), lam("P", prop, imp(bound(0), bound(0)))))
}

private let ax = trueprop(app(free("A"), free("x")))
private let bb = trueprop(app(free("B"), free("b")))

private func miniReader() throws -> Reader {
    var files: [String: String] = [
        "Pure/theory/axioms": axiomEntity("Pure.prop_def", frees: [("A", prop)], prop: propDef),
        "IFOL/theory/axioms": axiomEntity("IFOL.not_def_raw", prop: notDef) + axiomEntity("IFOL.bogus", prop: falsum)
            + termClassDef,
        "ZF.T/theory/axioms": axiomEntity(
            "T.defax",
            frees: [("A", i)],
            prop: mem(tagged(1, ["A"], [i]), tagged(1, ["A"], [i])),
        ),
    ]
    let theorems: [(String?, Int, String)] = [
        ("T.termI", 400, proofFile(frees: [], prop: termClass(i))),
        ("T.reflAx", 401, proofFile(
            tfrees: ["'a"],
            frees: [],
            prop: imp(termClass(typeA), all("a", typeA, eq(typeA, bound(0)))),
        )),
        ("T.vacAx", 402, proofFile(tfrees: ["'a"], frees: [("Q", o)], prop: imp(all("h", typeA, Q), Q))),
        ("T.imp", 10, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        (
            "T.fix",
            20,
            proofFile(
                frees: [("A", i)],
                prop: all("x", i, imp(mem(bound(0), free("A")), mem(bound(0), free("A")))),
                proof: pabst("x", i, pabsp("H", mem(bound(0), free("A")), pbound(0))),
            ),
        ),
        (
            "T.outer",
            30,
            proofFile(frees: [("Q", o)], prop: imp(Q, all("x", i, Q)), proof: pabsp("H", Q, pabst("x", i, pbound(0)))),
        ),
        (
            "T.cite",
            40,
            proofFile(
                frees: [("a", i), ("A", i)],
                prop: imp(mem(free("a"), free("A")), mem(free("a"), free("A"))),
                proof: pappt(pappt(pcite(20, "ZF.T", "T.fix"), free("A")), free("a")),
            ),
        ),
        (
            nil,
            50,
            proofFile(
                frees: [("x", i), ("B", i)],
                prop: imp(mem(free("x"), free("B")), mem(free("x"), free("B"))),
                proof: pabsp("H", mem(free("x"), free("B")), pbound(0)),
            ),
        ),
        (
            "T.inline",
            60,
            proofFile(
                frees: [("a", i), ("A", i)],
                prop: imp(mem(free("a"), free("A")), mem(free("a"), free("A"))),
                proof: pappt(pappt(pcite(50, "ZF.T"), free("a")), free("A")),
            ),
        ),
        ("T.axiom", 70, proofFile(
            frees: [("b", i)],
            prop: eq(i, free("b")),
            proof: pappt(pappp(pcite(401, "ZF.T", "T.reflAx", i), pcite(95, "ZF.T")), free("b")),
        )),
        (nil, 80, proofFile(
            tfrees: ["'a"],
            frees: [("x", typeA)],
            prop: imp(termClass(typeA), eq(typeA, free("x"))),
            proof: pabsp(
                "H",
                termClass(typeA),
                pappt(pappp(pcite(401, "ZF.T", "T.reflAx", typeA), pbound(0)), free("x")),
            ),
        )),
        (nil, 95, proofFile(frees: [], prop: termClass(i), proof: pcite(120, "ZF.T", "T.arity"))),
        ("T.poly", 90, proofFile(
            frees: [("c", i)],
            prop: eq(i, free("c")),
            proof: pappp(pappt(pcite(80, "ZF.T", "", i), free("c")), pcite(95, "ZF.T")),
        )),
        (
            "T.polyNamed",
            100,
            proofFile(
                tfrees: ["'a"],
                frees: [("y", typeA)],
                prop: imp(termClass(typeA), eq(typeA, free("y"))),
                proof: pabsp(
                    "H",
                    termClass(typeA),
                    pappt(pappp(pcite(401, "ZF.T", "T.reflAx", typeA), pbound(0)), free("y")),
                ),
            ),
        ),
        ("T.usesPoly", 110, proofFile(
            frees: [("d", i)],
            prop: eq(i, free("d")),
            proof: pappp(
                pappt(pcite(100, "ZF.T", "T.polyNamed", i), free("d")),
                pcite(95, "ZF.T"),
            ),
        )),
        ("T.arity", 120, proofFile(frees: [], prop: termClass(i), proof: pcite(400, "ZF.T", "T.termI"))),
        (
            "T.useDef",
            125,
            proofFile(frees: [("a", i)], prop: mem(free("a"), free("a")), proof: pappt(paxiom("T.defax"), free("a"))),
        ),
        ("T.hidden", 127, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pabsp(
            "H",
            Q,
            pappp(
                pappt(
                    pcite(402, "ZF.T", "T.vacAx", dummy),
                    free("Q"),
                ),
                pabst("h", dummy, pbound(0)),
            ),
        ))),
        ("T.hiddenTerm", 128, proofFile(
            frees: [("Q", o)],
            prop: imp(all("x", i, all("R", o, Q)), Q),
            proof: pabsp(
                "H",
                all("x", i, all("R", o, Q)),
                pappt(pappt(pbound(0), const("Pure.dummy_pattern", i)), const("Pure.dummy_pattern", o)),
            ),
        )),
        ("T.hiddenFunctions", 138, proofFile(
            frees: [("Q", o), ("P", fn(i, o)), ("a", i)],
            prop: imp(all("x", i, all("y", i, all("R", o, Q))), imp(trueprop(app(free("P"), free("a"))), Q)),
            proof: pabsp(
                "H",
                all("x", i, all("y", i, all("R", o, Q))),
                pabsp("K", trueprop(app(free("P"), free("a"))), pappt(
                    pappt(
                        pappt(
                            pbound(1),
                            app(
                                const("Pure.dummy_pattern", fn(fn(i, o), fn(o, i))),
                                lam("x", i, app(free("P"), bound(0))),
                                free("Q"),
                            ),
                        ),
                        app(const("Pure.dummy_pattern", fn(i, i)), const("Pure.dummy_pattern", i)),
                    ),
                    app(const("Pure.dummy_pattern", fn(i, o)), const("Pure.dummy_pattern", i)),
                )),
            ),
        )),
        ("T.useNotDef", 129, proofFile(frees: [], prop: notDef, proof: paxiom("IFOL.not_def_raw"))),
        ("T.useBogus", 131, proofFile(frees: [], prop: falsum, proof: paxiom("IFOL.bogus"))),
        (
            "T.useProp",
            135,
            proofFile(
                frees: [("Q", o)],
                prop: app(const("Pure.eq", prop), app(const("Pure.prop"), Q), Q),
                proof: pappt(paxiom("Pure.prop_def"), Q),
            ),
        ),
        ("T.useClassDef", 136, proofFile(frees: [], prop: classDefAt(i), proof: paxiom("IFOL.term_class_def", i))),
        ("T.anyType", 280, proofFile(
            tfrees: ["'a"],
            frees: [("A", fn(typeA, o)), ("x", typeA)],
            prop: imp(ax, ax),
            proof: pabsp("H", ax, pbound(0)),
        )),
        ("T.usesAny", 285, proofFile(
            frees: [("B", fn(i, o)), ("b", i)],
            prop: imp(bb, bb),
            proof: pappt(pappt(pcite(280, "ZF.T", "T.anyType", i), free("B")), free("b")),
        )),
        ("T.unboundType", 132, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pabsp(
            "H",
            Q,
            pappp(
                pappt(pcite(402, "ZF.T", "T.vacAx", tfree("'b")), free("Q")),
                pabst(
                    "h",
                    tfree("'b"),
                    pbound(0),
                ),
            ),
        ))),
        ("T.nop", 130, proofFile(frees: [], prop: falsum, proof: pnop)),
        ("T.oracle", 140, proofFile(frees: [], prop: falsum, proof: poracle("skip_proof"))),
        ("T.wrong", 150, proofFile(frees: [("Q", o), ("P", o)], prop: imp(Q, P), proof: pabsp("H", Q, pbound(0)))),
        ("T.freeHyp", 160, proofFile(frees: [], prop: falsum, proof: phyp(falsum))),
        ("T.sortAlgebra", 170, proofFile(frees: [], prop: termClass(i), proof: pofclass(i, "IFOL.term"))),
        ("T.unbound", 180, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(3)))),
        (
            "T.notAll",
            190,
            proofFile(frees: [("P", o)], prop: imp(P, P), proof: pappt(pabsp("H", P, pbound(0)), free("P"))),
        ),
        ("T.undeclared", 200, proofFile(
            frees: [("P", o)],
            prop: imp(P, P),
            proof: pappt(
                pabst("x", o, pabsp("H", trueprop(bound(0)), pbound(0))),
                free("Z"),
            ),
        )),
        ("T.header", 210, proofFile(frees: [("A", i), ("a", i)], prop: mem(free("a"), free("A")), proof: pnop)),
        ("T.simps(2)", 220, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        (nil, 250, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        (nil, 255, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        ("T.viaBox", 260, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pappt(pcite(250, "ZF.T"), free("Q")))),
        ("T.viaTwin", 265, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pappt(pcite(255, "ZF.T"), free("Q")))),
        (
            "T.boundPremise",
            270,
            proofFile(
                frees: [("Q", o)],
                prop: imp(all("P", o, imp(trueprop(bound(0)), trueprop(bound(0)))), imp(Q, Q)),
                proof: pabsp(
                    "H",
                    all("P", o, imp(trueprop(bound(0)), trueprop(bound(0)))),
                    pabsp("q", Q, pappp(pappt(pbound(1), free("Q")), pbound(0))),
                ),
            ),
        ),
        ("T.introProp", 275, proofFile(
            frees: [("Q", o)],
            prop: imp(Q, Q),
            proof: pappt(
                pabst("P", o, pabsp("h", trueprop(bound(0)), pbound(0))),
                free("Q"),
            ),
        )),
        ("T.late", 300, proofFile(
            frees: [("P", fn(i, o)), ("R", o)],
            prop: imp(all("x", i, trueprop(app(free("P"), bound(0)))), imp(trueprop(free("R")), trueprop(free("R")))),
            proof: pabsp(
                "H",
                all("x", i, trueprop(app(free("P"), bound(0)))),
                pabsp("r", trueprop(free("R")), pbound(0)),
            ),
        )),
        ("T.citesLate", 310, proofFile(
            frees: [("A", i), ("Q", o)],
            prop: imp(all("x", i, mem(bound(0), free("A"))), imp(Q, Q)),
            proof: pappt(
                pappt(pcite(300, "ZF.T", "T.late"), lam("y", i, app(const("ZF_Base.mem"), bound(0), free("A")))),
                free("Q"),
            ),
        )),
        ("T.leavesLetter", 320, proofFile(
            frees: [("A", i)],
            prop: all("R", o, imp(all("x", i, mem(bound(0), free("A"))), imp(trueprop(bound(0)), trueprop(bound(0))))),
            proof: pappt(pcite(300, "ZF.T", "T.late"), lam("y", i, app(const("ZF_Base.mem"), bound(0), free("A")))),
        )),
        ("T.polyPartial", 230, proofFile(
            tfrees: ["'a", "'b"],
            frees: [("Q", o)],
            prop: imp(termClass(typeA), imp(all("h", typeB, Q), all("h", typeB, Q))),
            proof: pabsp(
                "C",
                termClass(typeA),
                pabsp("H", all("h", typeB, Q), pbound(0)),
            ),
        )),
        ("T.usesPartial", 240, proofFile(
            frees: [("Q", o)],
            prop: imp(all("h", i, Q), all("h", i, Q)),
            proof: pappp(
                pappt(pcite(230, "ZF.T", "T.polyPartial", i, i), free("Q")),
                pcite(95, "ZF.T"),
            ),
        )),
        ("T.usesPartialAgain", 245, proofFile(
            frees: [("R", o)],
            prop: imp(all("h", i, trueprop(free("R"))), all("h", i, trueprop(free("R")))),
            proof: pappp(
                pappt(pcite(230, "ZF.T", "T.polyPartial", i, i), free("R")),
                pcite(95, "ZF.T"),
            ),
        )),
    ]
    files["ZF.T/theory/thms"] = thmsFile(theorems.compactMap { f in f.0.map { ($0, f.1) } })
    for (_, serial, text) in theorems { files["ZF.T/proofs/\(serial)"] = text }
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

private func uses(_ root: NodeID, _ t: Table) -> Set<String> {
    var seen = Set<NodeID>()
    var names = Set<String>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .use(let cited, _, _) = t[n] { names.insert(cited.name) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return names
}

private struct Citation: Hashable {
    let cited: Cited
    let types: [IRType]
}

private func citations(_ root: NodeID, _ t: Table) -> Set<Citation> {
    var seen = Set<NodeID>()
    var found = Set<Citation>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .use(let cited, let types, _) = t[n] { found.insert(Citation(cited: cited, types: types)) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private struct Unfolded: Hashable {
    let axiom: String
    let defines: Definiendum
    let types: [IRType]
    let terms: [NodeID]
}

private func definitions(_ root: NodeID, _ t: Table) -> Set<Unfolded> {
    var seen = Set<NodeID>()
    var found = Set<Unfolded>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .isaDefinition(let axiom, let d, let types, _, let args) = t[n] {
            found.insert(Unfolded(axiom: axiom, defines: d, types: types, terms: args))
        }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private func roots(citing name: String, _ root: NodeID, _ t: Table) -> Set<NodeID> {
    var seen = Set<NodeID>()
    var found = Set<NodeID>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .use(.theorem(let cited), _, let stated) = t[n], cited == name { found.insert(stated) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private let reflAx = Cited.theorem("T.reflAx")

private func failure(_ r: inout Reader, _ name: String) throws -> ReadFailure? {
    do {
        let outcome = try r.read(try theorem(r, name))
        Issue.record("\(name) read as \(outcome)")
    } catch let f as ReadFailure {
        return f
    }
    return nil
}

@Test
func aHypothesisIsItsBindersFormula() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.imp") else { return }
    var t = r.table
    let P = try t.intern(.isaBound(0, .o))
    #expect(proof == (try t.intern(.isaAllIntro(
        .o,
        body: try t.intern(.folImpliesIntro(P, body: try t.intern(.hyp(0, P)))),
    ))))
}

/// The hypothesis `Q` is read where it is assumed; used under `⋀x` it is one binder further out.
@Test
func aHypothesisUsedUnderATermBinderIsShifted() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.outer") else { return }
    var t = r.table
    let used = try t.intern(.isaAllIntro(.i, body: try t.intern(.hyp(0, try t.intern(.isaBound(1, .o))))))
    let expected = try t.intern(.isaAllIntro(
        .o,
        body: try t.intern(.folImpliesIntro(try t.intern(.isaBound(0, .o)), body: used)),
    ))
    #expect(proof == expected)
}

@Test
func aTermBinderIsAnIsaQuantifierStep() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.fix") else { return }
    guard case .isaAllIntro(.i, let inner) = r.table[proof], case .isaAllIntro(.i, _) = r.table[inner] else {
        Issue.record("\(r.table[proof])")
        return
    }
}

@Test
func aNamedCitationIsAUseInstantiatedByItsTermArguments() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.cite") else { return }
    #expect(uses(proof, r.table) == ["T.fix"])
    #expect(r.cited.map { r.name(of: $0) } == ["T.fix"])
}

/// A statement enters the pipeline under the name its citations use: an index `(2)` is spelled
/// `.2` (CLAUDE.md rule 5).
@Test
func aTheoremsClaimNameIsTheNameItsCitationsUse() throws {
    var r = try miniReader()
    #expect(try claimName(try #require(r.name(of: try theorem(r, "T.simps(2)")))) == "T.simps.2")
    let fix = try claimName(try #require(r.name(of: try theorem(r, "T.fix"))))
    guard let (_, proof) = try proved(&r, "T.cite") else { return }
    #expect(uses(proof, r.table) == [fix])
}

/// DESIGN "Letters first": a statement binds its propositions outermost, and a citation instantiates them first —
/// `T.late`'s `R` before its `P`, though Isabelle's header lists `P` first.
@Test
func aCitationInstantiatesItsLettersFirst() throws {
    var r = try miniReader()
    guard
        let (late, _) = try proved(&r, "T.late"),
        let (_, proof) = try proved(&r, "T.citesLate")
    else { return }
    guard case .ifolAll(.o, _) = r.table[late] else {
        Issue.record("T.late: \(r.table[late])")
        return
    }
    var atTheCitation = [IRType]()
    var seen = Set<NodeID>()
    var work = [proof]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case .isaAllElim(let p, let a) = r.table[n], case .use = r.table[p], let T = r.table.type(of: a) {
            atTheCitation.append(T)
        }
        r.table[n].forEachChild { c, _ in work.append(c) }
    }
    #expect(atTheCitation == [.o])
}

/// `T.late` cited at its `P` alone, its letter `R` left: closed letters first, `T.late` has no order that citation
/// reads
/// in.
@Test
func aCitationLeavingALetterBehindAnInstantiatedFreeIsRefused() throws {
    var r = try miniReader()
    #expect(try r.read(try theorem(r, "T.leavesLetter")) == .refused(.letterLeft))
}

@Test
func anUnnamedBoxIsInlined() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.inline") else { return }
    #expect(uses(proof, r.table).isEmpty)
    #expect(r.cited.isEmpty)
}

/// A `⋀` Isabelle writes over a proposition — `Pure.all` in a formula, `ZAbst` in a proof — is Pure's `⋀`, its own
/// nodes
/// and its own variable; a free proposition, which the reader closes over, stays the schema letter's `ifolAll` at `o`.
@Test
func pureAllOverAPropositionIsItsOwnNodeAndAFreeOneTheLetter() throws {
    var r = try miniReader()
    guard
        let (statement, _) = try proved(&r, "T.boundPremise"),
        let (_, intro) = try proved(&r, "T.introProp")
    else { return }
    var t = r.table
    let P = try t.intern(.isaPropBound(0))
    let Q = try t.intern(.isaBound(0, .o))
    let bound = try t.intern(.isaPropAll(body: try t.intern(.folImplies(P, P))))
    #expect(statement == (try t.intern(.ifolAll(
        .o,
        body: try t.intern(.folImplies(bound, try t.intern(.folImplies(Q, Q)))),
    ))))
    let inner = try t.intern(.isaPropIntro(body: try t.intern(.folImpliesIntro(P, body: try t.intern(.hyp(0, P))))))
    #expect(intro == (try t.intern(.isaAllIntro(.o, body: try t.intern(.isaAllElim(inner, Q))))))
}

/// Box 250 binds the proposition `P`: a statement, cited by the name of its proof's content — `T.imp`'s proof, the same
/// node — and box 255, the same box at another serial, by the same name: a serial names a box only within one build.
@Test
func aBoxBindingAPropositionIsCitedByItsContentsName() throws {
    var r = try miniReader()
    guard
        let (statement, own) = try proved(&r, "T.imp"), let (_, proof) = try proved(&r, "T.viaBox"),
        let (_, twin) = try proved(&r, "T.viaTwin")
    else { return }
    let name = "T.BOX_" + fingerprint(own, r.table)
    #expect(uses(proof, r.table) == [name])
    #expect(uses(twin, r.table) == [name])
    #expect(roots(citing: name, proof, r.table) == [statement])
    #expect(r.cited.map { r.name(of: $0) } == [nil])
}

/// `T.reflAx`'s class premise is discharged by an ordinary ⟹-elim, with box 95's inlined proof; read at `i`, every type
/// variable restricted to `term`, it is cited with no types.
@Test
func aClassDischargeIsAnOrdinaryPremise() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.axiom") else { return }
    #expect(citations(proof, r.table) == [
        Citation(cited: reflAx, types: []),
        Citation(cited: .theorem("T.arity"), types: []),
    ])
}

/// A theory's own axiom is a premise of what reaches it (DESIGN "A theory's own parameter"), its frees closed like a
/// theorem's and its typed variables agreeing: `T.useDef` reads `(⋀A. A ∈ A) ⟹ ⋀a. a ∈ a`, the citation the
/// premise's hypothesis at `a`.
@Test
func aTheorysOwnAxiomIsAPremiseItsFreesClosedLikeATheorems() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.useDef") else { return }
    var t = r.table
    let a = try t.intern(.isaBound(0, .i))
    let aa = try t.intern(.isaConst(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), args: [a, a]))
    let axiom = try t.intern(.ifolAll(.i, body: aa))
    #expect(statement == (try t.intern(.folImplies(axiom, axiom))))
    let atA = try t.intern(.isaAllElim(try t.intern(.hyp(0, axiom)), a))
    #expect(proof == (try t.intern(.folImpliesIntro(axiom, body: try t.intern(.isaAllIntro(.i, body: atA))))))
    #expect(uses(proof, r.table).isEmpty)
}

/// Box 80 binds its class hypothesis and discharges `T.reflAx`'s class premise with it: both bookkeeping.
@Test
func aPolymorphicBoxIsInlinedAtTheInstanceItIsCitedAt() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.poly") else { return }
    #expect(citations(proof, r.table) == [
        Citation(cited: reflAx, types: []),
        Citation(cited: .theorem("T.arity"), types: []),
    ])
}

/// Every type variable of `T.polyNamed` carries `OFCLASS(α, term)`, and `i` is the only type in `term`: it is read at
/// `i`,
/// its proof with it.
@Test
func aTheoremRestrictedToTermIsReadAtI() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.polyNamed") else { return }
    var t = r.table
    let y = try t.intern(.isaBound(0, .i))
    let member = try t.intern(.isaOfClass(.i, ifolTerm))
    let eq = try t.intern(.isaConst(.primitive(.ifol(.eq)), .fn(.i, .fn(.i, .o)), args: [y, y]))
    #expect(statement == (try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(member, eq))))))
    #expect(citations(proof, r.table) == [Citation(cited: reflAx, types: [])])
}

/// `T.polyPartial`'s `'b` carries no class: it is read at its variables. Cited at `[i, i]` it binds `Q`, a proposition,
/// on its spine there: its instance there is a statement of the unit, named by its proof's content as a box binding a
/// proposition is, and cited with no types — by `T.usesPartial` and `T.usesPartialAgain` alike.
@Test
func aTheoremCitedAtATypeBindingAPropositionIsItsInstanceAStatement() throws {
    var r = try miniReader()
    guard
        let (statement, _) = try proved(&r, "T.polyPartial"),
        let (_, user) = try proved(&r, "T.usesPartial"),
        let (_, again) = try proved(&r, "T.usesPartialAgain")
    else { return }
    var t = r.table
    #expect(reaches(statement, try t.intern(.isaOfClass(.variable("'a"), ifolTerm)), t))
    let named = uses(user, r.table).filter { $0.hasPrefix("T.BOX_") }
    #expect(named.count == 1)
    #expect(uses(again, r.table).filter { $0.hasPrefix("T.BOX_") } == named)
    #expect(!citations(user, r.table).contains { !$0.types.isEmpty })
    let instance = try #require(r.cited.first { $0.at == [.i, .i] })
    #expect(r.name(of: instance) == nil)
    guard case .proved(let stated, _) = try r.read(instance) else {
        Issue.record("the instance is not proved")
        return
    }
    #expect(roots(citing: try #require(named.first), user, r.table) == [stated])
}

/// Isabelle's citation carries one type per type variable of what it cites (`ZConstp`), and so does `use` — but a
/// theorem
/// read at `i`, cited at `i`, is the unit's statement: cited with none, its root that statement exactly.
@Test
func aCitationAtIOfATheoremReadAtICitesItsStatement() throws {
    var r = try miniReader()
    guard
        let (_, ground) = try proved(&r, "T.usesPoly"),
        let (statement, _) = try proved(&r, "T.polyNamed")
    else { return }
    #expect(citations(ground, r.table) == [
        Citation(cited: .theorem("T.polyNamed"), types: []),
        Citation(cited: .theorem("T.arity"), types: []),
    ])
    #expect(roots(citing: "T.polyNamed", ground, r.table) == [statement])
}

/// A ground theorem whose proof uses a type only inside: Isabelle writes it `dummy`.
@Test
func aHiddenProofTypeIsATypeVariable() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.hidden") else { return }
    #expect(citations(proof, r.table) == [Citation(cited: .theorem("T.vacAx"), types: [.variable("dummy")])])
}

/// The exporter writes a variable only the proof uses as `dummy_pattern` (`standard_hidden_terms`), one per type: the
/// reader binds each at its proof's top, below the closure's letters, in the order the proof first uses them, and each
/// occurrence is a bound variable — at `o` a proposition bound below the top (DESIGN "Step 7").
@Test
func aVariableOnlyTheProofUsesIsBoundAtItsProofsTop() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.hiddenTerm") else { return }
    var t = r.table
    let stated = try t.intern(.ifolAll(.i, body: try t.intern(.isaPropAll(body: try t.intern(.isaBound(2, .o))))))
    let q = try t.intern(.isaBound(0, .o))
    #expect(statement == (try t.intern(.ifolAll(.o, body: try t.intern(.folImplies(stated, q))))))
    let premise = try t.intern(.ifolAll(.i, body: try t.intern(.isaPropAll(body: try t.intern(.isaBound(4, .o))))))
    let atX = try t.intern(.isaAllElim(try t.intern(.hyp(0, premise)), try t.intern(.isaBound(1, .i))))
    let atR = try t.intern(.isaAllElim(atX, try t.intern(.isaPropBound(0))))
    let body = try t.intern(.folImpliesIntro(premise, body: atR))
    let bound = try t.intern(.isaHidden(.i, body: try t.intern(.isaHidden(.o, body: body))))
    #expect(proof == (try t.intern(.isaAllIntro(.o, body: bound))))
}

/// A variable only the proof uses is constant in its arguments: the reader binds one per result type at its proof's
/// top,
/// and reads each application as that variable — `F(λx. P x, Q)`, `g(c)` and `c` the one at `i`, `C(c)` the one at `o`
/// (DESIGN "A variable only the proof uses, constant in its arguments").
@Test
func aVariableOnlyTheProofUsesIsConstantInItsArguments() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.hiddenFunctions") else { return }
    var t = r.table
    var top = proof
    while case .isaAllIntro(_, let body) = t[top] { top = body }
    guard case .isaHidden(.i, let inner) = t[top], case .isaHidden(.o, let body) = t[inner] else {
        Issue.record("not bound at i, then at o: \(t[top])")
        return
    }
    guard
        case .folImpliesIntro(_, let k) = t[body], case .folImpliesIntro(_, let atR) = t[k],
        case .isaAllElim(let atY, let R) = t[atR], case .isaAllElim(let atX, let y) = t[atY],
        case .isaAllElim(_, let x) = t[atX]
    else {
        Issue.record("not H at three instances: \(t[body])")
        return
    }
    let h = try t.intern(.isaBound(1, .i))
    #expect(x == h)
    #expect(y == h)
    #expect(R == (try t.intern(.isaPropBound(0))))
}

/// A cited axiom is typed by what it is: an axiom of the foundation, a definition, or a theory's own axiom — the last
/// no citation but the premise's hypothesis.
@Test
func aCitedAxiomIsTypedByWhatItIs() throws {
    var r = try miniReader()
    guard let (_, notDef) = try proved(&r, "T.useNotDef"), let (_, defax) = try proved(&r, "T.useDef") else { return }
    #expect(citations(notDef, r.table).isEmpty)
    #expect(definitions(notDef, r.table) == [Unfolded(
        axiom: "IFOL.not_def_raw",
        defines: .constant(Defined(.ifol, "IFOL.Not", .object)),
        types: [],
        terms: [],
    )])
    #expect(citations(defax, r.table).isEmpty)
    #expect(try r.reach(of: try theorem(r, "T.useDef")) == Reach(premises: ["T.defax"]))
}

/// `prop_def % Q` is one application, as a rule's is: the definition at its term, concluding `PROP Q ≡ Q`, and no
/// `use`.
@Test
func anAppliedDefinitionIsReadAtItsTerms() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.useProp") else { return }
    var t = r.table
    let q = try t.intern(.isaBound(0, .o))
    let prop = Defined(.pure, "Pure.prop", .meta)
    #expect(definitions(proof, t) == [Unfolded(
        axiom: "Pure.prop_def",
        defines: .constant(prop),
        types: [],
        terms: [q],
    )])
    #expect(uses(proof, t).isEmpty)
    let stated = try t.intern(.folIff(try t.intern(.isaConst(.defined(prop), .fn(.o, .o), args: [q])), q))
    #expect(statement == (try t.intern(.ifolAll(.o, body: stated))))
}

/// `term_class_def`'s left side is `OFCLASS('a, term)`: a citation of it defines the class's membership, never the
/// constant `IFOL.term_class` the constdefs name it by.
@Test
func aCitationOfAClassDefinitionDefinesTheClass() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.useClassDef") else { return }
    #expect(definitions(proof, r.table) == [Unfolded(
        axiom: "IFOL.term_class_def",
        defines: .ofClass(ifolTerm),
        types: [.i],
        terms: [],
    )])
    #expect(uses(proof, r.table).isEmpty)
}

/// `T.anyType`'s `'a` no class restricts: read at its variable. Cited at `[i]`, where it binds no proposition on its
/// spine, it is its proof read at `i`, in place — the target has no type — and no `use` of it stands.
@Test
func aGenericTheoremCitedAtATypeIsItsProofThereInPlace() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.usesAny") else { return }
    var t = r.table
    #expect(uses(proof, t).isEmpty)
    let applied = try t.intern(.isaVarApp(
        head: try t.intern(.isaBound(1, .fn(.i, .o))),
        args: [try t.intern(.isaBound(0, .i))],
    ))
    let identity = try t.intern(.folImpliesIntro(applied, body: try t.intern(.hyp(0, applied))))
    let inPlace = try t.intern(.isaAllIntro(.fn(.i, .o), body: try t.intern(.isaAllIntro(.i, body: identity))))
    #expect(reaches(proof, inPlace, t))
}

/// An axiom of the foundation that the dialect does not list is a gap: the read stops, it refuses nothing.
/// Every instance is determined by its citer: a citation at a type variable the citing proof does not bind is
/// malformed.
@Test
func aCitationAtATypeVariableTheProofDoesNotBindStopsTheRead() throws {
    var r = try miniReader()
    let f = try #require(try failure(&r, "T.unboundType"))
    #expect(f.error as? MalformedExport == .undeclaredTypeVariable("'b"))
}

@Test
func anUnlistedAxiomOfTheFoundationStopsTheRead() throws {
    var r = try miniReader()
    let f = try #require(try failure(&r, "T.useBogus"))
    #expect(f.error as? DialectGap == .axiom("IFOL.bogus"))
}

private func reaches(_ root: NodeID, _ target: NodeID, _ t: Table) -> Bool {
    var seen = Set<NodeID>()
    var work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if n == target { return true }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return false
}

/// The reader's output is the isa dialect (DESIGN §4.3a 4): no kind only fol-zfc has.
@Test
func theReaderEmitsOnlyTheIsaDialect() throws {
    var r = try miniReader()
    var roots = [NodeID]()
    for theorem in r.population {
        if case .proved(let statement, let proof)? = try? r.read(theorem) { roots += [statement, proof] }
    }
    #expect(roots.count == 58)
    var seen = Set<NodeID>()
    var work = roots
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        #expect(Pattern(r.table[n], in: r.table).dialects.contains(.isa), "\(r.table[n])")
        if case .isaFree = r.table[n] { Issue.record("a free variable: \(r.table[n])") }
        r.table[n].forEachChild { c, _ in work.append(c) }
    }
}

@Test
func aClassFactIsProved() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.arity") else { return }
    var t = r.table
    #expect(statement == (try t.intern(.isaOfClass(.i, ifolTerm))))
    #expect(citations(proof, r.table) == [Citation(cited: .theorem("T.termI"), types: [])])
}

@Test
func anOmittedProofAndAnOracleAreRefused() throws {
    var r = try miniReader()
    #expect(try r.read(try theorem(r, "T.nop")) == .refused(.omittedProof))
    #expect(try r.read(try theorem(r, "T.oracle")) == .refused(.oracle("skip_proof")))
}

@Test
func aClassProvedByTheSortAlgebraIsRefused() throws {
    var r = try miniReader()
    #expect(try r.read(try theorem(r, "T.sortAlgebra")) == .refused(.ofclass("IFOL.term")))
}

@Test
func aProofConcludingSomethingElseIsMalformed() throws {
    var r = try miniReader()
    let f = try #require(try failure(&r, "T.wrong"))
    #expect(f.file == "ZF.T/proofs/150")
    guard case .unproved = f.error as? MalformedExport else {
        Issue.record("\(f.error)")
        return
    }
}

@Test
func malformedProofsAreReportedWithTheirPath() throws {
    var r = try miniReader()
    let expected: [(String, any Error & Equatable)] = [
        ("T.freeHyp", MalformedExport.freeHypothesis),
        ("T.unbound", MalformedExport.unboundHypothesis(3)),
        ("T.undeclared", MalformedExport.undeclaredFree("Z")),
        ("T.header", MalformedExport.freesHeader(header: ["A", "a"], occurring: ["a", "A"])),
    ]
    for (name, error) in expected {
        guard let f = try failure(&r, name) else { continue }
        #expect(f.file.hasPrefix("ZF.T/proofs/"))
        #expect("\(f.error)" == "\(error)", "\(name)")
    }
}

@Test
func aTermArgumentToAProofThatIsNotAQuantifierIsAPrincipalConnectiveError() throws {
    var r = try miniReader()
    let f = try #require(try failure(&r, "T.notAll"))
    guard case .principalConnective = f.error as? TableError else {
        Issue.record("\(f.error)")
        return
    }
}
