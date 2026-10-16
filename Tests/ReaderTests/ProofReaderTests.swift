import Foundation
import IR
import Testing
import YXML
@testable import Reader

private let P = trueprop(free("P")), Q = trueprop(free("Q"))
private func mem(_ a: String, _ b: String) -> String { trueprop(app(const("ZF_Base.mem"), a, b)) }
private func eq(_ T: String, _ a: String) -> String { trueprop(app(const("IFOL.eq", T), a, a)) }
private func imp(_ a: String, _ b: String) -> String { app(const("Pure.imp"), a, b) }
private func all(_ x: String, _ T: String, _ body: String) -> String { app(const("Pure.all", T), lam(x, T, body)) }
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
///   T.reflAx     axiom OFCLASS('a, term) ⟹ ⋀a. a = a, a theory's own: cited, never read as a step
///   T.termI      axiom OFCLASS(i, term)
///   T.arity      OFCLASS(i, term)          T.termI           as arity_term_i
///   box 95       OFCLASS(i, term)          T.arity           as box 1792: how a proof discharges at i
///   T.axiom      b = b                     reflAx[i] %% box95 % b
///   box 80       OFCLASS('a, term) ⟹ x = x   λH. reflAx['a] %% H % x
///   T.poly       c = c                     box80[i] % c %% box95     terms first: the ∀-closure is outermost
///   T.polyNamed  OFCLASS('a, term) ⟹ y = y   as box 80, read at i: every type variable restricted to term; cited by T.usesPoly at i
///   T.polyPartial  OFCLASS('a, term) ⟹ (⋀h::'b. Q) ⟹ (⋀h::'b. Q)   'b unrestricted: read as stated; cited by T.usesPartial at i, i
///   T.defax      axiom with a typed free: A ∈ A;   T.useDef  a ∈ a   T.defax % a
///   T.vacAx      axiom (⋀h::'a. Q) ⟹ Q;          T.hidden  Q ⟹ Q   λH. vacAx[dummy] % Q %% (⋀h::dummy. H)
///   T.hiddenTerm (⋀x::i. Q) ⟹ Q                λH. H % dummy_pattern::i   a variable only the proof uses
///   IFOL.not_def_raw  a definition;  T.useNotDef cites it.   IFOL.bogus  an unlisted IFOL axiom;  T.useBogus cites it
///   T.sortAlgebra  OFCLASS(i, term) by ZClassp — 0 in the export, refused
///   T.nop, T.oracle, T.wrong, T.freeHyp, T.unbound, T.notAll, T.undeclared, T.header
private let notDef = app(const("Pure.eq", fn(o, o)), const("IFOL.Not"),
                         lam("P", o, app(const("IFOL.imp"), bound(0), const("IFOL.False"))))

private func miniReader() throws -> Reader {
    var files: [String: String] = [
        "IFOL/theory/axioms": axiomEntity("IFOL.not_def_raw", prop: notDef) + axiomEntity("IFOL.bogus", prop: falsum),
        "ZF.T/theory/axioms": axiomEntity("T.defax", frees: [("A", i)], prop: mem(tagged(1, ["A"], [i]), tagged(1, ["A"], [i])))
            + axiomEntity("T.vacAx", tfrees: ["'a"], frees: [("Q", o)], prop: imp(all("h", typeA, Q), Q))
            + axiomEntity("T.termI", prop: termClass(i))
            + axiomEntity("T.reflAx", tfrees: ["'a"], prop: imp(termClass(typeA), all("a", typeA, eq(typeA, bound(0))))),
    ]
    let theorems: [(String?, Int, String)] = [
        ("T.imp", 10, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        ("T.fix", 20, proofFile(frees: [("A", i)], prop: all("x", i, imp(mem(bound(0), free("A")), mem(bound(0), free("A")))),
                                proof: pabst("x", i, pabsp("H", mem(bound(0), free("A")), pbound(0))))),
        ("T.outer", 30, proofFile(frees: [("Q", o)], prop: imp(Q, all("x", i, Q)), proof: pabsp("H", Q, pabst("x", i, pbound(0))))),
        ("T.cite", 40, proofFile(frees: [("a", i), ("A", i)], prop: imp(mem(free("a"), free("A")), mem(free("a"), free("A"))),
                                 proof: pappt(pappt(pcite(20, "ZF.T", "T.fix"), free("A")), free("a")))),
        (nil, 50, proofFile(frees: [("x", i), ("B", i)], prop: imp(mem(free("x"), free("B")), mem(free("x"), free("B"))),
                            proof: pabsp("H", mem(free("x"), free("B")), pbound(0)))),
        ("T.inline", 60, proofFile(frees: [("a", i), ("A", i)], prop: imp(mem(free("a"), free("A")), mem(free("a"), free("A"))),
                                   proof: pappt(pappt(pcite(50, "ZF.T"), free("a")), free("A")))),
        ("T.axiom", 70, proofFile(frees: [("b", i)], prop: eq(i, free("b")),
                                  proof: pappt(pappp(paxiom("T.reflAx", i), pcite(95, "ZF.T")), free("b")))),
        (nil, 80, proofFile(tfrees: ["'a"], frees: [("x", typeA)], prop: imp(termClass(typeA), eq(typeA, free("x"))),
                            proof: pabsp("H", termClass(typeA), pappt(pappp(paxiom("T.reflAx", typeA), pbound(0)), free("x"))))),
        (nil, 95, proofFile(frees: [], prop: termClass(i), proof: pcite(120, "ZF.T", "T.arity"))),
        ("T.poly", 90, proofFile(frees: [("c", i)], prop: eq(i, free("c")),
                                 proof: pappp(pappt(pcite(80, "ZF.T", "", i), free("c")), pcite(95, "ZF.T")))),
        ("T.polyNamed", 100, proofFile(tfrees: ["'a"], frees: [("y", typeA)], prop: imp(termClass(typeA), eq(typeA, free("y"))),
                                       proof: pabsp("H", termClass(typeA), pappt(pappp(paxiom("T.reflAx", typeA), pbound(0)), free("y"))))),
        ("T.usesPoly", 110, proofFile(frees: [("d", i)], prop: eq(i, free("d")),
                                      proof: pappp(pappt(pcite(100, "ZF.T", "T.polyNamed", i), free("d")), pcite(95, "ZF.T")))),
        ("T.arity", 120, proofFile(frees: [], prop: termClass(i), proof: paxiom("T.termI"))),
        ("T.useDef", 125, proofFile(frees: [("a", i)], prop: mem(free("a"), free("a")), proof: pappt(paxiom("T.defax"), free("a")))),
        ("T.hidden", 127, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pabsp("H", Q,
            pappp(pappt(paxiom("T.vacAx", dummy), free("Q")), pabst("h", dummy, pbound(0)))))),
        ("T.hiddenTerm", 128, proofFile(frees: [("Q", o)], prop: imp(all("x", i, Q), Q),
            proof: pabsp("H", all("x", i, Q), pappt(pbound(0), const("Pure.dummy_pattern", i))))),
        ("T.useNotDef", 129, proofFile(frees: [], prop: notDef, proof: paxiom("IFOL.not_def_raw"))),
        ("T.useBogus", 131, proofFile(frees: [], prop: falsum, proof: paxiom("IFOL.bogus"))),
        ("T.unboundType", 132, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pabsp("H", Q,
            pappp(pappt(paxiom("T.vacAx", tfree("'b")), free("Q")), pabst("h", tfree("'b"), pbound(0)))))),
        ("T.nop", 130, proofFile(frees: [], prop: falsum, proof: pnop)),
        ("T.oracle", 140, proofFile(frees: [], prop: falsum, proof: poracle("skip_proof"))),
        ("T.wrong", 150, proofFile(frees: [("Q", o), ("P", o)], prop: imp(Q, P), proof: pabsp("H", Q, pbound(0)))),
        ("T.freeHyp", 160, proofFile(frees: [], prop: falsum, proof: phyp(falsum))),
        ("T.sortAlgebra", 170, proofFile(frees: [], prop: termClass(i), proof: pofclass(i, "IFOL.term"))),
        ("T.unbound", 180, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(3)))),
        ("T.notAll", 190, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pappt(pabsp("H", P, pbound(0)), free("P")))),
        ("T.undeclared", 200, proofFile(frees: [("P", o)], prop: imp(P, P),
                                        proof: pappt(pabst("x", o, pabsp("H", trueprop(bound(0)), pbound(0))), free("Z")))),
        ("T.header", 210, proofFile(frees: [("A", i), ("a", i)], prop: mem(free("a"), free("A")), proof: pnop)),
        ("T.simps(2)", 220, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        (nil, 250, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        (nil, 255, proofFile(frees: [("P", o)], prop: imp(P, P), proof: pabsp("H", P, pbound(0)))),
        ("T.viaBox", 260, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pappt(pcite(250, "ZF.T"), free("Q")))),
        ("T.viaTwin", 265, proofFile(frees: [("Q", o)], prop: imp(Q, Q), proof: pappt(pcite(255, "ZF.T"), free("Q")))),
        ("T.boundPremise", 270, proofFile(frees: [("Q", o)], prop: imp(all("P", o, imp(trueprop(bound(0)), trueprop(bound(0)))), imp(Q, Q)),
                                          proof: pabsp("H", all("P", o, imp(trueprop(bound(0)), trueprop(bound(0)))),
                                                       pabsp("q", Q, pappp(pappt(pbound(1), free("Q")), pbound(0)))))),
        ("T.introProp", 275, proofFile(frees: [("Q", o)], prop: imp(Q, Q),
                                       proof: pappt(pabst("P", o, pabsp("h", trueprop(bound(0)), pbound(0))), free("Q")))),
        ("T.polyPartial", 230, proofFile(tfrees: ["'a", "'b"], frees: [("Q", o)],
                                         prop: imp(termClass(typeA), imp(all("h", typeB, Q), all("h", typeB, Q))),
                                         proof: pabsp("C", termClass(typeA), pabsp("H", all("h", typeB, Q), pbound(0))))),
        ("T.usesPartial", 240, proofFile(frees: [("Q", o)], prop: imp(all("h", i, Q), all("h", i, Q)),
                                         proof: pappp(pappt(pcite(230, "ZF.T", "T.polyPartial", i, i), free("Q")), pcite(95, "ZF.T")))),
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
    guard case let .proved(statement, proof) = outcome else {
        Issue.record("\(name): \(outcome)")
        return nil
    }
    return (statement, proof)
}

private func uses(_ root: NodeID, _ t: Table) -> Set<String> {
    var seen: Set<NodeID> = [], names: Set<String> = [], work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case let .use(cited, _, _) = t[n] { names.insert(cited.name) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return names
}

private struct Citation: Hashable {
    let cited: Cited
    let types: [IRType]
}

private func citations(_ root: NodeID, _ t: Table) -> Set<Citation> {
    var seen: Set<NodeID> = [], found: Set<Citation> = [], work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case let .use(cited, types, _) = t[n] { found.insert(Citation(cited: cited, types: types)) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private func roots(citing name: String, _ root: NodeID, _ t: Table) -> Set<NodeID> {
    var seen: Set<NodeID> = [], found: Set<NodeID> = [], work = [root]
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        if case let .use(.theorem(cited), _, stated) = t[n], cited == name { found.insert(stated) }
        t[n].forEachChild { c, _ in work.append(c) }
    }
    return found
}

private let reflAx = Cited.theoryAxiom("T.reflAx")

private func failure(_ r: inout Reader, _ name: String) throws -> ReadFailure? {
    do {
        let outcome = try r.read(try theorem(r, name))
        Issue.record("\(name) read as \(outcome)")
    } catch let f as ReadFailure {
        return f
    }
    return nil
}

@Test func aHypothesisIsItsBindersFormula() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.imp") else { return }
    var t = r.table
    let P = try t.intern(.isaBound(0, .o))
    #expect(proof == (try t.intern(.isaAllIntro(.o, body: try t.intern(.folImpliesIntro(P, body: try t.intern(.hyp(0, P))))))))
}

/// The hypothesis `Q` is read where it is assumed; used under `⋀x` it is one binder further out.
@Test func aHypothesisUsedUnderATermBinderIsShifted() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.outer") else { return }
    var t = r.table
    let used = try t.intern(.isaAllIntro(.i, body: try t.intern(.hyp(0, try t.intern(.isaBound(1, .o))))))
    let expected = try t.intern(.isaAllIntro(.o, body: try t.intern(.folImpliesIntro(try t.intern(.isaBound(0, .o)), body: used))))
    #expect(proof == expected)
}

@Test func aTermBinderIsAnIsaQuantifierStep() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.fix") else { return }
    guard case let .isaAllIntro(.i, inner) = r.table[proof], case .isaAllIntro(.i, _) = r.table[inner] else {
        Issue.record("\(r.table[proof])")
        return
    }
}

@Test func aNamedCitationIsAUseInstantiatedByItsTermArguments() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.cite") else { return }
    #expect(uses(proof, r.table) == ["T.fix"])
    #expect(r.cited.map { r.name(of: $0) } == ["T.fix"])
}

/// A statement enters the pipeline under the name its citations use: an index `(2)` is spelled
/// `.2` (CLAUDE.md rule 5).
@Test func aTheoremsClaimNameIsTheNameItsCitationsUse() throws {
    var r = try miniReader()
    #expect(try claimName(try #require(r.name(of: try theorem(r, "T.simps(2)")))) == "T.simps.2")
    let fix = try claimName(try #require(r.name(of: try theorem(r, "T.fix"))))
    guard let (_, proof) = try proved(&r, "T.cite") else { return }
    #expect(uses(proof, r.table) == [fix])
}

@Test func anUnnamedBoxIsInlined() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.inline") else { return }
    #expect(uses(proof, r.table).isEmpty)
    #expect(r.cited.isEmpty)
}

/// A `⋀` Isabelle writes over a proposition — `Pure.all` in a formula, `ZAbst` in a proof — is Pure's `⋀`, its own nodes
/// and its own variable; a free proposition, which the reader closes over, stays the schema letter's `ifolAll` at `o`.
@Test func pureAllOverAPropositionIsItsOwnNodeAndAFreeOneTheLetter() throws {
    var r = try miniReader()
    guard let (statement, _) = try proved(&r, "T.boundPremise"), let (_, intro) = try proved(&r, "T.introProp") else { return }
    var t = r.table
    let P = try t.intern(.isaPropBound(0)), Q = try t.intern(.isaBound(0, .o))
    let bound = try t.intern(.isaPropAll(body: try t.intern(.folImplies(P, P))))
    #expect(statement == (try t.intern(.ifolAll(.o, body: try t.intern(.folImplies(bound, try t.intern(.folImplies(Q, Q))))))))
    let inner = try t.intern(.isaPropIntro(body: try t.intern(.folImpliesIntro(P, body: try t.intern(.hyp(0, P))))))
    #expect(intro == (try t.intern(.isaAllIntro(.o, body: try t.intern(.isaAllElim(inner, Q))))))
}

/// Box 250 binds the proposition `P`: a statement, cited by the name of its proof's content — `T.imp`'s proof, the same
/// node — and box 255, the same box at another serial, by the same name: a serial names a box only within one build.
@Test func aBoxBindingAPropositionIsCitedByItsContentsName() throws {
    var r = try miniReader()
    guard let (statement, own) = try proved(&r, "T.imp"), let (_, proof) = try proved(&r, "T.viaBox"),
          let (_, twin) = try proved(&r, "T.viaTwin") else { return }
    let name = "T.BOX_" + fingerprint(own, r.table)
    #expect(uses(proof, r.table) == [name])
    #expect(uses(twin, r.table) == [name])
    #expect(roots(citing: name, proof, r.table) == [statement])
    #expect(r.cited.map { r.name(of: $0) } == [nil])
}

/// `T.reflAx`'s class premise is discharged by an ordinary ⟹-elim, with box 95's inlined proof.
@Test func aClassDischargeIsAnOrdinaryPremise() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.axiom") else { return }
    #expect(citations(proof, r.table) == [Citation(cited: reflAx, types: [.i]), Citation(cited: .theorem("T.arity"), types: [])])
}

@Test func anAxiomsFreesCloseLikeATheoremsAndItsTypedVariablesAgree() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.useDef") else { return }
    #expect(uses(proof, r.table) == ["T.defax"])
}

/// Box 80 binds its class hypothesis and discharges `T.reflAx`'s class premise with it: both bookkeeping.
@Test func aPolymorphicBoxIsInlinedAtTheInstanceItIsCitedAt() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.poly") else { return }
    #expect(citations(proof, r.table) == [Citation(cited: reflAx, types: [.i]), Citation(cited: .theorem("T.arity"), types: [])])
}

/// Every type variable of `T.polyNamed` carries `OFCLASS(α, term)`, and `i` is the only type in `term`: it is read at `i`,
/// its proof with it.
@Test func aTheoremRestrictedToTermIsReadAtI() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.polyNamed") else { return }
    var t = r.table
    let y = try t.intern(.isaBound(0, .i))
    let member = try t.intern(.isaOfClass(.i, "IFOL.term"))
    let eq = try t.intern(.isaConst(.primitive(.ifol(.eq)), .fn(.i, .fn(.i, .o)), args: [y, y]))
    #expect(statement == (try t.intern(.ifolAll(.i, body: try t.intern(.folImplies(member, eq))))))
    #expect(citations(proof, r.table) == [Citation(cited: reflAx, types: [.i])])
}

/// `T.polyPartial`'s `'b` carries no class: it is read at its variables, and a citation of it keeps its types.
@Test func aTheoremWithATypeVariableNotRestrictedToTermIsReadAsStated() throws {
    var r = try miniReader()
    guard let (statement, _) = try proved(&r, "T.polyPartial"), let (_, user) = try proved(&r, "T.usesPartial") else { return }
    var t = r.table
    #expect(reaches(statement, try t.intern(.isaOfClass(.variable("'a"), "IFOL.term")), t))
    #expect(citations(user, r.table) == [Citation(cited: .theorem("T.polyPartial"), types: [.i, .i]),
                                         Citation(cited: .theorem("T.arity"), types: [])])
}

/// Isabelle's citation carries one type per type variable of what it cites (`ZConstp`), and so does `use` — but a theorem
/// read at `i`, cited at `i`, is the unit's statement: cited with none, its root that statement exactly.
@Test func aCitationAtIOfATheoremReadAtICitesItsStatement() throws {
    var r = try miniReader()
    guard let (_, ground) = try proved(&r, "T.usesPoly"), let (statement, _) = try proved(&r, "T.polyNamed") else { return }
    #expect(citations(ground, r.table) == [Citation(cited: .theorem("T.polyNamed"), types: []), Citation(cited: .theorem("T.arity"), types: [])])
    #expect(roots(citing: "T.polyNamed", ground, r.table) == [statement])
}

/// A ground theorem whose proof uses a type only inside: Isabelle writes it `dummy`.
@Test func aHiddenProofTypeIsATypeVariable() throws {
    var r = try miniReader()
    guard let (_, proof) = try proved(&r, "T.hidden") else { return }
    #expect(citations(proof, r.table) == [Citation(cited: .theoryAxiom("T.vacAx"), types: [.variable("dummy")])])
}

/// The exporter writes the variable only the proof uses as `dummy_pattern` (`standard_hidden_terms`): it reads as the
/// hidden variable, inside the proof and never in its statement.
@Test func aVariableOnlyTheProofUsesIsTheHiddenVariable() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.hiddenTerm") else { return }
    var t = r.table
    let hidden = try t.intern(.isaFree(.hidden, .i))
    #expect(!reaches(statement, hidden, t))
    #expect(reaches(proof, hidden, t))
}

/// A cited axiom is typed by what it is: an axiom of the foundation, a definition, or a theory's own axiom.
@Test func aCitedAxiomIsTypedByWhatItIs() throws {
    var r = try miniReader()
    guard let (_, notDef) = try proved(&r, "T.useNotDef"), let (_, defax) = try proved(&r, "T.useDef") else { return }
    #expect(citations(notDef, r.table) == [Citation(cited: .isaDefinition("IFOL.not_def_raw", of: Defined(.ifol, "IFOL.Not", .object)), types: [])])
    #expect(citations(defax, r.table) == [Citation(cited: .theoryAxiom("T.defax"), types: [])])
}

/// An axiom of the foundation that the dialect does not list is a gap: the read stops, it refuses nothing.
/// Every instance is determined by its citer: a citation at a type variable the citing proof does not bind is malformed.
@Test func aCitationAtATypeVariableTheProofDoesNotBindStopsTheRead() throws {
    var r = try miniReader()
    guard let f = try failure(&r, "T.unboundType") else { return }
    #expect(f.error as? MalformedExport == .undeclaredTypeVariable("'b"))
}

@Test func anUnlistedAxiomOfTheFoundationStopsTheRead() throws {
    var r = try miniReader()
    guard let f = try failure(&r, "T.useBogus") else { return }
    #expect(f.error as? DialectGap == .axiom("IFOL.bogus"))
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

/// The reader's output is the isa dialect (DESIGN §4.3a 4): no kind only fol-zfc has.
@Test func theReaderEmitsOnlyTheIsaDialect() throws {
    var r = try miniReader()
    var roots: [NodeID] = []
    for theorem in r.population {
        if case let .proved(statement, proof)? = try? r.read(theorem) { roots += [statement, proof] }
    }
    #expect(roots.count == 42)
    var seen: Set<NodeID> = [], work = roots
    while let n = work.popLast() {
        guard seen.insert(n).inserted else { continue }
        #expect(Pattern(r.table[n], in: r.table).dialects.contains(.isa), "\(r.table[n])")
        r.table[n].forEachChild { c, _ in work.append(c) }
    }
}

@Test func aClassFactIsProved() throws {
    var r = try miniReader()
    guard let (statement, proof) = try proved(&r, "T.arity") else { return }
    var t = r.table
    #expect(statement == (try t.intern(.isaOfClass(.i, "IFOL.term"))))
    #expect(citations(proof, r.table) == [Citation(cited: .theoryAxiom("T.termI"), types: [])])
}

@Test func anOmittedProofAndAnOracleAreRefused() throws {
    var r = try miniReader()
    #expect(try r.read(try theorem(r, "T.nop")) == .refused(.omittedProof))
    #expect(try r.read(try theorem(r, "T.oracle")) == .refused(.oracle("skip_proof")))
}

@Test func aClassProvedByTheSortAlgebraIsRefused() throws {
    var r = try miniReader()
    #expect(try r.read(try theorem(r, "T.sortAlgebra")) == .refused(.ofclass("IFOL.term")))
}

@Test func aProofConcludingSomethingElseIsMalformed() throws {
    var r = try miniReader()
    guard let f = try failure(&r, "T.wrong") else { return }
    #expect(f.file == "ZF.T/proofs/150")
    guard case .unproved = f.error as? MalformedExport else {
        Issue.record("\(f.error)")
        return
    }
}

@Test func malformedProofsAreReportedWithTheirPath() throws {
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

@Test func aTermArgumentToAProofThatIsNotAQuantifierIsAPrincipalConnectiveError() throws {
    var r = try miniReader()
    guard let f = try failure(&r, "T.notAll") else { return }
    guard case .principalConnective = f.error as? TableError else {
        Issue.record("\(f.error)")
        return
    }
}
