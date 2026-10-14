import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private let memT = IRType.fn(i, .fn(i, o))
private let free = Pattern.isaFree(i)
private let memAtom = Pattern.isaConst(.primitive(.zf(.mem)), memT, args: [i, i])
private let axiomCited = Pattern.use(.theoryAxiom, [], o)

private struct Owning<R: Rule>: Pass {
    let name: String
    let owned: [Pattern: Owned]
    let rule: R

    func owns(_ p: Pattern) -> Owned? { owned[p] }
    func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        try transform(roots, rule, in: &t)
    }
}

private final class Reading: Pass {
    let name = "reading"
    let owned: [Pattern: Owned]
    var received: [Definition] = []

    init(owned: [Pattern: Owned]) { self.owned = owned }

    func owns(_ p: Pattern) -> Owned? { owned[p] }
    func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] {
        received += definitions
        return roots
    }
}

private struct Named: Request {
    let name: String
}

private func lemma(_ name: String) -> Lemma { Lemma(Named(name: name)) }

private final class Proving: Registry {
    var asked: [String] = []
    let answer: (Lemma, NodeID, inout Table) throws -> Proved

    init(_ answer: @escaping (Lemma, NodeID, inout Table) throws -> Proved) { self.answer = answer }

    func prove(_ lemma: Lemma, _ statement: NodeID, _ definitions: [Definition], in t: inout Table) throws -> Proved {
        asked.append(lemma.name)
        return try answer(lemma, statement, &t)
    }
}

private struct NoMatch: Rule {}

private final class VisitCount: Rule {
    var visits: [NodeID: Int] = [:]
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        visits[id, default: 0] += 1
        return nil
    }
}

private struct Close: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .isaFree = t[id] else { return nil }
        return try t.intern(.folBound(0))
    }
}

private struct Reopen: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .folBound = t[id] else { return nil }
        return try t.intern(.isaFree(.named("a"), i))
    }
}

private struct Elem: Rule {
    func after(_ n: Node, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .isaConst(.primitive(.zf(.mem)), _, xs) = n else { return nil }
        return try t.intern(.folPred("elem", args: xs))
    }
}

private struct ForgetTheProof: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .folImpliesIntro = t[id] else { return nil }
        return try t.intern(.hyp(0, try t.intern(.folBottom)))
    }
}

private struct BottomToC: Rule {
    func before(_ id: NodeID, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case .folBottom = t[id] else { return nil }
        return try t.intern(.isaConst(.declared("C"), o, args: []))
    }
}

/// Every citation of a theory axiom becomes a citation of the lemma of the same name, at the same statement.
private struct CiteLemma: Rule {
    func after(_ n: Node, context depth: Depth, in t: inout Table) throws -> NodeID? {
        guard case let .use(.theoryAxiom(name), [], root) = n else { return nil }
        return try t.intern(.use(.lemma(lemma(name)), [], root))
    }
}

private let close = Owning(name: "close", owned: [free: .rule], rule: Close())
private let elem = Owning(name: "elem", owned: [memAtom: .rule], rule: Elem())
private let cite = Owning(name: "cite", owned: [axiomCited: .rule], rule: CiteLemma())

/// `A → A`, proved by assuming `A`.
private func identity(_ name: String, _ a: NodeID, _ t: inout Table) throws -> Statement {
    let root = try t.intern(.folImplies(a, a))
    let proof = try t.intern(.folImpliesIntro(a, body: try t.intern(.hyp(0, a))))
    return Statement(name: name, root: root, proof: proof)
}

/// `mem(a, a)`, `a` free.
private func memOfA(_ t: inout Table) throws -> NodeID {
    let a = try t.intern(.isaFree(.named("a"), i))
    return try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [a, a]))
}

/// `∀x. mem(x, x) → mem(x, x)`, and its proof.
private func reflexiveMem(_ t: inout Table) throws -> (statement: NodeID, proof: NodeID) {
    let x = try t.intern(.folBound(0))
    let m = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, x]))
    let statement = try t.intern(.folForall(body: try t.intern(.folImplies(m, m))))
    let proof = try t.intern(.folForallIntro(body: try t.intern(.folImpliesIntro(m, body: try t.intern(.hyp(0, m))))))
    return (statement, proof)
}

/// A statement proved by citing the theory axiom `name` at its own statement.
private func citing(_ name: String, _ statementName: String, _ root: NodeID, _ t: inout Table) throws -> Statement {
    Statement(name: statementName, root: root, proof: try t.intern(.use(.theoryAxiom(name), [], root)))
}

private func refusals(_ unit: Unit) -> [String: PipelineRefusal] {
    Dictionary(uniqueKeysWithValues: unit.refused.map { ($0.name, $0.refusal) })
}

/// `close` makes the variables `elem` needs, so the order is the plan's.
@Test func aPipelineRunsItsPassesInOrderOverEveryStatementAndItsProof() throws {
    var t = Table()
    let s = try identity("s", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [s])
    try Pipeline(passes: [close, elem]).run(&unit)
    let b0 = try unit.table.intern(.folBound(0))
    let A = try unit.table.intern(.folPred("elem", args: [b0, b0]))
    #expect(unit.statements.map(\.root) == [try unit.table.intern(.folImplies(A, A))])
    #expect(unit.statements.map(\.proof) == [try unit.table.intern(.folImpliesIntro(A, body: try unit.table.intern(.hyp(0, A))))])
    #expect(unit.refused.isEmpty)
}

@Test func aPatternNoPassOwnsIsRefusedBeforeTheFirstPassNamingEveryOne() throws {
    var t = Table()
    let member = try t.intern(.isaOfClass(i, "IFOL.term"))
    let c = try t.intern(.isaConst(.declared("C"), o, args: []))
    let bad = try identity("bad", try t.intern(.folAnd(member, c)), &t)
    let good = try identity("good", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [bad, good])
    let count = VisitCount()
    try Pipeline(passes: [close, elem, Owning(name: "count", owned: [:], rule: count)]).run(&unit)
    #expect(unit.statements.map(\.name) == ["good"])
    #expect(unit.refused.map(\.name) == ["bad"])
    #expect(unit.refused.map(\.refusal) == [.noOwner([.isaConst(.declared, o, args: []), .isaOfClass(i)])])
    #expect(count.visits[member] == nil)
}

/// A pass that owns a pattern it has no rule for yet is where a statement holding it stops: the passes
/// before it ran, the passes after it never see it.
@Test func aPatternItsPassHasNotBuiltIsRefusedAtThatPass() throws {
    var t = Table()
    let s = try identity("s", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [s])
    let count = VisitCount()
    let unbuilt = Owning(name: "elem", owned: [memAtom: .unbuilt], rule: Elem())
    try Pipeline(passes: [close, unbuilt, Owning(name: "count", owned: [:], rule: count)]).run(&unit)
    #expect(unit.statements.isEmpty)
    #expect(unit.refused.map(\.name) == ["s"])
    #expect(unit.refused.map(\.refusal) == [.unbuilt(pass: "elem", [memAtom])])
    #expect(count.visits.isEmpty)
}

@Test func aPatternThatSurvivesItsOwnPassStopsTheRun() throws {
    var t = Table()
    let s = try identity("s", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [s])
    let idle = Owning(name: "idle", owned: [free: .rule], rule: NoMatch())
    #expect(throws: PipelineError.survived(name: "s", pass: "idle", pattern: free)) {
        try Pipeline(passes: [idle, elem]).run(&unit)
    }
}

@Test func aPatternAnEarlierPassOwnsWrittenBackStopsTheRun() throws {
    var t = Table()
    let s = try identity("s", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [s])
    let reopen = Owning(name: "reopen", owned: [:], rule: Reopen())
    #expect(throws: PipelineError.survived(name: "s", pass: "reopen", pattern: free)) {
        try Pipeline(passes: [close, reopen, elem]).run(&unit)
    }
}

@Test func twoPassesOwningOnePatternStopTheRun() throws {
    var t = Table()
    let s = try identity("s", try memOfA(&t), &t)
    var unit = Unit(table: t, statements: [s])
    let again = Owning(name: "again", owned: [free: .unbuilt], rule: NoMatch())
    #expect(throws: PipelineError.twoOwners(free, passes: ["close", "again"])) {
        try Pipeline(passes: [close, again, elem]).run(&unit)
    }
}

@Test func aPassThatBreaksAProofStopsThePipelineNamingThePassAndTheStatement() throws {
    var t = Table()
    let s = try identity("s", try t.intern(.folBottom), &t)
    var unit = Unit(table: t, statements: [s])
    let bottom = try unit.table.intern(.folBottom)
    let forget = Owning(name: "forget-the-proof", owned: [:], rule: ForgetTheProof())
    #expect(throws: PipelineError.unproved(name: "s", pass: "forget-the-proof", statement: s.root, conclusion: bottom)) {
        try Pipeline(passes: [forget]).run(&unit)
    }
}

/// A pattern no pass owns cannot be removed by any: written by a pass, it reaches the end, which is fol-zfc.
@Test func aPatternNoPassOwnsWrittenByAPassFailsAtTheEnd() throws {
    var t = Table()
    let s = try identity("s", try t.intern(.folBottom), &t)
    var unit = Unit(table: t, statements: [s])
    let c = try unit.table.intern(.isaConst(.declared("C"), o, args: []))
    #expect(throws: IRRefusal.sourceKindSurvived(c)) {
        try Pipeline(passes: [Owning(name: "bottom-to-c", owned: [:], rule: BottomToC())]).run(&unit)
    }
}

/// `A` cites `B`, `B` cites `C`, and `C` stops on a pattern only its proof holds: `B` and `A` hold `C`'s statement
/// alone, so they are lowered, and then fall with it.
@Test func aStatementCitingARefusedOneIsRefusedTransitively() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let r = try t.intern(.folImplies(bottom, bottom))
    let c = try citing("ax", "C", r, &t)
    let b = Statement(name: "B", root: r, proof: try t.intern(.use(.theorem("C"), [], r)))
    let a = Statement(name: "A", root: r, proof: try t.intern(.use(.theorem("B"), [], r)))
    var unit = Unit(table: t, statements: [a, b, c])
    try Pipeline(passes: [Owning(name: "ax", owned: [axiomCited: .unbuilt], rule: NoMatch())]).run(&unit)
    #expect(unit.statements.isEmpty)
    #expect(refusals(unit) == ["C": .unbuilt(pass: "ax", [axiomCited]), "B": .cites("C"), "A": .cites("B")])
}

/// A lemma two statements cite is added once, after the pass that cites it; the registry proves it; `elem`, after the
/// registry, lowers it and both citations alike, so the citations and the lemma stay one node.
@Test func aLemmaTwoStatementsCiteIsAddedOnceAndLoweredWithBothAsOneNode() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let s1 = try citing("L", "S1", r, &t)
    let p = try t.intern(.use(.theoryAxiom("L"), [], r))
    let s2 = Statement(name: "S2", root: try t.intern(.folAnd(r, r)), proof: try t.intern(.folAndIntro(p, p)))
    var unit = Unit(table: t, statements: [s1, s2])
    let registry = Proving { _, _, _ in .proof(proof) }
    try Pipeline(passes: [cite, elem], registry: registry, provingAfter: "cite").run(&unit)
    #expect(registry.asked == ["L"])
    #expect(unit.statements.map(\.name) == ["S1", "S2", "L"])
    let x = try unit.table.intern(.folBound(0))
    let e = try unit.table.intern(.folPred("elem", args: [x, x]))
    let lowered = try unit.table.intern(.folForall(body: try unit.table.intern(.folImplies(e, e))))
    #expect(unit.statements.map(\.root)[2] == lowered)
    #expect(unit.statements[0].proof == (try unit.table.intern(.use(.lemma(lemma("L")), [], lowered))))
    #expect(unit.statements[2].lemma == lemma("L"))
}

@Test func theRegistryProvesEachLemmaAfterItsPassAndTheLemmasItsProofsCite() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let viaL2 = try t.intern(.use(.lemma(lemma("L2")), [], r))
    let s = try citing("L1", "S", r, &t)
    var unit = Unit(table: t, statements: [s])
    let registry = Proving { l, _, _ in .proof(l.name == "L1" ? viaL2 : proof) }
    try Pipeline(passes: [cite, elem], registry: registry, provingAfter: "cite").run(&unit)
    #expect(registry.asked == ["L1", "L2"])
    #expect(unit.statements.map(\.name) == ["S", "L1", "L2"])
    #expect(unit.refused.isEmpty)
}

@Test func aLemmaItsProverHasNotBuiltIsRefusedThereAndItsCitersFall() throws {
    var t = Table()
    let (r, _) = try reflexiveMem(&t)
    let s = try citing("L", "S", r, &t)
    var unit = Unit(table: t, statements: [s])
    try Pipeline(passes: [cite, elem], registry: Proving { _, _, _ in .unbuilt }, provingAfter: "cite").run(&unit)
    #expect(unit.statements.isEmpty)
    #expect(refusals(unit) == ["L": .lemmaUnbuilt, "S": .cites("L")])
}

/// `⋀f::i ⇒ i. f ≡ f`, `f` η-long: `Pure.reflexive` as the reader reads it at `i ⇒ i`.
private func reflexiveAtFunction(_ t: inout Table) throws -> NodeID {
    let T = IRType.fn(i, i)
    let f = try t.intern(.isaAbs(i, body: try t.intern(.isaVarApp(head: try t.intern(.isaBound(1, T)), args: [try t.intern(.isaBound(0, i))]))))
    return try t.intern(.ifolAll(T, body: try t.intern(.isaConst(.primitive(.pure(.eq)), .fn(T, .fn(T, o)), args: [f, f]))))
}

/// `T.d ≡ λx. K(x ∈ x)`: `elem` lowers it before `reading`, which owns `T.d`, reads it; nothing lowers it after.
@Test func aPassReadsTheDefinitionsOfTheConstantsItOwnsAsTheyStandAtItsInput() throws {
    var t = Table()
    let x = try t.intern(.isaBound(0, i))
    let k = { (a: NodeID, t: inout Table) in try t.intern(.isaConst(.declared("K"), .fn(o, i), args: [a])) }
    let m = try t.intern(.isaConst(.primitive(.zf(.mem)), memT, args: [x, x]))
    let definiens = try t.intern(.isaAbs(i, body: try k(m, &t)))
    let reflexive = try reflexiveAtFunction(&t)
    let d = Defined(.zf, "T.d", .object)
    let read = Definition(constant: d, type: .fn(i, i), axiomTypes: [], parameters: 0, definiens: definiens, reflexive: reflexive)
    var unit = Unit(table: t, statements: [], definitions: [read])
    let reading = Reading(owned: [
        .isaConst(.defined(.zf, .object), .fn(i, i), args: [i]): .unbuilt, .isaAbs(i, body: i): .unbuilt,
        .isaConst(.declared, .fn(o, i), args: [o]): .unbuilt, .isaBound(i): .unbuilt,
    ])
    try Pipeline(passes: [elem, reading]).run(&unit)
    let e = try unit.table.intern(.folPred("elem", args: [x, x]))
    var lowered = read
    lowered.definiens = try unit.table.intern(.isaAbs(i, body: try k(e, &unit.table)))
    #expect(reading.received == [lowered])
    #expect(unit.definitions == [lowered])
}

@Test func aCitationOfNoStatementStopsTheRun() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let r = try t.intern(.folImplies(bottom, bottom))
    let s = Statement(name: "S", root: r, proof: try t.intern(.use(.theorem("ghost"), [], r)))
    var unit = Unit(table: t, statements: [s])
    #expect(throws: PipelineError.citesNothing(name: "S", cited: "ghost")) { try Pipeline(passes: []).run(&unit) }
}

@Test func twoStatementsForOneLemmaStopTheRun() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let bottom = try t.intern(.folBottom)
    let other = try t.intern(.folImplies(bottom, bottom))
    let s1 = try citing("L", "S1", r, &t), s2 = try citing("L", "S2", other, &t)
    var unit = Unit(table: t, statements: [s1, s2])
    #expect(throws: PipelineError.citationMismatch("L")) {
        try Pipeline(passes: [cite, elem], registry: Proving { _, _, _ in .proof(proof) }, provingAfter: "cite").run(&unit)
    }
}

@Test func aCycleOfCitationsStopsTheRun() throws {
    var t = Table()
    let bottom = try t.intern(.folBottom)
    let r = try t.intern(.folImplies(bottom, bottom))
    let a = Statement(name: "A", root: r, proof: try t.intern(.use(.theorem("B"), [], r)))
    let b = Statement(name: "B", root: r, proof: try t.intern(.use(.theorem("A"), [], r)))
    var unit = Unit(table: t, statements: [a, b])
    #expect(throws: PipelineError.citationCycle("A")) { try Pipeline(passes: []).run(&unit) }
}

@Test func aLemmaCitedAfterTheRegistryStopsTheRun() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let s = try citing("L", "S", r, &t)
    var late = Unit(table: t, statements: [s]), unregistered = late
    let idle = Owning(name: "idle", owned: [:], rule: NoMatch())
    #expect(throws: PipelineError.citedAfterRegistry("L")) {
        try Pipeline(passes: [idle, cite, elem], registry: Proving { _, _, _ in .proof(proof) }, provingAfter: "idle").run(&late)
    }
    #expect(throws: PipelineError.citedAfterRegistry("L")) { try Pipeline(passes: [cite, elem]).run(&unregistered) }
}

/// The registry proves after `elem`, so a lemma stated with `elem`'s pattern would reach it unlowered.
@Test func aLemmaHoldingAPatternAPassBeforeTheRegistryOwnsStopsTheRun() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let s = try citing("L", "S", r, &t)
    var unit = Unit(table: t, statements: [s])
    #expect(throws: PipelineError.misstatedLemma(name: "L", pattern: memAtom)) {
        try Pipeline(passes: [cite, elem], registry: Proving { _, _, _ in .proof(proof) }, provingAfter: "elem").run(&unit)
    }
}

@Test func aLemmaNamedAsATheoremStopsTheRun() throws {
    var t = Table()
    let (r, proof) = try reflexiveMem(&t)
    let s = try citing("S", "S", r, &t)
    var unit = Unit(table: t, statements: [s])
    #expect(throws: PipelineError.duplicateName("S")) {
        try Pipeline(passes: [cite, elem], registry: Proving { _, _, _ in .proof(proof) }, provingAfter: "cite").run(&unit)
    }
}
