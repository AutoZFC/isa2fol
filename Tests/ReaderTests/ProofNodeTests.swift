import Testing
import YXML
@testable import Reader

private func decode(_ s: String) throws -> (Decode, ProofNode) {
    var f = Forest()
    let body = try f.parse(Array(s.utf8))
    let d = Decode(forest: f)
    return (d, try d.proofNode(body))
}

private let iT = IsaType.type("ZF_Base.i", [])

@Test func everyProofConstructorDecodes() throws {
    guard case .head(.nop) = try decode(pnop).1 else { Issue.record("nop"); return }
    guard case .head(.bound(3)) = try decode(pbound(3)).1 else { Issue.record("bound"); return }
    guard case let .head(.termAbstraction(T, _)) = try decode(pabst("x", i, pnop)).1, T == iT else { Issue.record("abst"); return }
    guard case .head(.hypothesisAbstraction) = try decode(pabsp("H", trueprop(const("IFOL.False")), pnop)).1 else { Issue.record("absp"); return }
    guard case .application(_, .term) = try decode(pappt(pnop, free("a"))).1 else { Issue.record("appt"); return }
    guard case .application(_, .proof) = try decode(pappp(pnop, pnop)).1 else { Issue.record("appp"); return }
    guard case .head(.hypothesis) = try decode(phyp(trueprop(const("IFOL.False")))).1 else { Issue.record("hyp"); return }
    guard case let .head(.axiom(name, types)) = try decode(paxiom("Pure.reflexive", i)).1, name == "Pure.reflexive", types == [iT] else {
        Issue.record("axiom"); return
    }
    guard case let .head(.ofclass(T, c)) = try decode(pofclass(i, "IFOL.term")).1, T == iT, c == "IFOL.term" else { Issue.record("ofclass"); return }
    guard case let .head(.oracle(name, _)) = try decode(poracle("skip_proof")).1, name == "skip_proof" else { Issue.record("oracle"); return }
    guard case let .head(.theorem(c)) = try decode(pcite(222, "IFOL", "IFOL.refl", i)).1 else { Issue.record("theorem"); return }
    #expect(c == Citation(theory: "IFOL", serial: 222, name: "IFOL.refl", index: 0, types: [iT]))
}

@Test func aCitationWithoutItsFourAtomsIsMalformed() {
    #expect(throws: MalformedExport.atoms(["222", "IFOL"])) { try decode(tagged(10, ["222", "IFOL"], [])) }
}

@Test func aProofSpineFlattensToItsHeadAndArgumentsInOrder() throws {
    var f = Forest()
    let body = try f.parse(Array(pappp(pappt(pcite(1, "T"), free("a")), pnop, pbound(0)).utf8))
    let spine = try Decode(forest: f).proofSpine(body)
    guard case .theorem = spine.node else { Issue.record("head"); return }
    #expect(spine.arguments.map { if case .term = $0 { "t" } else { "p" } } == ["t", "p", "p"])
}
