import Foundation
import Testing
@testable import FolDialect

private func v(_ n: String) -> Term { Term(n) }
private func p(_ n: String, _ a: String...) -> Formula {
    .predicate(n, args: a.map(Term.init), isSchema: false)
}

@Test func aGuardedForallRendersAsAnImplication() {
    let f = Formula.quantified(.forAll, .setVar, "x",
        body: .binary(.implies, p("set", "x"), p("elem", "x", "y")))
    #expect(render(f) == "forall x. (set(x) -> elem(x, y))")
}

@Test func aClassBinderCarriesNoGuard() {
    let f = Formula.quantified(.forAll, .classVar, "A", body: p("elem", "x", "A"))
    #expect(render(f) == "forall A. elem(x, A)")
    #expect(!render(f).contains("set(A)"), "guarding a class makes the claim FALSE")
}

/// ⚠ THE CHECKER'S GRAMMAR IS THE ONLY AUTHORITY. This is the test that keeps
/// `render` honest; anything else only checks our own reading of it.
@Test func theRealCheckerAcceptsWhatRenderEmits() throws {
    let ck = ProcessInfo.processInfo.environment["PROOF_CHECKER"]
        ?? NSString(string: "~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker")
            .expandingTildeInPath
    guard FileManager.default.isExecutableFile(atPath: ck) else {
        Issue.record("no proof_checker at \(ck); set PROOF_CHECKER")
        return
    }
    let members = Declaration.axiom("members_are_sets",
        .quantified(.forAll, .setVar, "x",
            body: .quantified(.forAll, .setVar, "y",
                body: .binary(.implies, p("elem", "x", "y"), p("set", "x")))))
    let goal = Declaration.claim("probe", members.statement)

    let dir = URL(fileURLWithPath: NSTemporaryDirectory())
        .appendingPathComponent("isa2fol-render-\(getpid())")
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: dir) }
    let def = dir.appendingPathComponent("p.fol.def")
    let prf = dir.appendingPathComponent("p.fol.proof")
    try "\(render(members))\n\n\(render(goal))\n".write(to: def, atomically: true, encoding: .utf8)
    try "proof probe:\n    _a = use members_are_sets\n    qed _a\n"
        .write(to: prf, atomically: true, encoding: .utf8)

    let proc = Process()
    proc.executableURL = URL(fileURLWithPath: ck)
    proc.arguments = [def.path, prf.path]
    let out = Pipe(), err = Pipe()
    proc.standardOutput = out
    proc.standardError = err
    try proc.run()
    let stdout = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let stderr = String(decoding: err.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    proc.waitUntilExit()

    #expect(proc.terminationStatus == 0, "checker rejected our syntax:\n\(stdout)\(stderr)")
    #expect(stderr.isEmpty, "stderr must be empty: \(stderr)")
    #expect(stdout.contains("+ probe"), "the claim did not prove:\n\(stdout)")
}
