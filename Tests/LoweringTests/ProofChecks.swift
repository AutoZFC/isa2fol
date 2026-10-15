import Foundation
import Testing
import IR
import FolDialect
import Lowering

/// Every `hyp(k, a)` against the assumption it names, shifted by the term binders between: the table computes each step's
/// conclusion but never compares a hypothesis with its binder, so a wrong one would surface only at the kernel.
func misscoped(_ proof: NodeID, in t: Table) throws -> [NodeID] {
    struct Assumed: Hashable { let formula: NodeID; let depth: Int }
    struct Visit: Hashable { let id: NodeID; let assumed: [Assumed]; let depth: Int }
    var wrong: [NodeID] = [], seen: Set<Visit> = []
    func walk(_ id: NodeID, _ assumed: [Assumed], _ depth: Int, _ t: inout Table) throws {
        guard seen.insert(Visit(id: id, assumed: assumed, depth: depth)).inserted else { return }
        switch t[id] {
        case let .hyp(k, a):
            guard k < assumed.count else { wrong.append(id); return }
            let h = assumed[assumed.count - 1 - k]
            if try shift(h.formula, by: depth - h.depth, in: &t) != a { wrong.append(id) }
        case let .folImpliesIntro(a, body), let .folNotIntro(a, body):
            try walk(body, assumed + [Assumed(formula: a, depth: depth)], depth, &t)
        case let .folClassicalAbsurd(a, body):
            try walk(body, assumed + [Assumed(formula: try t.intern(.folNot(a)), depth: depth)], depth, &t)
        case let .isaExElim(_, p, body), let .folExistsElim(p, body):
            try walk(p, assumed, depth, &t)
            guard let c = t.conclusion(of: p) else { wrong.append(id); return }
            switch t[c] {
            case let .ifolEx(_, inner), let .folExists(inner):
                try walk(body, assumed + [Assumed(formula: inner, depth: depth + 1)], depth + 1, &t)
            default: wrong.append(id)
            }
        case let .isaAllIntro(_, body), let .folForallIntro(body):
            try walk(body, assumed, depth + 1, &t)
        case .use:
            return
        default:
            var children: [NodeID] = []
            t[id].forEachChild { c, _ in children.append(c) }
            for c in children where t.conclusion(of: c) != nil { try walk(c, assumed, depth, &t) }
        }
    }
    var table = t
    try walk(proof, [], 0, &table)
    return wrong
}

private let tiers = ["pairs", "witness", "logic", "cong", "s2s3", "primitives", "regroup", "tuples", "classes", "metafun", "inf", "zf"]

/// Each claim, lowered by Fol, rendered and checked by the real checker chained on all of base: Proved, exit 0, stderr
/// empty.
func kernelChecks(_ claims: [(name: String, root: NodeID, proof: NodeID)], definitions: [(Defined, NodeID)] = [],
                  in t: inout Table) throws {
    let ck = ProcessInfo.processInfo.environment["PROOF_CHECKER"]
        ?? NSString(string: "~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker").expandingTildeInPath
    guard FileManager.default.isExecutableFile(atPath: ck) else {
        Issue.record("no proof_checker at \(ck); set PROOF_CHECKER")
        return
    }
    var def = "", proof = "", placed: Set<String> = [], ordered: [(name: String, root: NodeID, proof: NodeID)] = []
    let byName = Dictionary(claims.map { ($0.name, $0) }, uniquingKeysWith: { a, _ in a })
    func place(_ c: (name: String, root: NodeID, proof: NodeID)) {
        guard placed.insert(c.name).inserted else { return }
        var stack = [c.proof], seen: Set<NodeID> = []
        while let id = stack.popLast() {
            guard seen.insert(id).inserted else { continue }
            if case let .use(.lemma(l), _, _) = t[id], let d = byName[l.name] { place(d) }
            t[id].forEachChild { c, _ in stack.append(c) }
        }
        ordered.append(c)
    }
    claims.forEach(place)
    let repo0 = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
    let letters = schemaLetters(from: try baseTexts(repo0.appendingPathComponent("base")))
    for (c, root) in definitions {
        let lowered = try Fol().run([root], [], in: &t)[0]
        def += try render(Declaration(kind: .definition(predicate: c.name), name: c.definitionName, root: lowered), in: t) + "\n"
    }
    for c in ordered {
        let lowered = try Fol().run([c.root, c.proof], [], in: &t)
        let claim = Declaration(kind: .claim, name: c.name, root: lowered[0])
        def += try render(claim, in: t) + "\n"
        proof += try render(proof: lowered[1], of: claim, in: t, letters: letters) + "\n"
    }
    let repo = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
    let dir = URL(fileURLWithPath: NSTemporaryDirectory()).appendingPathComponent("isa2fol-kernel-\(getpid())-\(claims[0].name)")
    try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: dir) }
    let defURL = dir.appendingPathComponent("u.fol.def"), prfURL = dir.appendingPathComponent("u.fol.proof")
    try def.write(to: defURL, atomically: true, encoding: .utf8)
    try proof.write(to: prfURL, atomically: true, encoding: .utf8)
    let base = repo.appendingPathComponent("base")
    let units = [base.appendingPathComponent("axioms")] + tiers.map { base.appendingPathComponent("tiers/\($0)") }
    let proc = Process()
    proc.executableURL = URL(fileURLWithPath: ck)
    proc.arguments = [defURL.path, prfURL.path] + units.map { $0.path + ".fol.def" } + ["--"] + units.map { $0.path + ".fol.proof" }
    proc.environment = ["PROOF_CHECKER_MAX_WARNINGS": "100000"]
    let out = Pipe(), err = Pipe()
    proc.standardOutput = out
    proc.standardError = err
    try proc.run()
    let stdout = String(decoding: out.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let stderr = String(decoding: err.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    proc.waitUntilExit()
    #expect(proc.terminationStatus == 0, "checker rejected:\n\(stdout.suffix(3000))\(stderr.prefix(3000))")
    #expect(stderr.isEmpty, "stderr must be empty: \(stderr.prefix(3000))")
    let proved = stdout.components(separatedBy: "Proved (").dropFirst().first ?? ""
    let section = proved.components(separatedBy: "\n\n").first ?? proved
    for c in claims { #expect(section.contains(" \(c.name)\n") || section.hasSuffix(" \(c.name)"), "\(c.name) not Proved:\n\(stdout.suffix(2000))") }
}
