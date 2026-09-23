import Foundation
import Testing
@testable import YXML

private let X = "\u{05}"
private let Y = "\u{06}"

private func bytes(_ s: String) -> [UInt8] { Array(s.utf8) }

@Test func anElementCarriesItsTagAndAttributes() throws {
    let n = try parse(bytes("\(X)\(Y)0\(Y)0=ZF_Base.mem\(X)\(X)\(Y)\(X)"))
    let e = n.elements
    #expect(e.count == 1)
    #expect(e[0].tag == "0")
    #expect(e[0].attribute("0") == "ZF_Base.mem")
    #expect(e[0].attribute("absent") == "")
}

@Test func textBetweenMarkupSurvives() throws {
    let n = try parse(bytes("\(X)\(Y)3\(X)17\(X)\(Y)\(X)"))
    #expect(n.elements[0].allText == "17")
}

@Test func anUnbalancedCloseIsAnError() {
    #expect(throws: YXMLError.unbalancedClose) {
        _ = try parse(bytes("\(X)\(Y)\(X)"))
    }
}

/// The parser is only right if it reads what Isabelle actually wrote.
@Test func aRealExportFileParses() throws {
    let root = "data/zf_export/Pure/theory/axioms"
    guard FileManager.default.fileExists(atPath: root) else {
        Issue.record("export missing at \(root) — run from the repo root")
        return
    }
    let n = try parse(contentsOf: root)
    let entities = n.children.filter { $0.tag == "entity" }
    #expect(entities.count >= 11, "Pure declares 11 axioms")
    let names = Set(entities.map { $0.attribute("name") })
    #expect(names.contains("Pure.reflexive"))
    #expect(names.contains("Pure.conjunction_def"))
    #expect(entities.first { $0.attribute("name") == "Pure.reflexive" }?
        .attribute("file") == "theory.ML")
}
