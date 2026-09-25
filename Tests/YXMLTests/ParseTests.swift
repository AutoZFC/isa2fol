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
    #expect(try e[0].attribute("0") == "ZF_Base.mem")
}

@Test func aMissingAttributeIsAnErrorNotEmpty() throws {
    let e = try parse(bytes("\(X)\(Y)0\(Y)0=ZF_Base.mem\(X)\(X)\(Y)\(X)")).elements[0]
    #expect(throws: YXMLError.missingAttribute(tag: "0", name: "absent")) { try e.attribute("absent") }
    #expect(e.attributes["absent"] == nil)
}

@Test func anEmptyAttributeValueIsPresent() throws {
    let e = try parse(bytes("\(X)\(Y)0\(Y)k=\(X)\(X)\(Y)\(X)")).elements[0]
    #expect(try e.attribute("k") == "")
}

@Test func anAttributeFieldWithoutEqualsIsAnError() {
    #expect(throws: YXMLError.malformedAttribute(tag: "0", field: "junk")) {
        _ = try parse(bytes("\(X)\(Y)0\(Y)junk\(X)\(X)\(Y)\(X)"))
    }
}

@Test func aDuplicateAttributeIsAnError() {
    #expect(throws: YXMLError.duplicateAttribute(tag: "0", name: "k")) {
        _ = try parse(bytes("\(X)\(Y)0\(Y)k=a\(Y)k=b\(X)\(X)\(Y)\(X)"))
    }
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
    let names = Set(try entities.map { try $0.attribute("name") })
    #expect(names.contains("Pure.reflexive"))
    #expect(names.contains("Pure.conjunction_def"))
    let reflexive = entities.first { $0.attributes["name"] == "Pure.reflexive" }
    #expect(try reflexive?.attribute("file") == "theory.ML")
}
