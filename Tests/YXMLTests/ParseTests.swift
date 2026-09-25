import Foundation
import Testing
import YXML

private let X = "\u{05}"
private let Y = "\u{06}"

private func bytes(_ s: String) -> [UInt8] { Array(s.utf8) }
private func open(_ tag: String, _ attributes: String...) -> String { X + Y + ([tag] + attributes).joined(separator: Y) + X }
private let close = X + Y + X

private func element(_ f: Forest, _ r: Ref) throws -> Element {
    guard case let .element(e) = f[r] else { throw ExpectedElement() }
    return e
}
private struct ExpectedElement: Error {}

private func one(_ s: String) throws -> (Forest, Element) {
    var f = Forest()
    let body = try f.parse(bytes(s))
    try #require(body.count == 1)
    return (f, try element(f, body[0]))
}

@Test func anElementCarriesItsTagAndAttributesInFileOrder() throws {
    let (_, e) = try one(open("0", "1=b", "0=ZF_Base.mem") + close)
    #expect(e.tag == "0")
    #expect(e.attributes == [Attribute(name: "1", value: "b"), Attribute(name: "0", value: "ZF_Base.mem")])
    #expect(try e.attribute("0") == "ZF_Base.mem")
}

@Test func aMissingAttributeIsAnErrorNotEmpty() throws {
    let (_, e) = try one(open("0", "0=ZF_Base.mem") + close)
    #expect(throws: YXMLError.missingAttribute(tag: "0", name: "absent")) { try e.attribute("absent") }
}

@Test func anEmptyAttributeValueIsPresent() throws {
    let (_, e) = try one(open("0", "k=") + close)
    #expect(try e.attribute("k") == "")
}

@Test func anAttributeFieldWithoutEqualsIsAnError() {
    var f = Forest()
    #expect(throws: YXMLError.malformedAttribute(tag: "0", field: "junk")) { try f.parse(bytes(open("0", "junk") + close)) }
}

@Test func aDuplicateAttributeIsAnError() {
    var f = Forest()
    #expect(throws: YXMLError.duplicateAttribute(tag: "0", name: "k")) {
        try f.parse(bytes(open("0", "k=a", "k=b") + close))
    }
}

@Test func anEmptyTagIsAnErrorNotAClose() {
    var f = Forest()
    #expect(throws: YXMLError.emptyTag) { try f.parse(bytes(open("a") + open("", "k=v") + close + close)) }
}

@Test func textBetweenMarkupSurvives() throws {
    let (f, e) = try one(open("3") + "17" + close)
    #expect(e.children.map { f[$0] } == [.text("17")])
}

@Test func anUnbalancedCloseIsAnError() {
    var f = Forest()
    #expect(throws: YXMLError.unbalancedClose) { try f.parse(bytes(close)) }
}

@Test func anUnclosedElementIsAnError() {
    var f = Forest()
    #expect(throws: YXMLError.unclosed(tag: "a")) { try f.parse(bytes(open("a") + open("b") + close)) }
}

@Test func invalidUTF8IsAnErrorNotAReplacement() {
    var f = Forest()
    #expect(throws: YXMLError.invalidUTF8) { try f.parse(bytes(open("a")) + [0xFF] + bytes(close)) }
}

@Test func equalSubtreesAreOneRef() throws {
    var f = Forest()
    let ab = open("a") + open("b") + "x" + close + close
    let body = try f.parse(bytes(ab + ab + open("a") + open("b") + "y" + close + close))
    #expect(body.count == 3)
    #expect(body[0] == body[1])
    #expect(body[0] != body[2])
}

@Test func aForestSharesSubtreesAcrossParses() throws {
    var f = Forest()
    let first = try f.parse(bytes(open("a", "k=v") + "x" + close))
    let size = f.count
    let second = try f.parse(bytes(open("a", "k=v") + "x" + close))
    #expect(first == second)
    #expect(f.count == size)
}

/// The parser is only right if it reads what Isabelle actually wrote.
@Test func aRealExportFileParses() throws {
    let root = "data/zf_export/Pure/theory/axioms"
    guard FileManager.default.fileExists(atPath: root) else {
        Issue.record("export missing at \(root) — run scripts/03-export-zf.sh from the repo root")
        return
    }
    var f = Forest()
    let entities = try f.parse(contentsOf: root).map { try element(f, $0) }.filter { $0.tag == "entity" }
    #expect(entities.count >= 11, "Pure declares 11 axioms")
    let names = Set(try entities.map { try $0.attribute("name") })
    #expect(names.contains("Pure.reflexive"))
    #expect(names.contains("Pure.conjunction_def"))
    let reflexive = try entities.first { try $0.attribute("name") == "Pure.reflexive" }
    #expect(try reflexive?.attribute("file") == "theory.ML")
}

/// ⚠ Slow in a debug build: `ISA2FOL_SCALE=1 swift test -c release --filter theLargestProofFile`.
@Test(.enabled(if: ProcessInfo.processInfo.environment["ISA2FOL_SCALE"] != nil))
func theLargestProofFileReadsAsItsDAG() throws {
    let dir = "data/zf_export/ZF.List/proofs"
    let files = try FileManager.default.contentsOfDirectory(atPath: dir)
    let sizes = try files.map { ($0, try FileManager.default.attributesOfItem(atPath: "\(dir)/\($0)")[.size] as! Int) }
    let (largest, size) = try #require(sizes.max { $0.1 < $1.1 })
    try #require(size > 1_000_000_000, "the export is expected to hold one proof file over 1 GB")
    var f = Forest()
    _ = try f.parse(contentsOf: "\(dir)/\(largest)")
    #expect(f.count < 20_000, "312 M tree nodes, measured 11,604 distinct")
}
