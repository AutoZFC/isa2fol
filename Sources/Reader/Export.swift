import Foundation
import IR
import YXML

public let zfSessions = [
    "ZF",
    "ZF-AC",
    "ZF-Coind",
    "ZF-Constructible",
    "ZF-IMP",
    "ZF-Induct",
    "ZF-Resid",
    "ZF-UNITY",
    "ZF-ex",
]

public func session(of theory: String) -> String? {
    if theory.hasPrefix("ZF-") { return String(theory.prefix { $0 != "." }) }
    if theory == "ZF" || theory == "ZFC" || theory.hasPrefix("ZF.") { return "ZF" }
    return nil
}

public struct ReadFailure: Error {
    public let file: String
    public let error: any Error
}

func located<T>(_ file: String, _ body: () throws -> T) throws -> T {
    do {
        return try body()
    } catch let refusal as ReaderRefusal {
        throw refusal
    } catch let failure as ReadFailure {
        throw failure
    } catch {
        throw ReadFailure(file: file, error: error)
    }
}

struct TheoremKey: Hashable {
    let theory: String
    let serial: Int

    var path: String {
        "\(theory)/proofs/\(serial)"
    }
}

struct AxiomEntry {
    let theory: String
    let body: Body
    let order: Int

    var file: String {
        "\(theory)/theory/axioms"
    }
}

struct Corpus {
    let names: [TheoremKey: String]
    let files: [TheoremKey: Body]
    let axioms: [String: AxiomEntry]

    func file(_ key: TheoremKey) throws -> Body {
        guard let body = files[key] else { throw MalformedExport.unresolvedCitation(
            theory: key.theory,
            serial: key.serial,
        ) }
        return body
    }
}

struct Families {
    func isFoundation(_ theory: String) -> Bool {
        Families.foundation[theory] != nil
    }

    mutating func family(of theory: String, parents: (String) throws -> [String]) throws -> Family? {
        if let f = known[theory] { return f }
        var seen = Set<String>()
        var work = [theory]
        while let t = work.popLast() {
            guard seen.insert(t).inserted else { continue }
            if known[t] == .zf {
                known[theory] = .zf
                return .zf
            }
            work += try parents(t)
        }
        return nil
    }

    private static let foundation: [String: Family] = ["Pure": .pure, "IFOL": .ifol, "FOL": .fol, "ZF.ZF_Base": .zf]

    private var known: [String: Family] = foundation

}

private func listedParents(of theory: String, in root: String) throws -> [String] {
    try String(contentsOfFile: "\(root)/\(theory)/theory/parents", encoding: .utf8).split(separator: "\n")
        .map(String.init)
}

public struct Export {
    public init(root: String) throws {
        self.root = root
        theories = try FileManager.default.contentsOfDirectory(atPath: root).sorted()
        for theory in theories {
            if let body = try theoryFile(theory, "consts") {
                guard let family = try families.family(of: theory, parents: { try listedParents(of: $0, in: root) })
                else {
                    throw MalformedExport.constantsOutsideTheFamilies(theory: theory)
                }
                let inFoundation = families.isFoundation(theory)
                try located("\(theory)/theory/consts") {
                    try constants.load(body, theory: theory, family: family, foundation: inFoundation, in: forest)
                }
            }
            if let body = try theoryFile(theory, "classes") {
                guard let family = try families.family(of: theory, parents: { try listedParents(of: $0, in: root) })
                else {
                    throw MalformedExport.classesOutsideTheFamilies(theory: theory)
                }
                try located("\(theory)/theory/classes") { try classes.load(body, family: family, in: forest) }
            }
        }
        for theory in theories {
            guard let body = try theoryFile(theory, "constdefs") else { continue }
            let d = Decode(forest: forest)
            try located("\(theory)/theory/constdefs") {
                for (constant, axiom) in try d.list({ try d.pair(d.string, d.string, $0) }, body) {
                    try constants.define(constant, by: axiom)
                }
            }
        }
    }

    public let root: String
    public let theories: [String]

    var forest = Forest()
    private(set) var constants = Constants()
    private(set) var classes = Classes()
    private(set) var families = Families()

    mutating func load() throws -> Corpus {
        var names = [TheoremKey: String]()
        var files = [TheoremKey: Body]()
        var axioms = [String: AxiomEntry]()
        for theory in theories {
            for (serial, name) in try located("\(theory)/theory/thms", { try self.names(theory) }) {
                names[TheoremKey(theory: theory, serial: serial)] = name
            }
            for serial in try proofSerials(theory) {
                let key = TheoremKey(theory: theory, serial: serial)
                files[key] = try located(key.path) { try forest.parse(contentsOf: "\(root)/\(key.path)") }
            }
            try located("\(theory)/theory/axioms") {
                for (name, body) in try entities(theory, "axioms") {
                    let entry = AxiomEntry(theory: theory, body: body, order: axioms.count)
                    guard axioms.updateValue(entry, forKey: name) == nil else {
                        throw MalformedExport.duplicateAxiom(name)
                    }
                }
            }
        }
        return Corpus(names: names, files: files, axioms: axioms)
    }

    func parents(_ theory: String) throws -> [String] {
        try located("\(theory)/theory/parents") { try listedParents(of: theory, in: root) }
    }

    mutating func names(_ theory: String) throws -> [Int: String] {
        var names = [Int: String]()
        for (name, element) in try entityElements(theory, "thms") {
            let serial = try element.attribute("serial")
            guard let s = Int(serial) else { throw MalformedExport.notASerial(serial) }
            guard names.updateValue(name, forKey: s) == nil else { throw MalformedExport.duplicateSerial(s) }
        }
        return names
    }

    private func proofSerials(_ theory: String) throws -> [Int] {
        let dir = "\(root)/\(theory)/proofs"
        guard FileManager.default.fileExists(atPath: dir) else { return [] }
        return try FileManager.default.contentsOfDirectory(atPath: dir).map { file in
            guard let s = Int(file) else { throw MalformedExport.notASerial(file) }
            return s
        }.sorted()
    }

    private mutating func entities(_ theory: String, _ file: String) throws -> [(String, Body)] {
        try entityElements(theory, file).map { ($0.0, $0.1.children) }
    }

    private mutating func entityElements(_ theory: String, _ file: String) throws -> [(String, Element)] {
        try (try theoryFile(theory, file) ?? []).map { r in
            guard case .element(let e) = forest[r], e.tag == "entity" else {
                throw MalformedExport.notAnEntity(tag: Decode(forest: forest).tag(r))
            }
            return (try e.attribute("name"), e)
        }
    }

    private mutating func theoryFile(_ theory: String, _ file: String) throws -> [Ref]? {
        let path = "\(root)/\(theory)/theory/\(file)"
        guard FileManager.default.fileExists(atPath: path) else { return nil }
        return try located("\(theory)/theory/\(file)") { try forest.parse(contentsOf: path) }
    }
}
