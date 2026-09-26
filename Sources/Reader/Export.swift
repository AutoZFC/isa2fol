import Foundation
import YXML

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

    var path: String { "\(theory)/proofs/\(serial)" }
}

struct Corpus {
    let names: [TheoremKey: String]
    let files: [TheoremKey: Body]
    let axioms: [String: (file: String, body: Body)]

    func file(_ key: TheoremKey) throws -> Body {
        guard let body = files[key] else { throw MalformedExport.unresolvedCitation(theory: key.theory, serial: key.serial) }
        return body
    }
}

public struct Export {
    public let root: String
    public let theories: [String]
    var forest = Forest()
    private(set) var constants = Constants()
    private(set) var classes = Classes()

    public init(root: String) throws {
        self.root = root
        theories = try FileManager.default.contentsOfDirectory(atPath: root).sorted()
        for theory in theories {
            if let body = try theoryFile(theory, "consts") {
                try located("\(theory)/theory/consts") { try constants.load(body, in: forest) }
            }
            if let body = try theoryFile(theory, "classes") {
                try located("\(theory)/theory/classes") { try classes.load(body, in: forest) }
            }
        }
    }

    mutating func load() throws -> Corpus {
        var names: [TheoremKey: String] = [:]
        var files: [TheoremKey: Body] = [:]
        var axioms: [String: (file: String, body: Body)] = [:]
        for theory in theories {
            for (serial, name) in try located("\(theory)/theory/thms", { try self.names(theory) }) {
                names[TheoremKey(theory: theory, serial: serial)] = name
            }
            for serial in try proofSerials(theory) {
                let key = TheoremKey(theory: theory, serial: serial)
                files[key] = try located(key.path) { try forest.parse(contentsOf: "\(root)/\(key.path)") }
            }
            let file = "\(theory)/theory/axioms"
            try located(file) {
                for (name, body) in try entities(theory, "axioms") {
                    guard axioms.updateValue((file, body), forKey: name) == nil else { throw MalformedExport.duplicateAxiom(name) }
                }
            }
        }
        return Corpus(names: names, files: files, axioms: axioms)
    }

    private func proofSerials(_ theory: String) throws -> [Int] {
        let dir = "\(root)/\(theory)/proofs"
        guard FileManager.default.fileExists(atPath: dir) else { return [] }
        return try FileManager.default.contentsOfDirectory(atPath: dir).map { file in
            guard let s = Int(file) else { throw MalformedExport.notASerial(file) }
            return s
        }.sorted()
    }

    mutating func names(_ theory: String) throws -> [Int: String] {
        var names: [Int: String] = [:]
        for (name, element) in try entityElements(theory, "thms") {
            let serial = try element.attribute("serial")
            guard let s = Int(serial) else { throw MalformedExport.notASerial(serial) }
            guard names.updateValue(name, forKey: s) == nil else { throw MalformedExport.duplicateSerial(s) }
        }
        return names
    }

    private mutating func entities(_ theory: String, _ file: String) throws -> [(String, Body)] {
        try entityElements(theory, file).map { ($0.0, $0.1.children) }
    }

    private mutating func entityElements(_ theory: String, _ file: String) throws -> [(String, Element)] {
        try (try theoryFile(theory, file) ?? []).map { r in
            guard case let .element(e) = forest[r], e.tag == "entity" else {
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
