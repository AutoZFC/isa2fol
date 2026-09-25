import Foundation
import IR
import YXML

@frozen public enum Outcome: Equatable, Sendable {
    case translated(root: NodeID, frees: [NodeID])
    case refused(ReaderRefusal)
}

public struct Read: Equatable, Sendable {
    public let serial: Int
    public let name: String?
    public let outcome: Outcome
}

struct StatementReader {
    let decode: Decode
    let constants: Constants

    func read(_ file: Body, into t: inout Table) throws -> Outcome {
        let d = decode
        let (tfrees, rest) = try d.pair({ try d.list({ try d.pair(d.string, { try d.list(d.string, $0) }, $0).0 }, $0) },
                                        { $0 }, file)
        let (header, statement) = try d.pair({ try d.list({ try d.pair(d.string, d.type, $0) }, $0) }, { $0 }, rest)
        let (prop, _) = try d.pair({ $0 }, { $0 }, statement)
        let names = header.map(\.0)
        let occurring = try d.frees(prop)
        guard occurring == names else { throw MalformedExport.freesHeader(header: names, occurring: occurring) }
        do {
            if let a = tfrees.first { throw ReaderRefusal.typeVariable(a) }
            let typed = try header.map { ($0.0, try $0.1.irType()) }
            let terms = Terms(decode: d, constants: constants, frees: Dictionary(uniqueKeysWithValues: typed))
            let root = try terms.proposition(prop, in: &t)
            return .translated(root: root, frees: try typed.map { try t.intern(.isaFree($0.0, $0.1)) })
        } catch let r as ReaderRefusal {
            return .refused(r)
        }
    }
}

extension Decode {
    func frees(_ body: Body) throws -> [String] {
        var seen = Set<Ref>(), known = Set<String>(), names: [String] = []
        try collect(body, &seen, &known, &names)
        return names
    }

    private func collect(_ body: Body, _ seen: inout Set<Ref>, _ known: inout Set<String>, _ names: inout [String]) throws {
        let (head, arguments) = try spine(body)
        guard seen.insert(body[0]).inserted else { return }
        switch head {
        case let .free(name):
            if known.insert(name).inserted { names.append(name) }
        case let .abstraction(_, inner):
            try collect(inner, &seen, &known, &names)
        case .constant, .schematic, .bound, .ofclass:
            break
        }
        for a in arguments { try collect(a, &seen, &known, &names) }
    }
}

func claimName(_ entity: String) throws -> String {
    var base = Substring(entity), index = ""
    if entity.hasSuffix(")"), let open = entity.lastIndex(of: "(") {
        let digits = entity[entity.index(after: open)..<entity.index(before: entity.endIndex)]
        if !digits.isEmpty, digits.allSatisfy({ $0.isASCII && $0.isNumber }) {
            base = entity[..<open]
            index = "." + digits
        }
    }
    let wellFormed = base.split(separator: ".", omittingEmptySubsequences: false).allSatisfy { segment in
        guard let c = segment.first else { return false }
        return !c.isNumber
    }
    guard wellFormed else { throw ReaderRefusal.nameSegment(entity) }
    return base + index
}

public struct Export {
    public let root: String
    public let theories: [String]
    private var forest = Forest()
    private var constants = Constants()

    public init(root: String) throws {
        self.root = root
        theories = try FileManager.default.contentsOfDirectory(atPath: root).sorted()
        for theory in theories where FileManager.default.fileExists(atPath: "\(root)/\(theory)/theory/consts") {
            let body = try forest.parse(contentsOf: "\(root)/\(theory)/theory/consts")
            try constants.load(body, in: forest)
        }
    }

    public mutating func statements(_ theory: String, into t: inout Table) throws -> [Read] {
        let entities = try names(theory)
        let dir = "\(root)/\(theory)/proofs"
        guard FileManager.default.fileExists(atPath: dir) else { return [] }
        let serials = try FileManager.default.contentsOfDirectory(atPath: dir).map { file in
            guard let s = Int(file) else { throw MalformedExport.notASerial(file) }
            return s
        }.sorted()
        var reads: [Read] = []
        for serial in serials {
            let body = try forest.parse(contentsOf: "\(dir)/\(serial)")
            let reader = StatementReader(decode: Decode(forest: forest), constants: constants)
            var name: String?
            let outcome: Outcome
            do {
                name = try entities[serial].map(claimName)
                outcome = try reader.read(body, into: &t)
            } catch let r as ReaderRefusal {
                outcome = .refused(r)
            }
            reads.append(Read(serial: serial, name: name, outcome: outcome))
        }
        return reads
    }

    private mutating func names(_ theory: String) throws -> [Int: String] {
        let path = "\(root)/\(theory)/theory/thms"
        guard FileManager.default.fileExists(atPath: path) else { return [:] }
        var names: [Int: String] = [:]
        for r in try forest.parse(contentsOf: path) {
            guard case let .element(e) = forest[r], e.tag == "entity" else {
                throw MalformedExport.notAnEntity(tag: Decode(forest: forest).tag(r))
            }
            let serial = try e.attribute("serial")
            guard let s = Int(serial) else { throw MalformedExport.notASerial(serial) }
            guard names.updateValue(try e.attribute("name"), forKey: s) == nil else { throw MalformedExport.duplicateSerial(s) }
        }
        return names
    }
}
