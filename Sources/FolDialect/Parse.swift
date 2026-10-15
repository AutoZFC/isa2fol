import Foundation
import IR

@frozen public enum ParseError: Error, Equatable, Sendable {
    case notASchema(String)
    case notAClaim(String)
    case letterArity(String)
    case unknownName(String)
    case unexpected(String)
    case missing(String)
    case duplicate(String)
}

public func parse(schema line: String, in t: inout Table) throws -> (name: String, root: NodeID) {
    var p = Parser(tokens: try tokens(line))
    guard p.take() == "schema", let name = p.take(), isName(name) else { throw ParseError.notASchema(line) }
    try p.expect("[")
    var letters: [String] = []
    while true {
        guard let letter = p.take(), isName(letter) else { throw ParseError.notASchema(line) }
        try p.expect("(")
        guard p.take() == "0" else { throw ParseError.letterArity(letter) }
        try p.expect(")")
        letters.append(letter)
        guard let next = p.take() else { throw ParseError.unexpected("end") }
        if next == "]" { break }
        guard next == "," else { throw ParseError.unexpected(next) }
    }
    try p.expect(":")
    var body = try p.formula(Scope(letters: letters), in: &t)
    if let rest = p.take() { throw ParseError.unexpected(rest) }
    for _ in letters { body = try t.intern(.ifolAll(.o, body: body)) }
    return (name, body)
}

public func parse(claim line: String, in t: inout Table) throws -> (name: String, root: NodeID) {
    guard let (kind, name) = statementName(line), kind != .schema else { throw ParseError.notAClaim(line) }
    var p = Parser(tokens: try tokens(line))
    while let token = p.take(), token != ":" {}
    let body = try p.formula(Scope(letters: []), in: &t)
    if let rest = p.take() { throw ParseError.unexpected(rest) }
    return (name, body)
}

public func parse(statements names: [String], from texts: [String], in t: inout Table) throws -> [String: NodeID] {
    let wanted = Set(names)
    var lines: [String: (Kind, String)] = [:]
    for text in texts {
        for line in text.split(separator: "\n").map(String.init) {
            guard let (kind, name) = statementName(line), wanted.contains(name) else { continue }
            guard lines.updateValue((kind, line), forKey: name) == nil else { throw ParseError.duplicate(name) }
        }
    }
    var parsed: [String: NodeID] = [:]
    for name in names {
        guard let (kind, line) = lines[name] else { throw ParseError.missing(name) }
        parsed[name] = try (kind == .schema ? parse(schema: line, in: &t) : parse(claim: line, in: &t)).root
    }
    return parsed
}

private enum Kind { case schema, claim }

private func statementName(_ line: String) -> (Kind, String)? {
    let words = line.split(separator: " ").map(String.init)
    guard let first = words.first else { return nil }
    switch first {
    case "schema": return words.count > 1 ? (.schema, words[1]) : nil
    case "claim", "axiom": return words.count > 1 && words[1].hasSuffix(":") ? (.claim, String(words[1].dropLast())) : nil
    default:
        guard first.hasPrefix("@def("), words.count > 2, words[1] == "axiom", words[2].hasSuffix(":") else { return nil }
        return (.claim, String(words[2].dropLast()))
    }
}

private struct Scope {
    let letters: [String]
    var variables: [String] = []
}

public func baseTexts(_ directory: URL) throws -> [String] {
    let tiers = directory.appendingPathComponent("tiers")
    let files = try FileManager.default.contentsOfDirectory(atPath: tiers.path).filter { $0.hasSuffix(".fol.def") }.sorted()
    return try ([directory.appendingPathComponent("axioms.fol.def")] + files.map { tiers.appendingPathComponent($0) })
        .map { try String(contentsOf: $0, encoding: .utf8) }
}

private struct Parser {
    let tokens: [String]
    var at = 0

    mutating func take() -> String? {
        guard at < tokens.count else { return nil }
        defer { at += 1 }
        return tokens[at]
    }

    mutating func expect(_ token: String) throws {
        guard let found = take() else { throw ParseError.unexpected("end") }
        guard found == token else { throw ParseError.unexpected(found) }
    }

    mutating func formula(_ s: Scope, in t: inout Table) throws -> NodeID {
        let left = try unary(s, in: &t)
        guard at < tokens.count, let connective = binary[tokens[at]] else { return left }
        at += 1
        return try t.intern(connective(left, try unary(s, in: &t)))
    }

    private mutating func unary(_ s: Scope, in t: inout Table) throws -> NodeID {
        guard let token = take() else { throw ParseError.unexpected("end") }
        switch token {
        case "(":
            let inner = try formula(s, in: &t)
            try expect(")")
            return inner
        case "~":
            return try t.intern(.folNot(try unary(s, in: &t)))
        case "false":
            return try t.intern(.folBottom)
        case "forall", "exists":
            guard let bound = take(), bound.hasSuffix("."), isName(String(bound.dropLast())) else {
                throw ParseError.unexpected(token)
            }
            var inner = s
            inner.variables.append(String(bound.dropLast()))
            let body = try formula(inner, in: &t)
            return try t.intern(token == "forall" ? .folForall(body: body) : .folExists(body: body))
        default:
            if let k = s.letters.firstIndex(of: token) {
                return try t.intern(.isaBound(s.variables.count + s.letters.count - 1 - k, .o))
            }
            guard isName(token), at < tokens.count, tokens[at] == "(" else {
                throw isName(token) ? ParseError.unknownName(token) : ParseError.unexpected(token)
            }
            at += 1
            var args: [NodeID] = []
            while true {
                guard let name = take(), let k = s.variables.lastIndex(of: name) else { throw ParseError.unknownName(tokens[at - 1]) }
                args.append(try t.intern(.folBound(s.variables.count - 1 - k)))
                guard let next = take() else { throw ParseError.unexpected("end") }
                if next == ")" { break }
                guard next == "," else { throw ParseError.unexpected(next) }
            }
            return try t.intern(.folPred(predicate(token), args: args))
        }
    }
}

private func predicate(_ name: String) -> IR.Predicate {
    Primitive.all.first { $0.name == name }.map { .constant(.primitive($0)) } ?? .base(name)
}

private let binary: [String: (NodeID, NodeID) -> Node] = [
    "->": { .folImplies($0, $1) }, "<->": { .folIff($0, $1) }, "&": { .folAnd($0, $1) }, "|": { .folOr($0, $1) },
]

private func isName(_ s: String) -> Bool {
    guard let first = s.unicodeScalars.first, CharacterSet.letters.contains(first) || first == "_" else { return false }
    return s.unicodeScalars.allSatisfy { CharacterSet.alphanumerics.contains($0) || $0 == "_" || $0 == "'" || $0 == "." }
}

private func tokens(_ line: String) throws -> [String] {
    var found: [String] = [], word = ""
    var chars = Array(line)[...]
    func flush() {
        if !word.isEmpty { found.append(word) }
        word = ""
    }
    while let c = chars.first {
        if c.isWhitespace {
            flush()
            chars = chars.dropFirst()
        } else if let symbol = ["<->", "->", "(", ")", "[", "]", ",", ":", "~", "&", "|"].first(where: { chars.starts(with: $0) }) {
            flush()
            found.append(symbol)
            chars = chars.dropFirst(symbol.count)
        } else {
            word.append(c)
            chars = chars.dropFirst()
        }
    }
    flush()
    return found
}
