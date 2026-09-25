import Foundation

private let X = UInt8(0x05)
private let Y = UInt8(0x06)

public struct Forest: Sendable {
    private enum Stored: Sendable {
        case element(label: Int32, children: Range<Int>)
        case text(String)
    }

    private struct Label: Sendable {
        let tag: String
        let attributes: [Attribute]
    }

    private var items: [Stored] = []
    private var children: [Ref] = []
    private var labels: [Label] = []
    private var labelBytes = ByteSet()
    private var textBytes = ByteSet()
    private var textRefs: [Ref] = []
    private var elements = HashIndex()

    public init() {}

    public var count: Int { items.count }

    public subscript(_ r: Ref) -> Item {
        switch items[Int(r.raw)] {
        case let .element(label, range):
            let l = labels[Int(label)]
            return .element(Element(tag: l.tag, attributes: l.attributes, children: Array(children[range])))
        case let .text(s):
            return .text(s)
        }
    }

    public mutating func parse(contentsOf path: String) throws -> [Ref] {
        let data = try Data(contentsOf: URL(fileURLWithPath: path), options: .alwaysMapped)
        return try data.withUnsafeBytes { try parse($0) }
    }

    public mutating func parse(_ bytes: [UInt8]) throws -> [Ref] {
        try bytes.withUnsafeBytes { try parse($0) }
    }

    public mutating func parse(_ bytes: UnsafeRawBufferPointer) throws -> [Ref] {
        var frames: [(label: Int32, start: Int)] = []
        var open: [Ref] = []
        var i = 0
        while i < bytes.count {
            var j = i
            while j < bytes.count && bytes[j] != X { j += 1 }
            if j > i {
                let chunk = UnsafeRawBufferPointer(rebasing: bytes[i..<j])
                if chunk[0] != Y {
                    open.append(try text(chunk))
                } else if chunk.count == 1 {
                    guard let f = frames.popLast() else { throw YXMLError.unbalancedClose }
                    let r = element(f.label, open[f.start...])
                    open.removeSubrange(f.start...)
                    open.append(r)
                } else {
                    frames.append((try label(UnsafeRawBufferPointer(rebasing: chunk.dropFirst())), open.count))
                }
            }
            i = j + 1
        }
        if let f = frames.last { throw YXMLError.unclosed(tag: labels[Int(f.label)].tag) }
        return open
    }

    private mutating func text(_ bytes: UnsafeRawBufferPointer) throws -> Ref {
        let hash = ByteSet.hash(bytes)
        if let id = textBytes.find(bytes, hash) { return textRefs[Int(id)] }
        let s = try utf8(bytes)
        _ = textBytes.insert(bytes, hash)
        let r = Ref(raw: Int32(items.count))
        items.append(.text(s))
        textRefs.append(r)
        return r
    }

    private mutating func label(_ bytes: UnsafeRawBufferPointer) throws -> Int32 {
        let hash = ByteSet.hash(bytes)
        if let id = labelBytes.find(bytes, hash) { return id }
        labels.append(try Self.decodeLabel(bytes))
        return labelBytes.insert(bytes, hash)
    }

    private mutating func element(_ label: Int32, _ kids: ArraySlice<Ref>) -> Ref {
        var h = Hasher()
        h.combine(label)
        h.combine(kids.count)
        for k in kids { h.combine(k.raw) }
        let hash = h.finalize()
        if let raw = elements.find(hash, { isElement($0, label, kids) }) { return Ref(raw: raw) }
        let start = children.count
        children.append(contentsOf: kids)
        let r = Ref(raw: Int32(items.count))
        items.append(.element(label: label, children: start..<children.count))
        elements.insert(hash, r.raw)
        return r
    }

    private func isElement(_ raw: Int32, _ label: Int32, _ kids: ArraySlice<Ref>) -> Bool {
        guard case let .element(l, range) = items[Int(raw)], l == label else { return false }
        return children[range].elementsEqual(kids)
    }

    private static func decodeLabel(_ bytes: UnsafeRawBufferPointer) throws -> Label {
        let fields = bytes.split(separator: Y, omittingEmptySubsequences: false)
        let tag = try utf8(fields[0])
        guard !tag.isEmpty else { throw YXMLError.emptyTag }
        var attributes: [Attribute] = []
        for field in fields.dropFirst() {
            let s = try utf8(field)
            guard let eq = s.firstIndex(of: "=") else { throw YXMLError.malformedAttribute(tag: tag, field: s) }
            let name = String(s[..<eq])
            guard !attributes.contains(where: { $0.name == name }) else {
                throw YXMLError.duplicateAttribute(tag: tag, name: name)
            }
            attributes.append(Attribute(name: name, value: String(s[s.index(after: eq)...])))
        }
        return Label(tag: tag, attributes: attributes)
    }
}

private func utf8<S: Sequence<UInt8>>(_ bytes: S) throws -> String {
    guard let s = String(validating: bytes, as: UTF8.self) else { throw YXMLError.invalidUTF8 }
    return s
}
