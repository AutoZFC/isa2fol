import Foundation

public enum YXMLError: Error, Equatable {
    case unbalancedClose
    case unclosed(tag: String)
    case malformedAttribute(tag: String, field: String)
    case duplicateAttribute(tag: String, name: String)
    case missingAttribute(tag: String, name: String)
}

private let X = UInt8(0x05)
private let Y = UInt8(0x06)

public func parse(_ bytes: [UInt8]) throws -> Node {
    var stack = [Node(tag: "")]

    for chunk in bytes.split(separator: X, omittingEmptySubsequences: false) {
        if chunk.isEmpty { continue }
        if chunk.first != Y {
            stack[stack.count - 1].children.append(
                Node(text: String(decoding: chunk, as: UTF8.self)))
            continue
        }
        let fields = chunk.dropFirst().split(separator: Y, omittingEmptySubsequences: false)
        if fields.isEmpty || fields[0].isEmpty {
            guard stack.count > 1 else { throw YXMLError.unbalancedClose }
            let done = stack.removeLast()
            stack[stack.count - 1].children.append(done)
            continue
        }
        var node = Node(tag: String(decoding: fields[0], as: UTF8.self))
        for f in fields.dropFirst() {
            let s = String(decoding: f, as: UTF8.self)
            guard let eq = s.firstIndex(of: "=") else {
                throw YXMLError.malformedAttribute(tag: node.tag, field: s)
            }
            let name = String(s[s.startIndex..<eq])
            guard node.attributes[name] == nil else {
                throw YXMLError.duplicateAttribute(tag: node.tag, name: name)
            }
            node.attributes[name] = String(s[s.index(after: eq)...])
        }
        stack.append(node)
    }

    guard stack.count == 1 else { throw YXMLError.unclosed(tag: stack.last!.tag) }
    return stack[0]
}

public func parse(contentsOf path: String) throws -> Node {
    try parse([UInt8](Data(contentsOf: URL(fileURLWithPath: path))))
}
