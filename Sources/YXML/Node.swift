public struct Node: Sendable {
    public var tag: String
    public var attributes: [String: String]
    public var children: [Node]
    public var text: String

    public init(tag: String = "", attributes: [String: String] = [:],
                children: [Node] = [], text: String = "") {
        self.tag = tag
        self.attributes = attributes
        self.children = children
        self.text = text
    }

    public var isText: Bool { tag.isEmpty }

    public func attribute(_ name: String) throws -> String {
        guard let value = attributes[name] else { throw YXMLError.missingAttribute(tag: tag, name: name) }
        return value
    }

    public var elements: [Node] {
        children.filter { !$0.isText }
    }

    public var allText: String {
        isText ? text : children.map(\.allText).joined()
    }
}
