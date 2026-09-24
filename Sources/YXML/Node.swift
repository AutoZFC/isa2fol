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

    public func attribute(_ name: String) -> String {
        attributes[name] ?? ""
    }

    public var elements: [Node] {
        children.filter { !$0.isText }
    }

    public var allText: String {
        isText ? text : children.map(\.allText).joined()
    }
}
