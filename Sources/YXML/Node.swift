/// Isabelle's transfer format. Knows nothing of either dialect.
///
/// X = 0x05 separates chunks, Y = 0x06 separates fields within a markup chunk.
/// `XY name Y k=v Y … X` opens an element; `XYX` closes one; anything else is
/// text.
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

    /// Element children, skipping text nodes.
    public var elements: [Node] {
        children.filter { !$0.isText }
    }

    /// All text under this node, concatenated.
    public var allText: String {
        isText ? text : children.map(\.allText).joined()
    }
}
