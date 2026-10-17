@frozen
public enum YXMLError: Error, Equatable, Sendable {
    case unbalancedClose
    case unclosed(tag: String)
    case emptyTag
    case malformedAttribute(tag: String, field: String)
    case duplicateAttribute(tag: String, name: String)
    case missingAttribute(tag: String, name: String)
    case invalidUTF8
}

public struct Ref: Hashable, Sendable, CustomStringConvertible {
    public var description: String {
        "#\(raw)"
    }

    let raw: Int32
}

public struct Attribute: Hashable, Sendable {
    public init(name: String, value: String) {
        self.name = name
        self.value = value
    }

    public let name: String
    public let value: String

}

public struct Element: Equatable, Sendable {
    public let tag: String
    public let attributes: [Attribute]
    public let children: [Ref]

    public func attribute(_ name: String) throws -> String {
        guard let a = attributes.first(where: { $0.name == name }) else {
            throw YXMLError.missingAttribute(tag: tag, name: name)
        }
        return a.value
    }
}

@frozen
public enum Item: Equatable, Sendable {
    case element(Element)
    case text(String)
}
