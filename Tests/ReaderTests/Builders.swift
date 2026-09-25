import YXML
@testable import Reader

private let X = "\u{05}"
private let Y = "\u{06}"

func element(_ tag: String, _ attributes: [(String, String)], _ body: [String]) -> String {
    X + Y + ([tag] + attributes.map { "\($0.0)=\($0.1)" }).joined(separator: Y) + X
        + body.joined() + X + Y + X
}

func tagged(_ tag: Int, _ atoms: [String], _ body: [String]) -> String {
    element(String(tag), atoms.enumerated().map { (String($0.offset), $0.element) }, body)
}

func node(_ body: String...) -> String { element(":", [], body) }

func typeT(_ name: String, _ args: String...) -> String { tagged(0, [name], args.map { node($0) }) }
func tfree(_ name: String, _ sort: String...) -> String { tagged(1, [name], sort.map { node($0) }) }
func tvar(_ atoms: [String], _ sort: String...) -> String { tagged(2, atoms, sort.map { node($0) }) }

func fn(_ a: String, _ b: String) -> String { typeT("fun", a, b) }
let i = typeT("ZF_Base.i")
let o = typeT("IFOL.o")

func constEntity(_ name: String, parameters: [String], scheme: String) -> String {
    element("entity", [("name", name)], [
        node(tagged(0, [], [])),
        node(node(parameters.map { node($0) }.joined()),
             node(node(scheme), node(node(), node("1")))),
    ])
}

func decodeType(_ s: String) throws -> IsaType {
    var f = Forest()
    let body = try f.parse(Array(s.utf8))
    return try Decode(forest: f).type(body)
}
