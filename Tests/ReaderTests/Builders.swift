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

let prop = typeT("prop")
let typeA = tfree("'a")

func const(_ name: String, _ typeArguments: String...) -> String { tagged(0, [name], typeArguments.map { node($0) }) }
func free(_ name: String) -> String { tagged(1, [name], []) }
func schematic(_ name: String) -> String { tagged(2, [name], []) }
func bound(_ k: Int) -> String { tagged(3, [], [String(k)]) }
func lam(_ name: String, _ T: String, _ body: String) -> String { tagged(4, [name], [node(T), node(body)]) }
func app(_ f: String, _ args: String...) -> String { args.reduce(f) { tagged(5, [], [node($0), node($1)]) } }
func ofclass(_ T: String, _ c: String) -> String { tagged(6, [c], [T]) }
func trueprop(_ t: String) -> String { app(const("IFOL.Trueprop"), t) }

private let declarations: [(String, [String], String)] = [
    ("Pure.prop", [], fn(prop, prop)),
    ("Pure.imp", [], fn(prop, fn(prop, prop))),
    ("Pure.eq", ["'a"], fn(typeA, fn(typeA, prop))),
    ("Pure.all", ["'a"], fn(fn(typeA, prop), prop)),
    ("Pure.term", ["'a"], fn(typeA, prop)),
    ("Pure.conjunction", [], fn(prop, fn(prop, prop))),
    ("IFOL.Trueprop", [], fn(o, prop)),
    ("IFOL.False", [], o),
    ("IFOL.conj", [], fn(o, fn(o, o))),
    ("IFOL.disj", [], fn(o, fn(o, o))),
    ("IFOL.imp", [], fn(o, fn(o, o))),
    ("IFOL.iff", [], fn(o, fn(o, o))),
    ("IFOL.Not", [], fn(o, o)),
    ("IFOL.eq", ["'a"], fn(typeA, fn(typeA, o))),
    ("IFOL.All", ["'a"], fn(fn(typeA, o), o)),
    ("IFOL.Ex", ["'a"], fn(fn(typeA, o), o)),
    ("ZF_Base.mem", [], fn(i, fn(i, o))),
    ("ZF_Base.Ball", [], fn(i, fn(fn(i, o), o))),
    ("ZF_Base.split", ["'a"], fn(fn(i, fn(i, typeA)), fn(i, typeA))),
    ("Sum.Inl", [], fn(i, i)),
    ("Sum.Part", [], fn(i, fn(fn(i, i), i))),
    ("EquivClass.congruent", [], fn(i, fn(fn(i, i), o))),
    ("T.f", [], fn(i, fn(i, i))),
    ("T.g", [], fn(fn(i, fn(i, i)), i)),
]

func testConstants() throws -> Constants {
    var f = Forest()
    let body = try f.parse(Array(declarations.map { constEntity($0.0, parameters: $0.1, scheme: $0.2) }.joined().utf8))
    var c = Constants()
    try c.load(body, in: f)
    return c
}
