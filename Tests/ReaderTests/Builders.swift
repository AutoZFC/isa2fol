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
    ("T.h", [], fn(fn(i, o), o)),
    ("T.k", [], fn(fn(fn(i, o), o), i)),
    ("T.claim", [], prop),
    ("T.metaEx", ["'a"], fn(fn(typeA, prop), prop)),
]

let constsFile = declarations.map { constEntity($0.0, parameters: $0.1, scheme: $0.2) }.joined()

func testConstants() throws -> Constants {
    var f = Forest()
    let body = try f.parse(Array(constsFile.utf8))
    var c = Constants()
    try c.load(body, in: f)
    return c
}

func proofFile(tfrees: [String] = [], frees: [(String, String)], prop: String, proof: String = pnop) -> String {
    let tf = tfrees.map { node(node($0), node()) }.joined()
    let fr = frees.map { node(node($0.0), node($0.1)) }.joined()
    return node(tf) + node(node(fr) + node(node(prop) + node(proof)))
}

let pnop = tagged(0, [], [])
func pbound(_ k: Int) -> String { tagged(1, [], [String(k)]) }
func pabst(_ name: String, _ T: String, _ body: String) -> String { tagged(2, [name], [node(T), node(body)]) }
func pabsp(_ name: String, _ t: String, _ body: String) -> String { tagged(3, [name], [node(t), node(body)]) }
func pappt(_ p: String, _ t: String) -> String { tagged(4, [], [node(p), node(t)]) }
func pappp(_ p: String, _ args: String...) -> String { args.reduce(p) { tagged(5, [], [node($0), node($1)]) } }
func phyp(_ t: String) -> String { tagged(6, [], [t]) }
func paxiom(_ name: String, _ types: String...) -> String { tagged(7, [name], types.map { node($0) }) }
func pofclass(_ T: String, _ c: String) -> String { tagged(8, [c], [T]) }
func poracle(_ name: String) -> String { tagged(9, [name], []) }
func pcite(_ serial: Int, _ theory: String, _ name: String = "", _ types: String...) -> String {
    tagged(10, [String(serial), theory, name, "0"], types.map { node($0) })
}

func classEntity(_ name: String, axiomFree: Bool) -> String {
    element("entity", [("name", name)], [node(), node(axiomFree ? "" : node())])
}

let classesFile = classEntity("IFOL.term", axiomFree: true) + classEntity("T.withAxioms", axiomFree: false)

func testClasses() throws -> Classes {
    var f = Forest()
    let body = try f.parse(Array(classesFile.utf8))
    var c = Classes()
    try c.load(body, in: f)
    return c
}

func axiomEntity(_ name: String, tfrees: [String] = [], frees: [(String, String)] = [], prop: String) -> String {
    element("entity", [("name", name)], [
        node(tfrees.map { node(node($0), node()) }.joined()),
        node(frees.map { node(node($0.0), node($0.1)) }.joined()),
        node(prop),
    ])
}

func thmsFile(_ entries: [(String, Int)]) -> String {
    entries.map { element("entity", [("name", $0.0), ("serial", String($0.1))], []) }.joined()
}
