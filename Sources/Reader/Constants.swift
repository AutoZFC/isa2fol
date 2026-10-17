import IR
import YXML

enum Reading: Equatable {
    case erased
    case implies
    case and
    case or
    case bottom
    case all
    case ex
    case metaAll
    case metaEquality
    case hidden
    case constant(Constant)
}

private let leaves: [String: Reading] = [
    "IFOL.Trueprop": .erased,
    "Pure.imp": .implies,
    "IFOL.imp": .implies,
    "IFOL.conj": .and,
    "IFOL.disj": .or,
    "IFOL.False": .bottom,
    "Pure.all": .metaAll,
    "IFOL.All": .all,
    "IFOL.Ex": .ex,
    "Pure.eq": .metaEquality,
    "Pure.dummy_pattern": .hidden,
]

private let primitives = Dictionary(uniqueKeysWithValues: Primitive.all.map { ($0.name, $0) })

struct Constants {
    struct Declaration: Equatable {
        let parameters: [String]
        let scheme: IsaType
        let family: Family
        let foundation: Bool
        var definition: String? = nil
    }

    subscript(_ name: String) -> Declaration? {
        declarations[name]
    }

    func defined(byAxiom axiom: String) -> Defined? {
        definitions[axiom]
    }

    mutating func load(_ body: [Ref], family: Family, foundation: Bool, in forest: Forest) throws {
        let d = Decode(forest: forest)
        for r in body {
            guard case .element(let entity) = forest[r], entity.tag == "entity" else {
                throw MalformedExport.notAnEntity(tag: d.tag(r))
            }
            let name = try entity.attribute("name")
            let (_, rest) = try d.pair({ $0 }, { $0 }, entity.children)
            let (parameters, typed) = try d.pair({ try d.list(d.string, $0) }, { $0 }, rest)
            let (scheme, _) = try d.pair(d.type, { $0 }, typed)
            guard
                parameters.count == Set(parameters).count,
                scheme.variables == Set(parameters.map { IsaType.tfree($0, sort: []) })
            else {
                throw MalformedExport.schemeVariables(constant: name)
            }
            guard declarations[name] == nil else { throw MalformedExport.duplicateConstant(name) }
            declarations[name] = Declaration(
                parameters: parameters,
                scheme: scheme,
                family: family,
                foundation: foundation,
            )
        }
    }

    mutating func define(_ constant: String, by axiom: String) throws {
        guard var d = declarations[constant] else { throw MalformedExport.undeclaredConstant(constant) }
        guard leaves[constant] == nil, primitives[constant] == nil else { throw MalformedExport.definedLeaf(constant) }
        guard
            d.definition == nil,
            definitions[axiom] == nil
        else { throw MalformedExport.duplicateDefinition(constant) }
        d.definition = axiom
        declarations[constant] = d
        definitions[axiom] = Defined(d.family, constant, d.scheme.level)
    }

    func reading(_ name: String) throws -> Reading {
        if let r = leaves[name] { return r }
        guard let d = declarations[name] else { throw MalformedExport.undeclaredConstant(name) }
        if d.definition != nil { return .constant(.defined(Defined(d.family, name, d.scheme.level))) }
        if let p = primitives[name] { return .constant(.primitive(p)) }
        guard !d.foundation else { throw DialectGap.leaf(name) }
        return .constant(.declared(name))
    }

    func instantiate(_ name: String, _ arguments: [IsaType]) throws -> IsaType {
        guard let d = declarations[name] else { throw MalformedExport.undeclaredConstant(name) }
        guard arguments.count == d.parameters.count else {
            throw MalformedExport.typeArgumentCount(
                constant: name,
                declared: d.parameters.count,
                found: arguments.count,
            )
        }
        return d.scheme.substituting(Dictionary(uniqueKeysWithValues: zip(d.parameters, arguments)))
    }

    private var declarations = [String: Declaration]()
    private var definitions = [String: Defined]()

}
