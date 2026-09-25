import YXML

struct Constants {
    struct Declaration: Equatable {
        let parameters: [String]
        let scheme: IsaType
    }

    private var declarations: [String: Declaration] = [:]

    subscript(_ name: String) -> Declaration? { declarations[name] }

    mutating func load(_ file: YXML.Node) throws {
        for entity in file.children {
            guard entity.tag == "entity" else { throw MalformedExport.notAnEntity(tag: entity.tag) }
            let name = try entity.attribute("name")
            let (_, rest) = try Decode.pair({ $0 }, { $0 }, entity.children)
            let (parameters, typed) = try Decode.pair({ try Decode.list(Decode.string, $0) }, { $0 }, rest)
            let (scheme, _) = try Decode.pair(IsaType.init, { $0 }, typed)
            guard parameters.count == Set(parameters).count,
                  scheme.variables == Set(parameters.map { IsaType.tfree($0, sort: []) }) else {
                throw MalformedExport.schemeVariables(constant: name)
            }
            guard declarations[name] == nil else { throw MalformedExport.duplicateConstant(name) }
            declarations[name] = Declaration(parameters: parameters, scheme: scheme)
        }
    }

    func instantiate(_ name: String, _ arguments: [IsaType]) throws -> IsaType {
        guard let d = declarations[name] else { throw MalformedExport.undeclaredConstant(name) }
        guard arguments.count == d.parameters.count else {
            throw MalformedExport.typeArgumentCount(constant: name, declared: d.parameters.count, found: arguments.count)
        }
        return d.scheme.substituting(Dictionary(uniqueKeysWithValues: zip(d.parameters, arguments)))
    }
}
