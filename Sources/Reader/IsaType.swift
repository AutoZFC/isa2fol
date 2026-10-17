import IR

indirect enum IsaType: Hashable, Sendable {
    case type(String, [IsaType])
    case tfree(String, sort: [String])
    case tvar(String, index: Int, sort: [String])

    var variables: Set<IsaType> {
        switch self {
        case .type(_, let args): args.reduce(into: []) { $0.formUnion($1.variables) }
        case .tfree, .tvar: [self]
        }
    }

    var level: Level {
        switch self {
        case .type(let name, let args): name == "prop" || args.contains { $0.level == .meta } ? .meta : .object
        case .tfree, .tvar: .meta
        }
    }

    func substituting(_ s: [String: IsaType]) -> IsaType {
        switch self {
        case .type(let name, let args): .type(name, args.map { $0.substituting(s) })
        case .tfree(let name, _): s[name] ?? self
        case .tvar: self
        }
    }

    func irType() throws -> IRType {
        switch self {
        case .type("fun", let args):
            try arity("fun", args, 2)
            return .fn(try args[0].irType(), try args[1].irType())

        case .type("ZF_Base.i", let args):
            try arity("ZF_Base.i", args, 0)
            return .i

        case .type("dummy", let args):
            try arity("dummy", args, 0)
            return .variable("dummy")

        case .type(let name, let args) where name == "IFOL.o" || name == "prop":
            try arity(name, args, 0)
            return .o

        case .type(let name, _):
            throw ReaderRefusal.typeConstructor(name)

        case .tfree(let name, let sort):
            guard sort.isEmpty else { throw MalformedExport.sortedTypeVariable(name) }
            return .variable(name)

        case .tvar(let name, _, _):
            throw MalformedExport.schematicVariable(name)
        }
    }
}

extension Decode {
    func type(_ body: Body) throws -> IsaType {
        try variant([
            { atoms, ts in .type(try one(atoms), try list(type, ts)) },
            { atoms, ts in .tfree(try one(atoms), sort: try list(string, ts)) },
            { atoms, ts in
                let (name, index) = try indexname(atoms)
                return .tvar(name, index: index, sort: try list(string, ts))
            },
        ], body)
    }
}

private func arity(_ name: String, _ args: [IsaType], _ n: Int) throws {
    guard args.count == n else { throw MalformedExport.constructorArity(name, args.count) }
}
