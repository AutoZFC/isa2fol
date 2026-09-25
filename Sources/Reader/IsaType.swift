import IR

indirect enum IsaType: Hashable, Sendable {
    case type(String, [IsaType])
    case tfree(String, sort: [String])
    case tvar(String, index: Int, sort: [String])

    var variables: Set<IsaType> {
        switch self {
        case let .type(_, args): return args.reduce(into: []) { $0.formUnion($1.variables) }
        case .tfree, .tvar: return [self]
        }
    }

    func substituting(_ s: [String: IsaType]) -> IsaType {
        switch self {
        case let .type(name, args): return .type(name, args.map { $0.substituting(s) })
        case let .tfree(name, _): return s[name] ?? self
        case .tvar: return self
        }
    }

    func irType() throws -> IRType {
        switch self {
        case let .type("fun", args):
            try arity("fun", args, 2)
            return .fn(try args[0].irType(), try args[1].irType())
        case let .type("ZF_Base.i", args):
            try arity("ZF_Base.i", args, 0)
            return .i
        case let .type(name, args) where name == "IFOL.o" || name == "prop":
            try arity(name, args, 0)
            return .o
        case let .type(name, _):
            throw ReaderRefusal.typeConstructor(name)
        case let .tfree(name, _), let .tvar(name, _, _):
            throw ReaderRefusal.typeVariable(name)
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
