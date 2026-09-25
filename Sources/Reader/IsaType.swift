import IR

indirect enum IsaType: Hashable, Sendable {
    case type(String, [IsaType])
    case tfree(String, sort: [String])
    case tvar(String, index: Int, sort: [String])

    init(_ body: Body) throws {
        self = try Decode.variant([
            { atoms, ts in .type(try one(atoms), try Decode.list(IsaType.init, ts)) },
            { atoms, ts in .tfree(try one(atoms), sort: try Decode.list(Decode.string, ts)) },
            { atoms, ts in
                let (name, index) = try indexname(atoms)
                return .tvar(name, index: index, sort: try Decode.list(Decode.string, ts))
            },
        ], body)
    }

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
        case let .type("IFOL.o", args):
            try arity("IFOL.o", args, 0)
            return .o
        case let .type("prop", args):
            try arity("prop", args, 0)
            throw ReaderRefusal.prop
        case let .type(name, _):
            throw ReaderRefusal.typeConstructor(name)
        case let .tfree(name, _), let .tvar(name, _, _):
            throw ReaderRefusal.typeVariable(name)
        }
    }
}

private func one(_ atoms: [String]) throws -> String {
    guard atoms.count == 1 else { throw MalformedExport.atoms(atoms) }
    return atoms[0]
}

private func indexname(_ atoms: [String]) throws -> (String, Int) {
    if atoms.count == 1 { return (atoms[0], 0) }
    guard atoms.count == 2 else { throw MalformedExport.atoms(atoms) }
    return (atoms[0], try Decode.int(atoms[1]))
}

private func arity(_ name: String, _ args: [IsaType], _ n: Int) throws {
    guard args.count == n else { throw MalformedExport.constructorArity(name, args.count) }
}
