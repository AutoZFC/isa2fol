import IR
import YXML

enum Head {
    case constant(String, [IsaType])
    case free(String, IsaType?)
    case schematic(String)
    case bound(Int)
    case abstraction(IsaType, Body)
    case ofclass(String)
}

private enum Term {
    case head(Head)
    case application(Body, Body)
}

extension Decode {
    func spine(_ body: Body) throws -> (head: Head, arguments: [Body]) {
        switch try term(body) {
        case let .head(h):
            return (h, [])
        case let .application(f, x):
            let (h, arguments) = try spine(f)
            return (h, arguments + [x])
        }
    }

    private func term(_ body: Body) throws -> Term {
        try variant([
            { a, ts in .head(.constant(try one(a), try list(type, ts))) },
            { a, ts in .head(.free(try one(a), try variableType(ts))) },
            { a, ts in
                _ = try variableType(ts)
                return .head(.schematic(try indexname(a).0))
            },
            { a, ts in
                try noAtoms(a)
                return .head(.bound(try Decode.int(try string(ts))))
            },
            { a, ts in
                _ = try one(a)
                let (T, inner) = try pair(type, { $0 }, ts)
                return .head(.abstraction(T, inner))
            },
            { a, ts in
                try noAtoms(a)
                let (f, x) = try pair({ $0 }, { $0 }, ts)
                return .application(f, x)
            },
            { a, ts in
                _ = try type(ts)
                return .head(.ofclass(try one(a)))
            },
        ], body)
    }

    private func variableType(_ ts: Body) throws -> IsaType? {
        ts.isEmpty ? nil : try type(ts)
    }
}

struct Scope: Hashable {
    private struct Binder: Hashable {
        let type: IRType
        let level: Int
    }

    private var binders: [Binder] = []
    private(set) var depth: Int

    init(frees: Int) { depth = frees }

    func source(_ T: IRType) -> Scope {
        var s = self
        s.binders.append(Binder(type: T, level: depth))
        s.depth += 1
        return s
    }

    func eta() -> Scope {
        var s = self
        s.depth += 1
        return s
    }

    func bound(_ k: Int) throws -> (index: Int, type: IRType) {
        guard k >= 0, k < binders.count else { throw MalformedExport.unboundBound(k) }
        let b = binders[binders.count - 1 - k]
        return (depth - 1 - b.level, b.type)
    }
}

private enum Argument {
    case source(Body)
    case decoded(NodeID)
}

private enum Connective {
    case erased, implies, and, or, iff, not, bottom, metaEquality, all, ex
}

private let connectives: [String: Connective] = [
    "IFOL.Trueprop": .erased, "Pure.prop": .erased,
    "Pure.imp": .implies, "IFOL.imp": .implies,
    "IFOL.conj": .and, "IFOL.disj": .or, "IFOL.iff": .iff, "IFOL.Not": .not, "IFOL.False": .bottom,
    "Pure.eq": .metaEquality,
    "IFOL.All": .all, "IFOL.Ex": .ex, "Pure.all": .all,
]

struct Terms {
    private struct Memo: Hashable {
        let body: Body
        let type: IRType
        let scope: Scope
    }

    let decode: Decode
    let constants: Constants
    private let types: [String: IsaType]
    private let frees: [String: (level: Int, type: IRType)]
    private let freeTypes: [IRType]
    private var memo: [Memo: NodeID] = [:]

    init(decode: Decode, constants: Constants, file e: Envelope, at instance: [IsaType]) throws {
        guard instance.count == e.tfrees.count else {
            throw MalformedExport.instanceArity(expected: e.tfrees.count, found: instance.count)
        }
        let names = e.frees.map(\.0)
        let occurring = try decode.frees(e.prop)
        guard occurring == names else { throw MalformedExport.freesHeader(header: names, occurring: occurring) }
        self.decode = decode
        self.constants = constants
        let types = Dictionary(uniqueKeysWithValues: zip(e.tfrees, instance))
        let typed = try e.frees.map { ($0.0, try $0.1.substituting(types).irType()) }
        self.types = types
        freeTypes = typed.map(\.1)
        frees = Dictionary(uniqueKeysWithValues: typed.enumerated().map { ($0.element.0, (level: $0.offset, type: $0.element.1)) })
    }

    var closure: Scope { Scope(frees: freeTypes.count) }

    func close(_ n: NodeID, _ binder: (IRType, NodeID) -> Node, in t: inout Table) throws -> NodeID {
        try freeTypes.reversed().reduce(n) { body, T in try t.intern(binder(T, body)) }
    }

    func instance(_ T: IsaType) throws -> IsaType {
        let ground = T.substituting(types)
        _ = try ground.irType()
        return ground
    }

    func irType(_ T: IsaType) throws -> IRType { try T.substituting(types).irType() }

    mutating func proposition(_ body: Body, _ s: Scope, in t: inout Table) throws -> NodeID {
        try source(body, .o, s, &t)
    }

    mutating func term(_ body: Body, _ U: IRType, _ s: Scope, in t: inout Table) throws -> NodeID {
        try source(body, U, s, &t)
    }

    private mutating func source(_ body: Body, _ U: IRType, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let key = Memo(body: body, type: U, scope: s)
        if let n = memo[key] { return n }
        let n = try applied(body, [], U, s, &t)
        memo[key] = n
        return n
    }

    private mutating func argument(_ a: Argument, _ U: IRType, _ s: Scope, _ t: inout Table) throws -> NodeID {
        switch a {
        case let .source(body): return try source(body, U, s, &t)
        case let .decoded(n): return n
        }
    }

    private mutating func applied(_ body: Body, _ extra: [NodeID], _ U: IRType, _ s: Scope, _ t: inout Table) throws -> NodeID {
        guard case let .fn(T, rest) = U else { return try spine(body, extra, U, s, &t) }
        return try t.intern(.isaAbs(T, body: try abstraction(body, extra, T, rest, s, &t)))
    }

    private mutating func abstraction(_ body: Body, _ extra: [NodeID], _ T: IRType, _ rest: IRType,
                                      _ s: Scope, _ t: inout Table) throws -> NodeID {
        if extra.isEmpty, case let (domain, inner)? = try lambda(body) {
            let D = try irType(domain)
            guard D == T else { throw MalformedExport.typeMismatch(expected: T, found: D) }
            return try source(inner, rest, s.source(T), &t)
        }
        let y = try etaLong(try t.intern(.isaBound(0, T)), [], T, &t)
        let shifted = try extra.map { try shift($0, by: 1, in: &t) }
        return try applied(body, shifted + [y], rest, s.eta(), &t)
    }

    private func etaLong(_ v: NodeID, _ args: [NodeID], _ U: IRType, _ t: inout Table) throws -> NodeID {
        guard case let .fn(T, rest) = U else { return args.isEmpty ? v : try t.intern(.isaVarApp(head: v, args: args)) }
        let y = try etaLong(try t.intern(.isaBound(0, T)), [], T, &t)
        let shifted = try args.map { try shift($0, by: 1, in: &t) }
        return try t.intern(.isaAbs(T, body: try etaLong(try shift(v, by: 1, in: &t), shifted + [y], rest, &t)))
    }

    private func lambda(_ body: Body) throws -> (IsaType, Body)? {
        let (head, arguments) = try decode.spine(body)
        guard arguments.isEmpty, case let .abstraction(domain, inner) = head else { return nil }
        return (domain, inner)
    }

    private mutating func spine(_ body: Body, _ extra: [NodeID], _ U: IRType, _ s: Scope, _ t: inout Table) throws -> NodeID {
        let (head, sources) = try decode.spine(body)
        let arguments = sources.map(Argument.source) + extra.map(Argument.decoded)
        let n: NodeID
        switch head {
        case let .constant(name, types):
            n = try constant(name, types, arguments, s, &t)
        case let .free(name, declared):
            guard let f = frees[name] else { throw MalformedExport.undeclaredFree(name) }
            if let declared, try irType(declared) != f.type {
                throw MalformedExport.typeMismatch(expected: f.type, found: try irType(declared))
            }
            n = try variable(name, try t.intern(.isaBound(s.depth - 1 - f.level, f.type)), f.type, arguments, s, &t)
        case let .bound(k):
            let (index, T) = try s.bound(k)
            n = try variable("ZBound \(k)", try t.intern(.isaBound(index, T)), T, arguments, s, &t)
        case .abstraction:
            guard arguments.isEmpty else { throw ReaderRefusal.betaRedex }
            throw MalformedExport.unexpectedAbstraction(expected: U)
        case let .schematic(name):
            throw MalformedExport.schematicVariable(name)
        case let .ofclass(c):
            throw ReaderRefusal.ofclass(c)
        }
        let found = t.type(of: n)
        guard found == U else { throw MalformedExport.typeMismatch(expected: U, found: found) }
        return n
    }

    private mutating func variable(_ name: String, _ head: NodeID, _ T: IRType, _ arguments: [Argument],
                                   _ s: Scope, _ t: inout Table) throws -> NodeID {
        if arguments.isEmpty { return head }
        return try t.intern(.isaVarApp(head: head, args: try operands(name, T.domains, arguments, s, &t)))
    }

    private mutating func operands(_ name: String, _ domains: [IRType], _ arguments: [Argument],
                                   _ s: Scope, _ t: inout Table) throws -> [NodeID] {
        guard arguments.count == domains.count else {
            throw MalformedExport.applicationArity(name, expected: domains.count, found: arguments.count)
        }
        return try zip(arguments, domains).map { try argument($0, $1, s, &t) }
    }

    private mutating func constant(_ name: String, _ types: [IsaType], _ arguments: [Argument],
                                   _ s: Scope, _ t: inout Table) throws -> NodeID {
        let scheme = try constants.instantiate(name, types.map { $0.substituting(self.types) })
        guard let c = connectives[name] else {
            let T = try scheme.irType()
            return try t.intern(.isaConst(name, T, args: try operands(name, T.domains, arguments, s, &t)))
        }
        switch c {
        case .bottom:
            _ = try operands(name, [], arguments, s, &t)
            return try t.intern(.folBottom)
        case .erased:
            return try operands(name, [.o], arguments, s, &t)[0]
        case .not:
            return try t.intern(.folNot(try operands(name, [.o], arguments, s, &t)[0]))
        case .implies:
            let ab = try operands(name, [.o, .o], arguments, s, &t)
            return try t.intern(.folImplies(ab[0], ab[1]))
        case .and:
            let ab = try operands(name, [.o, .o], arguments, s, &t)
            return try t.intern(.folAnd(ab[0], ab[1]))
        case .or:
            let ab = try operands(name, [.o, .o], arguments, s, &t)
            return try t.intern(.folOr(ab[0], ab[1]))
        case .iff:
            let ab = try operands(name, [.o, .o], arguments, s, &t)
            return try t.intern(.folIff(ab[0], ab[1]))
        case .metaEquality:
            let T = try irType(try typeArgument(name, types))
            let ab = try operands(name, [T, T], arguments, s, &t)
            switch T {
            case .o: return try t.intern(.folIff(ab[0], ab[1]))
            case .i: return try t.intern(.isaConst("IFOL.eq", .fn(.i, .fn(.i, .o)), args: ab))
            case .fn: return try t.intern(.isaConst("Pure.eq", .fn(T, .fn(T, .o)), args: ab))
            }
        case .all:
            let T = try irType(try typeArgument(name, types))
            return try t.intern(.ifolAll(T, body: try binder(name, T, arguments, s, &t)))
        case .ex:
            let T = try irType(try typeArgument(name, types))
            return try t.intern(.ifolEx(T, body: try binder(name, T, arguments, s, &t)))
        }
    }

    private mutating func binder(_ name: String, _ T: IRType, _ arguments: [Argument], _ s: Scope, _ t: inout Table) throws -> NodeID {
        guard arguments.count == 1 else { throw MalformedExport.applicationArity(name, expected: 1, found: arguments.count) }
        switch arguments[0] {
        case let .source(body):
            return try abstraction(body, [], T, .o, s, &t)
        case let .decoded(n):
            guard case let .isaAbs(D, body) = t[n], D == T else {
                throw MalformedExport.typeMismatch(expected: .fn(T, .o), found: t.type(of: n))
            }
            return body
        }
    }

    private func typeArgument(_ name: String, _ types: [IsaType]) throws -> IsaType {
        guard types.count == 1 else { throw MalformedExport.typeArgumentCount(constant: name, declared: 1, found: types.count) }
        return types[0]
    }
}

extension IRType {
    var domains: [IRType] {
        guard case let .fn(T, rest) = self else { return [] }
        return [T] + rest.domains
    }
}
