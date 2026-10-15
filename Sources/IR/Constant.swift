@frozen public enum Family: String, Hashable, Sendable, CustomStringConvertible {
    case pure, ifol, fol, zf

    public var description: String { rawValue }
}

@frozen public enum Primitive: Hashable, Sendable, CustomStringConvertible {
    case pure(Pure)
    case ifol(IFOL)
    case zf(ZF)

    @frozen public enum Pure: String, Hashable, Sendable, CaseIterable {
        case eq = "Pure.eq"
    }

    @frozen public enum IFOL: String, Hashable, Sendable, CaseIterable {
        case eq = "IFOL.eq"
    }

    @frozen public enum ZF: String, Hashable, Sendable, CaseIterable {
        case mem = "ZF_Base.mem", zero = "ZF_Base.zero", pow = "ZF_Base.Pow", union = "ZF_Base.Union"
        case primReplace = "ZF_Base.PrimReplace", inf = "ZF_Base.Inf"
    }

    public static let all = Pure.allCases.map(pure) + IFOL.allCases.map(ifol) + ZF.allCases.map(zf)

    public var name: String {
        switch self {
        case let .pure(p): return p.rawValue
        case let .ifol(p): return p.rawValue
        case let .zf(p): return p.rawValue
        }
    }

    public var description: String { name }
}

@frozen public enum Level: String, Hashable, Sendable, CustomStringConvertible {
    case object, meta

    public var description: String { rawValue }
}

public struct Defined: Hashable, Sendable {
    public let family: Family
    public let name: String
    public let level: Level

    public init(_ family: Family, _ name: String, _ level: Level) {
        self.family = family
        self.name = name
        self.level = level
    }
}

@frozen public enum Constant: Hashable, Sendable {
    case primitive(Primitive)
    case defined(Defined)
    case declared(String)

    public var name: String {
        switch self {
        case let .primitive(p): return p.name
        case let .defined(d): return d.name
        case let .declared(name): return name
        }
    }
}

@frozen public enum Axiom: Hashable, Sendable, CustomStringConvertible {
    case ifol(IFOL)
    case fol(FOL)
    case zf(ZF)

    @frozen public enum IFOL: String, Hashable, Sendable, CaseIterable {
        case refl = "IFOL.refl", subst = "IFOL.subst", impI = "IFOL.impI", mp = "IFOL.mp"
        case conjI = "IFOL.conjI", conjunct1 = "IFOL.conjunct1", conjunct2 = "IFOL.conjunct2"
        case disjI1 = "IFOL.disjI1", disjI2 = "IFOL.disjI2", disjE = "IFOL.disjE", falseE = "IFOL.FalseE"
        case allI = "IFOL.allI", spec = "IFOL.spec", exI = "IFOL.exI", exE = "IFOL.exE"
        case eqReflection = "IFOL.eq_reflection", iffReflection = "IFOL.iff_reflection"
    }

    @frozen public enum FOL: String, Hashable, Sendable, CaseIterable {
        case classical = "FOL.classical"
    }

    @frozen public enum ZF: String, Hashable, Sendable, CaseIterable {
        case `extension` = "ZF_Base.extension", replacement = "ZF_Base.replacement"
        case powIff = "ZF_Base.Pow_iff", unionIff = "ZF_Base.Union_iff"
        case foundation = "ZF_Base.foundation", infinity = "ZF_Base.infinity", choice = "AC.AC"
    }

    public static let all = IFOL.allCases.map(ifol) + FOL.allCases.map(fol) + ZF.allCases.map(zf)

    public var family: Family {
        switch self {
        case .ifol: return .ifol
        case .fol: return .fol
        case .zf: return .zf
        }
    }

    public var name: String {
        switch self {
        case let .ifol(a): return a.rawValue
        case let .fol(a): return a.rawValue
        case let .zf(a): return a.rawValue
        }
    }

    public var description: String { name }
}

@frozen public enum Cited: Hashable, Sendable {
    case theorem(String)
    case isaDefinition(String, of: Defined)
    case axiom(Axiom)
    case theoryAxiom(String)
    case lemma(Lemma)
    case base(String)

    public var name: String {
        switch self {
        case let .theorem(name), let .isaDefinition(name, _), let .theoryAxiom(name), let .base(name): return name
        case let .axiom(a): return a.name
        case let .lemma(l): return l.name
        }
    }
}

public protocol Request: Hashable, Sendable {
    var name: String { get }
}

public struct Lemma: Hashable, Sendable, CustomStringConvertible {
    public let request: any Request

    public init(_ request: some Request) { self.request = request }

    public var name: String { request.name }
    public var description: String { name }

    public static func == (a: Lemma, b: Lemma) -> Bool { AnyHashable(a.request) == AnyHashable(b.request) }
    public func hash(into h: inout Hasher) { AnyHashable(request).hash(into: &h) }
}
