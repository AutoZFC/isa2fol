@frozen
public enum Family: String, Hashable, Sendable, CustomStringConvertible {
    case pure
    case ifol
    case fol
    case zf

    public var description: String {
        rawValue
    }
}

@frozen
public enum Primitive: Hashable, Sendable, CustomStringConvertible {
    case pure(Pure)
    case ifol(IFOL)
    case zf(ZF)

    @frozen
    public enum Pure: String, Hashable, Sendable, CaseIterable {
        case eq = "Pure.eq"
    }

    @frozen
    public enum IFOL: String, Hashable, Sendable, CaseIterable {
        case eq = "IFOL.eq"
    }

    @frozen
    public enum ZF: String, Hashable, Sendable, CaseIterable {
        case mem = "ZF_Base.mem"
        case zero = "ZF_Base.zero"
        case pow = "ZF_Base.Pow"
        case union = "ZF_Base.Union"
        case primReplace = "ZF_Base.PrimReplace"
        case inf = "ZF_Base.Inf"
    }

    public static let all = Pure.allCases.map(pure) + IFOL.allCases.map(ifol) + ZF.allCases.map(zf)

    public var name: String {
        switch self {
        case .pure(let p): p.rawValue
        case .ifol(let p): p.rawValue
        case .zf(let p): p.rawValue
        }
    }

    public var description: String {
        name
    }
}

@frozen
public enum Level: String, Hashable, Sendable, CustomStringConvertible {
    case object
    case meta

    public var description: String {
        rawValue
    }
}

public struct Defined: Hashable, Sendable {
    public init(_ family: Family, _ name: String, _ level: Level) {
        self.family = family
        self.name = name
        self.level = level
    }

    public let family: Family
    public let name: String
    public let level: Level

}

public struct TypeClass: Hashable, Sendable, CustomStringConvertible {
    public init(_ family: Family, _ name: String) {
        self.family = family
        self.name = name
    }

    public let family: Family
    public let name: String

    public var description: String {
        name
    }
}

@frozen
public enum Definiendum: Hashable, Sendable, CustomStringConvertible {
    case constant(Defined)
    case ofClass(TypeClass)

    public var family: Family {
        switch self {
        case .constant(let d): d.family
        case .ofClass(let c): c.family
        }
    }

    public var level: Level {
        switch self {
        case .constant(let d): d.level
        case .ofClass: .meta
        }
    }

    public var name: String {
        switch self {
        case .constant(let d): d.name
        case .ofClass(let c): c.name
        }
    }

    public var description: String {
        name
    }
}

@frozen
public enum Constant: Hashable, Sendable {
    case primitive(Primitive)
    case defined(Defined)
    case declared(String)

    public var name: String {
        switch self {
        case .primitive(let p): p.name
        case .defined(let d): d.name
        case .declared(let name): name
        }
    }
}

@frozen
public enum Axiom: Hashable, Sendable, CustomStringConvertible {
    case ifol(IFOL)
    case fol(FOL)
    case zf(ZF)

    @frozen
    public enum IFOL: String, Hashable, Sendable, CaseIterable {
        case refl = "IFOL.refl"
        case subst = "IFOL.subst"
        case impI = "IFOL.impI"
        case mp = "IFOL.mp"
        case conjI = "IFOL.conjI"
        case conjunct1 = "IFOL.conjunct1"
        case conjunct2 = "IFOL.conjunct2"
        case disjI1 = "IFOL.disjI1"
        case disjI2 = "IFOL.disjI2"
        case disjE = "IFOL.disjE"
        case falseE = "IFOL.FalseE"
        case allI = "IFOL.allI"
        case spec = "IFOL.spec"
        case exI = "IFOL.exI"
        case exE = "IFOL.exE"
        case eqReflection = "IFOL.eq_reflection"
        case iffReflection = "IFOL.iff_reflection"
    }

    @frozen
    public enum FOL: String, Hashable, Sendable, CaseIterable {
        case classical = "FOL.classical"
    }

    @frozen
    public enum ZF: String, Hashable, Sendable, CaseIterable {
        case `extension` = "ZF_Base.extension"
        case replacement = "ZF_Base.replacement"
        case powIff = "ZF_Base.Pow_iff"
        case unionIff = "ZF_Base.Union_iff"
        case foundation = "ZF_Base.foundation"
        case infinity = "ZF_Base.infinity"
        case choice = "AC.AC"
    }

    public static let all = IFOL.allCases.map(ifol) + FOL.allCases.map(fol) + ZF.allCases.map(zf)

    public var family: Family {
        switch self {
        case .ifol: .ifol
        case .fol: .fol
        case .zf: .zf
        }
    }

    public var name: String {
        switch self {
        case .ifol(let a): a.rawValue
        case .fol(let a): a.rawValue
        case .zf(let a): a.rawValue
        }
    }

    public var description: String {
        name
    }
}

@frozen
public enum Cited: Hashable, Sendable {
    case theorem(String)
    case axiom(Axiom)
    case theoryAxiom(String)
    case lemma(Lemma)
    case base(String)
    case definition(Defined)

    public var name: String {
        switch self {
        case .theorem(let name), .theoryAxiom(let name), .base(let name): name
        case .axiom(let a): a.name
        case .lemma(let l): l.name
        case .definition(let c): c.definitionName
        }
    }
}

public protocol Request: Hashable, Sendable {
    var name: String { get }

    func remapped(_ f: (NodeID) throws -> NodeID) rethrows -> Self
}

public struct Lemma: Hashable, Sendable, CustomStringConvertible {
    public init(_ request: some Request) {
        self.request = request
    }

    public let request: any Request

    public var name: String {
        request.name
    }

    public var description: String {
        name
    }

    public static func ==(a: Lemma, b: Lemma) -> Bool {
        AnyHashable(a.request) == AnyHashable(b.request)
    }

    public func hash(into h: inout Hasher) {
        AnyHashable(request).hash(into: &h)
    }
}
