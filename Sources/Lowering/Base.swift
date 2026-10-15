import IR

@frozen public enum BaseStatement: String, CaseIterable, Hashable, Sendable {
    case iffRefl = "iff_refl", iffSymm = "iff_symm", iffTrans = "iff_trans"
    case congNot = "cong_not", congAnd = "cong_and", congOr = "cong_or", congImp = "cong_imp", congIff = "cong_iff"
    case eqRefl = "eq_refl", eqSymm = "eq_symm", eqTrans = "eq_trans"
    case congElemL = "cong_elem_l", congElemR = "cong_elem_r", congEqL = "cong_eq_l", congEqR = "cong_eq_r"
    case congSnocV = "cong_snoc_v"
}

@frozen public enum BaseError: Error, Equatable, Sendable {
    case missing(String)
}

public struct Base {
    private let statements: [BaseStatement: NodeID]

    public init(_ parsed: [String: NodeID]) throws {
        var statements: [BaseStatement: NodeID] = [:]
        for s in BaseStatement.allCases {
            guard let root = parsed[s.rawValue] else { throw BaseError.missing(s.rawValue) }
            statements[s] = root
        }
        self.statements = statements
    }

    public func cite(_ s: BaseStatement, in t: inout Table) throws -> NodeID {
        guard let root = statements[s] else { throw BaseError.missing(s.rawValue) }
        return try t.intern(.use(.base(s.rawValue), [], root))
    }

    func instance(_ s: BaseStatement, _ letters: [NodeID], in t: inout Table) throws -> NodeID {
        var step = try cite(s, in: &t)
        for a in letters { step = try t.intern(.folSchemaInst(step, a)) }
        return step
    }

    func claimed(_ s: BaseStatement, _ variables: [NodeID], _ premises: [NodeID], in t: inout Table) throws -> NodeID {
        var step = try cite(s, in: &t)
        for v in variables { step = try t.intern(.folForallElim(step, v)) }
        for p in premises { step = try t.intern(.folImpliesElim(step, p)) }
        return step
    }

    func applied(_ s: BaseStatement, _ letters: [NodeID], _ premises: [NodeID], in t: inout Table) throws -> NodeID {
        var step = try instance(s, letters, in: &t)
        for p in premises { step = try t.intern(.folImpliesElim(step, p)) }
        return step
    }
}
