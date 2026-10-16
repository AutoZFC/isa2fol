import IR

@frozen public enum BaseStatement: String, CaseIterable, Hashable, Sendable {
    case iffRefl = "iff_refl", iffSymm = "iff_symm", iffTrans = "iff_trans"
    case truthEX = "truth_EX", weaken
    case congNot = "cong_not", congAnd = "cong_and", congOr = "cong_or", congImp = "cong_imp", congIff = "cong_iff"
    case eqRefl = "eq_refl", eqSymm = "eq_symm", eqTrans = "eq_trans", classSubst = "class_subst"
    case congElemL = "cong_elem_l", congElemR = "cong_elem_r", congEqL = "cong_eq_l", congEqR = "cong_eq_r"
    case congSnocV = "cong_snoc_v"
    case zeroEX = "zero_EX", zeroUNIQ = "zero_UNIQ", zeroDef = "zero_def"
    case nsuccEX = "nsucc_EX", nsuccUNIQ = "nsucc_UNIQ", nsuccCONG = "nsucc_CONG"
    case snocEX = "snoc_EX", snocUNIQ = "snoc_UNIQ", snocCONG = "snoc_CONG", snocInj = "snoc_inj", snocResCong = "snoc_res_cong"
    case tupleZero = "tuple_zero", tupleSnoc = "tuple_snoc"
    case functionDef = "function_def", applyEX = "apply_EX", applyAt = "apply_at", applyClassCong = "apply_class_cong"
    case funcAt = "func_at", extensionality
    case zfZeroEX = "ZF_Base.zero_EX", zfZeroUNIQ = "ZF_Base.zero_UNIQ", zfInfEX = "ZF_Base.Inf_EX", zfInfUNIQ = "ZF_Base.Inf_UNIQ"
    case zfPowDef = "ZF_Base.Pow_def", zfUnionDef = "ZF_Base.Union_def", zfPrimReplaceDef = "ZF_Base.PrimReplace_def"
    case zfPrimReplaceValue = "ZF_Base.PrimReplace_value"
    case powEX = "Pow_EX", powUNIQ = "Pow_UNIQ", powCONG = "Pow_CONG"
    case unionEX = "Union_EX", unionUNIQ = "Union_UNIQ", unionCONG = "Union_CONG"
    case congExists = "cong_exists", congForall = "cong_forall", congExistsBare = "cong_exists_bare", congForallBare = "cong_forall_bare"
    case forallAsNexists = "forall_as_nexists"
    case read1, read2, read4
    case b1 = "B1", b2 = "B2", b3 = "B3", bOr = "B_or", bIff = "B_iff", rowEx = "row_ex"
    case clsZero = "cls_zero", clsNsucc = "cls_nsucc", clsSnoc4 = "cls_snoc4", clsDiag = "cls_diag", rsKey = "rs_key"
    case clsApply = "cls_apply"
    case snocSome = "snoc_some", snocKeep = "snoc_keep", snocNew = "snoc_new"
    case memberClass = "member_class", graphClass = "graph_class"
    case impAsNand = "imp_as_nand", orIdem = "or_idem"
    case powDef = "Pow_def", unionDef = "Union_def"
    case upairEx = "upair_ex", upairDef = "upair_def"
    case applyDef = "apply_def", lamPred = "lam_pred", lamClass = "lam_class", snocEQ = "snoc_EQ", tuplesClass = "tuples_class"
    case zfZeroDef = "ZF_Base.zero_def", zfInfDef = "ZF_Base.Inf_def", infDef = "Inf_def", indDef = "ind_def"
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
