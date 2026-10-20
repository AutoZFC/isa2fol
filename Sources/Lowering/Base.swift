import IR

@frozen
public enum BaseStatement: String, CaseIterable, Hashable, Sendable {
    case iffRefl = "iff_refl"
    case iffSymm = "iff_symm"
    case iffTrans = "iff_trans"
    case truthEX = "truth_EX"
    case truthSetEX = "truth_set_EX"
    case truthUNIQ = "truth_UNIQ"
    case truthOfSet = "truth_of_set"
    case holdsDef = "holds_def"
    case congHolds = "cong_holds"
    case weaken
    case congNot = "cong_not"
    case congAnd = "cong_and"
    case congOr = "cong_or"
    case congImp = "cong_imp"
    case congIff = "cong_iff"
    case eqRefl = "eq_refl"
    case eqSymm = "eq_symm"
    case eqTrans = "eq_trans"
    case classSubst = "class_subst"
    case congElemL = "cong_elem_l"
    case congElemR = "cong_elem_r"
    case congEqL = "cong_eq_l"
    case congEqR = "cong_eq_r"
    case congSnocV = "cong_snoc_v"
    case congUnionL = "cong_Union_l"
    case congPowL = "cong_Pow_l"
    case zeroEX = "zero_EX"
    case setInhabited = "set_inhabited"
    case truthInhabited = "truth_inhabited"
    case zeroUNIQ = "zero_UNIQ"
    case zeroDef = "zero_def"
    case nsuccEX = "nsucc_EX"
    case nsuccUNIQ = "nsucc_UNIQ"
    case nsuccCONG = "nsucc_CONG"
    case snocEX = "snoc_EX"
    case snocUNIQ = "snoc_UNIQ"
    case snocCONG = "snoc_CONG"
    case snocInj = "snoc_inj"
    case snocResCong = "snoc_res_cong"
    case tupleZero = "tuple_zero"
    case tupleSnoc = "tuple_snoc"
    case functionDef = "function_def"
    case applyEX = "apply_EX"
    case applyAt = "apply_at"
    case applyClassCong = "apply_class_cong"
    case applyPmem = "apply_pmem"
    case funcAt = "func_at"
    case extensionality
    case zfZeroEX = "ZF_Base.zero_EX"
    case zfZeroUNIQ = "ZF_Base.zero_UNIQ"
    case zfInfEX = "ZF_Base.Inf_EX"
    case zfInfUNIQ = "ZF_Base.Inf_UNIQ"
    case zfPowDef = "ZF_Base.Pow_def"
    case zfUnionDef = "ZF_Base.Union_def"
    case zfPrimReplaceDef = "ZF_Base.PrimReplace_def"
    case zfPrimReplaceValue = "ZF_Base.PrimReplace_value"
    case powEX = "Pow_EX"
    case powUNIQ = "Pow_UNIQ"
    case powCONG = "Pow_CONG"
    case unionEX = "Union_EX"
    case unionUNIQ = "Union_UNIQ"
    case unionCONG = "Union_CONG"
    case congExists = "cong_exists"
    case congForall = "cong_forall"
    case congExistsBare = "cong_exists_bare"
    case congForallBare = "cong_forall_bare"
    case monoNot = "mono_not"
    case monoAnd = "mono_and"
    case monoOr = "mono_or"
    case monoImp = "mono_imp"
    case monoExists = "mono_exists"
    case monoForall = "mono_forall"
    case monoExistsBare = "mono_exists_bare"
    case monoForallBare = "mono_forall_bare"
    case forallAsNexists = "forall_as_nexists"
    case exIntro = "ex_intro"
    case read1
    case read2
    case read4
    case b1 = "B1"
    case b2 = "B2"
    case b3 = "B3"
    case bOr = "B_or"
    case bIff = "B_iff"
    case rowEx = "row_ex"
    case rowAll = "row_all"
    case rowLetter = "row_letter"
    case bImp = "B_imp"
    case nsuccEq = "nsucc_eq"
    case clsZero = "cls_zero"
    case clsNsucc = "cls_nsucc"
    case clsSnoc4 = "cls_snoc4"
    case clsDiag = "cls_diag"
    case rsKey = "rs_key"
    case clsApply = "cls_apply"
    case snocSome = "snoc_some"
    case snocFacts = "snoc_facts"
    case memberClass = "member_class"
    case graphClass = "graph_class"
    case impAsNand = "imp_as_nand"
    case orIdem = "or_idem"
    case powDef = "Pow_def"
    case unionDef = "Union_def"
    case upairEx = "upair_ex"
    case upairDef = "upair_def"
    case applyDef = "apply_def"
    case lamPred = "lam_pred"
    case lamClass = "lam_class"
    case snocEQ = "snoc_EQ"
    case tuplesClass = "tuples_class"
    case zfZeroDef = "ZF_Base.zero_def"
    case zfInfDef = "ZF_Base.Inf_def"
    case infDef = "Inf_def"
    case indDef = "ind_def"
    case zfExtensionNBG = "ZF_Base.extension_NBG"
    case zfUnionIffNBG = "ZF_Base.Union_iff_NBG"
    case zfPowIffNBG = "ZF_Base.Pow_iff_NBG"
    case zfReplacementNBG = "ZF_Base.replacement_NBG"
    case zfFoundationNBG = "ZF_Base.foundation_NBG"
    case zfInfinityNBG = "ZF_Base.infinity_NBG"
}

@frozen
public enum BaseError: Error, Equatable, Sendable {
    case missing(String)
}

public struct Base {
    public init(_ parsed: [String: NodeID]) throws {
        var statements = [BaseStatement: NodeID]()
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

    private let statements: [BaseStatement: NodeID]

}
