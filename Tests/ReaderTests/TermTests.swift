import IR
import Testing
import YXML
@testable import Reader

private let iT = IRType.i
private let oT = IRType.o
private func fnT(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

/// Reads a proposition under its frees' closure, so free `x` of `n` reads as bound `n − 1 − level(x)`
/// at the top, one more under each binder (DESIGN §4.4). `free(x, T, under:)` names that node.
private struct Reading {
    init() throws {
        constants = try testConstants()
    }

    var t = Table()
    let constants: Constants

    mutating func proposition(_ prop: String, tfrees: [String] = [], frees: [(String, String)] = []) throws -> NodeID {
        var f = Forest()
        let body = try f.parse(Array(prop.utf8))
        let e = Envelope(tfrees: tfrees, frees: try frees.map { ($0.0, try decodeType($0.1)) }, prop: body)
        var terms = try Terms(
            decode: Decode(forest: f),
            constants: constants,
            classes: try testClasses(),
            file: e,
            at: tfrees.map(IRType.variable),
            order: .stated,
        )
        self.frees = frees.map(\.0)
        return try terms.proposition(body, terms.closure, in: &t)
    }

    mutating func n(_ node: Node) throws -> NodeID {
        try t.intern(node)
    }

    mutating func free(_ name: String, _ T: IRType, under binders: Int = 0) throws -> NodeID {
        try n(.isaBound(binders + frees.count - 1 - frees.firstIndex(of: name)!, T))
    }

    mutating func bound(_ k: Int, _ T: IRType = .i) throws -> NodeID {
        try n(.isaBound(k, T))
    }

    mutating func const(_ c: Constant, _ T: IRType, _ args: NodeID...) throws -> NodeID {
        try n(.isaConst(c, T, args: args))
    }

    mutating func abs(_ T: IRType, _ body: NodeID) throws -> NodeID {
        try n(.isaAbs(T, body: body))
    }

    mutating func varApp(
        _ head: NodeID,
        _ args: NodeID...,
    ) throws -> NodeID {
        try n(.isaVarApp(head: head, args: args))
    }

    private var frees = [String]()

}

private let memT = fnT(iT, fnT(iT, oT))
private let pq = [("P", o), ("Q", o)]
private let mem = Constant.primitive(.zf(.mem))

/// A LEAF that FOL has reads as the SAME node as the FOL construct that covers it.
@Test
func aCoveredLeafReadsAsItsCover() throws {
    var r = try Reading()
    let P = trueprop(free("P"))
    let Q = trueprop(free("Q"))
    #expect(
        try r.proposition(app(const("Pure.imp"), P, Q), frees: pq)
            == (try r.proposition(trueprop(app(const("IFOL.imp"), free("P"), free("Q"))), frees: pq)),
        "⟹ is →",
    )
    let body = app(const("ZF_Base.mem"), bound(0), free("A"))
    #expect(
        try r.proposition(app(const("Pure.all", i), lam("x", i, trueprop(body))), frees: [("A", i)])
            == (try r.proposition(trueprop(app(const("IFOL.All", i), lam("x", i, body))), frees: [("A", i)])),
        "⋀ is ∀",
    )
}

@Test
func trueFalseIsBottom() throws {
    var r = try Reading()
    #expect(try r.proposition(trueprop(const("IFOL.False"))) == (try r.n(.folBottom)))
}

/// Coverage is for leaves only: IFOL DEFINES `↔` and `¬`, so they read as defined constants, never as
/// `folIff`/`folNot`.
@Test
func theCoveredLeavesReadAsFolNodesAndADefinedConnectiveAsDefined() throws {
    var r = try Reading()
    let prop = trueprop(app(
        const("IFOL.conj"),
        free("P"),
        app(
            const("IFOL.disj"),
            free("Q"),
            app(
                const("IFOL.imp"),
                free("P"),
                app(const("IFOL.iff"), free("Q"), app(const("IFOL.Not"), free("P"))),
            ),
        ),
    ))
    let got = try r.proposition(prop, frees: pq)
    let P = try r.free("P", oT)
    let Q = try r.free("Q", oT)
    let not = try r.const(defined(.ifol, "IFOL.Not", .object), fnT(oT, oT), P)
    let iff = try r.const(defined(.ifol, "IFOL.iff", .object), fnT(oT, fnT(oT, oT)), Q, not)
    #expect(got == (try r.n(.folAnd(P, try r.n(.folOr(Q, try r.n(.folImplies(P, iff))))))))
}

/// `Trueprop` is a leaf, the coercion FOL does not need; `PROP` is Pure's DEFINED identity, read as defined.
@Test
func truepropIsErasedAndPropIsADefinedConstant() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.prop"), trueprop(free("P"))), frees: [("P", o)])
    #expect(got == (try r.const(defined(.pure, "Pure.prop", .meta), fnT(oT, oT), try r.free("P", oT))))
}

/// The exporter writes only a variable a proof uses as `dummy_pattern` (`standard_hidden_terms`): the proof binds it
/// (DESIGN "Step 7"), so outside a proof the export is malformed.
@Test
func aHiddenVariableOutsideAProofIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.hiddenOutsideProof(iT)) {
        try r.proposition(
            trueprop(app(const("ZF_Base.mem"), const("Pure.dummy_pattern", i), free("A"))),
            frees: [("A", i)],
        )
    }
}

@Test
func anUndefinedConstantAboveTheFoundationIsDeclared() throws {
    var r = try Reading()
    #expect(try r.proposition(const("T.claim")) == (try r.const(defined(.zf, "T.claim", .meta), oT)))
}

/// `ZF_Base.not_mem` is an undefined constant of the foundation that the dialect does not list.
@Test
func anUnlistedLeafOfTheFoundationStopsTheRead() throws {
    var r = try Reading()
    #expect(throws: DialectGap.leaf("ZF_Base.not_mem")) {
        try r.proposition(trueprop(app(const("ZF_Base.not_mem"), free("a"), free("a"))), frees: [("a", i)])
    }
}

@Test
func metaImplicationIsFolImplies() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.imp"), trueprop(free("P")), trueprop(free("Q"))), frees: pq)
    #expect(got == (try r.n(.folImplies(try r.free("P", oT), try r.free("Q", oT)))))
}

@Test
func metaEqualityAtOAndAtPropIsIff() throws {
    var r = try Reading()
    let atO = try r.proposition(app(const("Pure.eq", o), free("P"), free("Q")), frees: pq)
    let atProp = try r.proposition(app(const("Pure.eq", prop), trueprop(free("P")), trueprop(free("Q"))), frees: pq)
    let iff = try r.n(.folIff(try r.free("P", oT), try r.free("Q", oT)))
    #expect(atO == iff)
    #expect(atProp == iff)
}

@Test
func metaEqualityAtIIsObjectEquality() throws {
    var r = try Reading()
    let ab = [("a", i), ("b", i)]
    let meta = try r.proposition(app(const("Pure.eq", i), free("a"), free("b")), frees: ab)
    let object = try r.proposition(trueprop(app(const("IFOL.eq", i), free("a"), free("b"))), frees: ab)
    #expect(meta == object)
    #expect(meta == (try r.const(.primitive(.ifol(.eq)), memT, try r.free("a", iT), try r.free("b", iT))))
}

/// Nothing covers `≡` at a type variable — it is `↔` at `o`, `=` at `i` — so it stays Pure's constant.
@Test
func metaEqualityAtATypeVariableIsPureEq() throws {
    var r = try Reading()
    let a = IRType.variable("'a")
    let got = try r.proposition(
        app(const("Pure.eq", typeA), free("x"), free("y")),
        tfrees: ["'a"],
        frees: [("x", typeA), ("y", typeA)],
    )
    #expect(got == (try r.const(.primitive(.pure(.eq)), fnT(a, fnT(a, oT)), try r.bound(1, a), try r.bound(0, a))))
}

@Test
func metaEqualityAtAFunctionTypeIsADefinitionNode() throws {
    var r = try Reading()
    let got = try r.proposition(
        app(const("Pure.eq", fn(i, i)), free("F"), lam("x", i, app(const("Sum.Inl"), bound(0)))),
        frees: [("F", fn(i, i))],
    )
    let ii = fnT(iT, iT)
    let lhs = try r.abs(iT, try r.varApp(try r.free("F", ii, under: 1), try r.bound(0)))
    let rhs = try r.abs(iT, try r.const(defined(.zf, "Sum.Inl", .object), ii, try r.bound(0)))
    #expect(got == (try r.const(.primitive(.pure(.eq)), fnT(ii, fnT(ii, oT)), lhs, rhs)))
}

@Test
func quantifiersReadAsIfolBinders() throws {
    var r = try Reading()
    let body = trueprop(app(const("ZF_Base.mem"), bound(0), free("A")))
    let meta = try r.proposition(app(const("Pure.all", i), lam("x", i, body)), frees: [("A", i)])
    let mem = try r.const(mem, memT, try r.bound(0), try r.free("A", iT, under: 1))
    #expect(meta == (try r.n(.ifolAll(iT, body: mem))))
    let exists = try r.proposition(
        trueprop(app(const("IFOL.Ex", i), lam("x", i, app(const("ZF_Base.mem"), bound(0), free("A"))))),
        frees: [("A", i)],
    )
    #expect(exists == (try r.n(.ifolEx(iT, body: mem))))
}

@Test
func aBoundVariableTakesItsBindersType() throws {
    var r = try Reading()
    let got = try r.proposition(trueprop(app(const("IFOL.All", o), lam("P", o, bound(0)))))
    #expect(got == (try r.n(.ifolAll(oT, body: try r.bound(0, oT)))))
}

/// Below a statement's top, Pure's `⋀` over a proposition is its own node, its variable its own: a bound proposition,
/// never the statement's letter.
@Test
func aMetaQuantifierOverAPropositionIsPuresBoundAll() throws {
    var r = try Reading()
    let got = try r.proposition(app(
        const("Pure.all", prop),
        lam("W", prop, app(const("Pure.imp"), bound(0), bound(0))),
    ))
    let W = try r.n(.isaPropBound(0))
    #expect(got == (try r.n(.isaPropAll(body: try r.n(.folImplies(W, W))))))
}

@Test
func aPropositionValuedConstantReadsAsAFormulaConstant() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.imp"), const("T.claim"), trueprop(const("IFOL.False"))))
    #expect(got == (try r.n(.folImplies(try r.const(defined(.zf, "T.claim", .meta), oT), try r.n(.folBottom)))))
}

@Test
func aConstantOverPropositionsReadsWithPropAsO() throws {
    var r = try Reading()
    let got = try r.proposition(
        app(const("T.metaEx", i), lam("x", i, trueprop(app(const("ZF_Base.mem"), bound(0), free("A"))))),
        frees: [("A", i)],
    )
    let mem = try r.const(mem, memT, try r.bound(0), try r.free("A", iT, under: 1))
    #expect(got == (try r.const(defined(.zf, "T.metaEx", .meta), fnT(fnT(iT, oT), oT), try r.abs(iT, mem))))
}

@Test
func aMetaQuantifierOverAFunctionIsAQuantifierAtThatType() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.all", fn(i, i)), lam("f", fn(i, i), trueprop(const("IFOL.False")))))
    #expect(got == (try r.n(.ifolAll(fnT(iT, iT), body: try r.n(.folBottom)))))
}

@Test
func aBareVariableArgumentReadsAsItsEtaExpansion() throws {
    var r = try Reading()
    let frees = [("A", i), ("P", fn(i, o))]
    let short = try r.proposition(trueprop(app(const("ZF_Base.Ball"), free("A"), free("P"))), frees: frees)
    let long = try r.proposition(
        trueprop(app(const("ZF_Base.Ball"), free("A"), lam("x", i, app(free("P"), bound(0))))),
        frees: frees,
    )
    #expect(short == long)
    let P = try r.abs(iT, try r.varApp(try r.free("P", fnT(iT, oT), under: 1), try r.bound(0)))
    #expect(short == (try r.const(
        defined(.zf, "ZF_Base.Ball", .object),
        fnT(iT, fnT(fnT(iT, oT), oT)),
        try r.free("A", iT),
        P,
    )))
}

@Test
func aConstantArgumentReadsAsItsEtaExpansion() throws {
    var r = try Reading()
    let part = { (inl: String) in
        trueprop(app(const("IFOL.eq", i), app(const("Sum.Part"), free("A"), inl), free("A")))
    }
    let short = try r.proposition(part(const("Sum.Inl")), frees: [("A", i)])
    let long = try r.proposition(part(lam("x", i, app(const("Sum.Inl"), bound(0)))), frees: [("A", i)])
    #expect(short == long)
}

@Test
func aPartialApplicationArgumentReadsEtaExpanded() throws {
    var r = try Reading()
    let got = try r.proposition(
        trueprop(app(const("EquivClass.congruent"), free("r"), app(const("ZF_Base.split", i), free("f")))),
        frees: [("r", i), ("f", fn(i, fn(i, i)))],
    )
    let iii = fnT(iT, fnT(iT, iT))
    let f = try r.abs(iT, try r.abs(iT, try r.varApp(try r.free("f", iii, under: 3), try r.bound(1), try r.bound(0))))
    let split = try r.abs(
        iT,
        try r.const(defined(.zf, "ZF_Base.split", .meta), fnT(iii, fnT(iT, iT)), f, try r.bound(0)),
    )
    #expect(got == (try r.const(
        defined(.zf, "EquivClass.congruent", .object),
        fnT(iT, fnT(fnT(iT, iT), oT)),
        try r.free("r", iT),
        split,
    )))
}

@Test
func aPartlyEtaReducedLambdaIsCompleted() throws {
    var r = try Reading()
    let partly = try r.proposition(
        trueprop(app(const("IFOL.eq", i), app(const("T.g"), lam("v", i, app(const("T.f"), bound(0)))), free("a"))),
        frees: [("a", i)],
    )
    let full = try r.proposition(
        trueprop(app(
            const("IFOL.eq", i),
            app(
                const("T.g"),
                lam("v", i, lam("w", i, app(const("T.f"), bound(1), bound(0)))),
            ),
            free("a"),
        )),
        frees: [("a", i)],
    )
    #expect(partly == full)
}

@Test
func etaUnderABinderKeepsOuterBoundsPointingOutward() throws {
    var r = try Reading()
    let frees = [("A", i), ("R", fn(i, fn(i, o)))]
    let short = try r.proposition(
        app(
            const("Pure.all", i),
            lam("x", i, trueprop(app(const("ZF_Base.Ball"), free("A"), app(free("R"), bound(0))))),
        ),
        frees: frees,
    )
    let long = try r.proposition(
        app(const("Pure.all", i), lam("x", i, trueprop(app(
            const("ZF_Base.Ball"),
            free("A"),
            lam(
                "y",
                i,
                app(
                    free("R"),
                    bound(1),
                    bound(0),
                ),
            ),
        )))),
        frees: frees,
    )
    #expect(short == long)
}

@Test
func anEtaVariableOfFunctionTypeIsItselfEtaLong() throws {
    var r = try Reading()
    let short = try r.proposition(
        trueprop(app(const("IFOL.eq", i), app(const("T.k"), const("T.h")), free("a"))),
        frees: [("a", i)],
    )
    let long = try r.proposition(
        trueprop(app(
            const("IFOL.eq", i),
            app(
                const("T.k"),
                lam(
                    "P",
                    fn(i, o),
                    app(const("T.h"), lam("x", i, app(bound(1), bound(0)))),
                ),
            ),
            free("a"),
        )),
        frees: [("a", i)],
    )
    #expect(short == long)
}

/// `standard_vars` turns every schematic variable into a free one.
@Test
func aSchematicVariableIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.schematicVariable("P")) { try r.proposition(trueprop(schematic("P"))) }
}

@Test
func anOfclassReadsAsAClassMembership() throws {
    var r = try Reading()
    #expect(try r.proposition(ofclass(i, "IFOL.term")) == (try r.n(.isaOfClass(iT, ifolTerm))))
    #expect(throws: MalformedExport.undeclaredClass("T.nowhere")) { try r.proposition(ofclass(i, "T.nowhere")) }
}

@Test
func aPureInternalConstantReadsAsAConstant() throws {
    var r = try Reading()
    let term = try r.proposition(app(const("Pure.term", i), free("a")), frees: [("a", i)])
    #expect(term == (try r.const(defined(.pure, "Pure.term", .meta), fnT(iT, oT), try r.free("a", iT))))
    let conjunction = try r.proposition(app(
        const("Pure.conjunction"),
        trueprop(const("IFOL.False")),
        trueprop(const("IFOL.False")),
    ))
    let bottom = try r.n(.folBottom)
    #expect(conjunction == (try r.const(
        defined(.pure, "Pure.conjunction", .meta),
        fnT(oT, fnT(oT, oT)),
        bottom,
        bottom,
    )))
}

@Test
func aBetaRedexIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.betaRedex) {
        try r.proposition(
            trueprop(app(lam("x", i, app(const("ZF_Base.mem"), bound(0), free("a"))), free("a"))),
            frees: [("a", i)],
        )
    }
}

@Test
func aTypeVariableTheHeaderDoesNotDeclareIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.undeclaredTypeVariable("'a")) {
        try r.proposition(trueprop(app(const("IFOL.eq", typeA), free("a"), free("a"))), frees: [("a", i)])
    }
}

@Test
func anUnboundBoundIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.unboundBound(0)) {
        try r.proposition(trueprop(app(const("ZF_Base.mem"), bound(0), free("a"))), frees: [("a", i)])
    }
}

@Test
func aFreeReadsAsItsClosureBinderTheFirstOutermost() throws {
    var r = try Reading()
    let got = try r.proposition(trueprop(app(const("ZF_Base.mem"), free("a"), free("A"))), frees: [("a", i), ("A", i)])
    #expect(got == (try r.const(mem, memT, try r.bound(1), try r.bound(0))))
}

/// Axioms are encoded with typed variables (`typed_vars = true`); the type must be the header's.
@Test
func aVariableCarryingItsTypeMustAgreeWithTheHeader() throws {
    var r = try Reading()
    let typed = { (T: String) in trueprop(app(const("ZF_Base.mem"), tagged(1, ["a"], [T]), tagged(1, ["a"], [T]))) }
    #expect(try r.proposition(typed(i), frees: [("a", i)]) == (try r.proposition(
        trueprop(app(const("ZF_Base.mem"), free("a"), free("a"))),
        frees: [("a", i)],
    )))
    #expect(throws: MalformedExport.typeMismatch(expected: iT, found: oT)) { try r.proposition(
        typed(o),
        frees: [("a", i)],
    ) }
}

/// The same export subtree under binders of different types is two terms: the memo is keyed on the scope.
@Test
func aSharedSubtreeReadsByItsScope() throws {
    var r = try Reading()
    let got = try r.proposition(trueprop(app(const("IFOL.All", i), lam("x", i, app(
        const("IFOL.conj"),
        app(
            const("IFOL.All", o),
            lam("P", o, bound(0)),
        ),
        app(
            const("ZF_Base.mem"),
            bound(0),
            bound(0),
        ),
    )))))
    let inner = try r.n(.ifolAll(oT, body: try r.bound(0, oT)))
    let mem = try r.const(mem, memT, try r.bound(0), try r.bound(0))
    #expect(got == (try r.n(.ifolAll(iT, body: try r.n(.folAnd(inner, mem))))))
}

@Test
func aLambdaWhereAPropositionIsExpectedIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.unexpectedAbstraction(expected: .o)) {
        try r.proposition(trueprop(lam("x", i, const("IFOL.False"))))
    }
}
