import IR
import Testing
import YXML
@testable import Reader

private let iT = IRType.i
private let oT = IRType.o
private func fnT(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }

private struct Reading {
    var t = Table()
    let constants: Constants

    init() throws { constants = try testConstants() }

    mutating func proposition(_ prop: String, frees: [(String, String)] = []) throws -> NodeID {
        var f = Forest()
        let body = try f.parse(Array(prop.utf8))
        let types = try frees.map { ($0.0, try decodeType($0.1).irType()) }
        let terms = Terms(decode: Decode(forest: f), constants: constants,
                          frees: Dictionary(uniqueKeysWithValues: types))
        return try terms.proposition(body, in: &t)
    }

    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func free(_ name: String, _ T: IRType) throws -> NodeID { try n(.isaFree(name, T)) }
    mutating func bound(_ k: Int, _ T: IRType = .i) throws -> NodeID { try n(.isaBound(k, T)) }
    mutating func const(_ name: String, _ T: IRType, _ args: NodeID...) throws -> NodeID {
        try n(.isaConst(name, T, args: args))
    }
    mutating func abs(_ T: IRType, _ body: NodeID) throws -> NodeID { try n(.isaAbs(T, body: body)) }
    mutating func varApp(_ head: NodeID, _ args: NodeID...) throws -> NodeID { try n(.isaVarApp(head: head, args: args)) }
}

private let memT = fnT(iT, fnT(iT, oT))
private let pq = [("P", o), ("Q", o)]

@Test func trueFalseIsBottom() throws {
    var r = try Reading()
    #expect(try r.proposition(trueprop(const("IFOL.False"))) == (try r.n(.folBottom)))
}

@Test func theConnectivesReadAsTheirFolNodes() throws {
    var r = try Reading()
    let prop = trueprop(app(const("IFOL.conj"), free("P"),
                            app(const("IFOL.disj"), free("Q"),
                                app(const("IFOL.imp"), free("P"),
                                    app(const("IFOL.iff"), free("Q"), app(const("IFOL.Not"), free("P")))))))
    let got = try r.proposition(prop, frees: pq)
    let P = try r.free("P", oT), Q = try r.free("Q", oT)
    let iff = try r.n(.folIff(Q, try r.n(.folNot(P))))
    #expect(got == (try r.n(.folAnd(P, try r.n(.folOr(Q, try r.n(.folImplies(P, iff))))))))
}

@Test func metaImplicationIsFolImplies() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.imp"), trueprop(free("P")), trueprop(free("Q"))), frees: pq)
    #expect(got == (try r.n(.folImplies(try r.free("P", oT), try r.free("Q", oT)))))
}

@Test func metaEqualityAtOAndAtPropIsIff() throws {
    var r = try Reading()
    let atO = try r.proposition(app(const("Pure.eq", o), free("P"), free("Q")), frees: pq)
    let atProp = try r.proposition(app(const("Pure.eq", prop), trueprop(free("P")), trueprop(free("Q"))), frees: pq)
    let iff = try r.n(.folIff(try r.free("P", oT), try r.free("Q", oT)))
    #expect(atO == iff)
    #expect(atProp == iff)
}

@Test func metaEqualityAtIIsObjectEquality() throws {
    var r = try Reading()
    let ab = [("a", i), ("b", i)]
    let meta = try r.proposition(app(const("Pure.eq", i), free("a"), free("b")), frees: ab)
    let object = try r.proposition(trueprop(app(const("IFOL.eq", i), free("a"), free("b"))), frees: ab)
    #expect(meta == object)
    #expect(meta == (try r.const("IFOL.eq", memT, try r.free("a", iT), try r.free("b", iT))))
}

@Test func metaEqualityAtAFunctionTypeIsADefinitionNode() throws {
    var r = try Reading()
    let got = try r.proposition(app(const("Pure.eq", fn(i, i)), free("F"), lam("x", i, app(const("Sum.Inl"), bound(0)))),
                                frees: [("F", fn(i, i))])
    let ii = fnT(iT, iT)
    let lhs = try r.abs(iT, try r.varApp(try r.free("F", ii), try r.bound(0)))
    let rhs = try r.abs(iT, try r.const("Sum.Inl", ii, try r.bound(0)))
    #expect(got == (try r.const("Pure.eq", fnT(ii, fnT(ii, oT)), lhs, rhs)))
}

@Test func quantifiersReadAsIfolBinders() throws {
    var r = try Reading()
    let body = trueprop(app(const("ZF_Base.mem"), bound(0), free("A")))
    let meta = try r.proposition(app(const("Pure.all", i), lam("x", i, body)), frees: [("A", i)])
    let mem = try r.const("ZF_Base.mem", memT, try r.bound(0), try r.free("A", iT))
    #expect(meta == (try r.n(.ifolAll(iT, body: mem))))
    let exists = try r.proposition(trueprop(app(const("IFOL.Ex", i), lam("x", i, app(const("ZF_Base.mem"), bound(0), free("A"))))),
                                   frees: [("A", i)])
    #expect(exists == (try r.n(.ifolEx(iT, body: mem))))
}

@Test func aBoundVariableTakesItsBindersType() throws {
    var r = try Reading()
    let got = try r.proposition(trueprop(app(const("IFOL.All", o), lam("P", o, bound(0)))))
    #expect(got == (try r.n(.ifolAll(oT, body: try r.bound(0, oT)))))
}

@Test func aMetaQuantifierOverAFunctionIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.quantifierOverFunction) {
        try r.proposition(app(const("Pure.all", fn(i, i)), lam("f", fn(i, i), trueprop(const("IFOL.False")))))
    }
}

@Test func aBareVariableArgumentReadsAsItsEtaExpansion() throws {
    var r = try Reading()
    let frees = [("A", i), ("P", fn(i, o))]
    let short = try r.proposition(trueprop(app(const("ZF_Base.Ball"), free("A"), free("P"))), frees: frees)
    let long = try r.proposition(trueprop(app(const("ZF_Base.Ball"), free("A"), lam("x", i, app(free("P"), bound(0))))), frees: frees)
    #expect(short == long)
    let P = try r.abs(iT, try r.varApp(try r.free("P", fnT(iT, oT)), try r.bound(0)))
    #expect(short == (try r.const("ZF_Base.Ball", fnT(iT, fnT(fnT(iT, oT), oT)), try r.free("A", iT), P)))
}

@Test func aConstantArgumentReadsAsItsEtaExpansion() throws {
    var r = try Reading()
    let part = { (inl: String) in trueprop(app(const("IFOL.eq", i), app(const("Sum.Part"), free("A"), inl), free("A"))) }
    let short = try r.proposition(part(const("Sum.Inl")), frees: [("A", i)])
    let long = try r.proposition(part(lam("x", i, app(const("Sum.Inl"), bound(0)))), frees: [("A", i)])
    #expect(short == long)
}

@Test func aPartialApplicationArgumentReadsEtaExpanded() throws {
    var r = try Reading()
    let got = try r.proposition(trueprop(app(const("EquivClass.congruent"), free("r"), app(const("ZF_Base.split", i), free("f")))),
                                frees: [("r", i), ("f", fn(i, fn(i, i)))])
    let iii = fnT(iT, fnT(iT, iT))
    let f = try r.abs(iT, try r.abs(iT, try r.varApp(try r.free("f", iii), try r.bound(1), try r.bound(0))))
    let split = try r.abs(iT, try r.const("ZF_Base.split", fnT(iii, fnT(iT, iT)), f, try r.bound(0)))
    #expect(got == (try r.const("EquivClass.congruent", fnT(iT, fnT(fnT(iT, iT), oT)), try r.free("r", iT), split)))
}

@Test func aPartlyEtaReducedLambdaIsCompleted() throws {
    var r = try Reading()
    let partly = try r.proposition(trueprop(app(const("IFOL.eq", i), app(const("T.g"), lam("v", i, app(const("T.f"), bound(0)))), free("a"))),
                                   frees: [("a", i)])
    let full = try r.proposition(trueprop(app(const("IFOL.eq", i),
                                              app(const("T.g"), lam("v", i, lam("w", i, app(const("T.f"), bound(1), bound(0))))),
                                              free("a"))),
                                 frees: [("a", i)])
    #expect(partly == full)
}

@Test func etaUnderABinderKeepsOuterBoundsPointingOutward() throws {
    var r = try Reading()
    let frees = [("A", i), ("R", fn(i, fn(i, o)))]
    let short = try r.proposition(app(const("Pure.all", i), lam("x", i, trueprop(app(const("ZF_Base.Ball"), free("A"), app(free("R"), bound(0)))))),
                                  frees: frees)
    let long = try r.proposition(app(const("Pure.all", i), lam("x", i, trueprop(app(const("ZF_Base.Ball"), free("A"),
                                                                                    lam("y", i, app(free("R"), bound(1), bound(0))))))),
                                 frees: frees)
    #expect(short == long)
}

@Test func aSchematicVariableIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.schematicVariable("P")) { try r.proposition(trueprop(schematic("P"))) }
}

@Test func anOfclassIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.ofclass("IFOL.term")) { try r.proposition(ofclass(i, "IFOL.term")) }
}

@Test func aPureInternalConstantIsRefusedByName() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.pureInternal("Pure.term")) {
        try r.proposition(app(const("Pure.term", i), free("a")), frees: [("a", i)])
    }
    #expect(throws: ReaderRefusal.pureInternal("Pure.conjunction")) {
        try r.proposition(app(const("Pure.conjunction"), trueprop(const("IFOL.False")), trueprop(const("IFOL.False"))))
    }
}

@Test func aBetaRedexIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.betaRedex) {
        try r.proposition(trueprop(app(lam("x", i, app(const("ZF_Base.mem"), bound(0), free("a"))), free("a"))), frees: [("a", i)])
    }
}

@Test func aTypeVariableInATypeArgumentIsRefused() throws {
    var r = try Reading()
    #expect(throws: ReaderRefusal.typeVariable("'a")) {
        try r.proposition(trueprop(app(const("IFOL.eq", typeA), free("a"), free("a"))), frees: [("a", i)])
    }
}

@Test func anUnboundBoundIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.unboundBound(0)) {
        try r.proposition(trueprop(app(const("ZF_Base.mem"), bound(0), free("a"))), frees: [("a", i)])
    }
}

@Test func aFreeMissingFromTheHeaderIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.undeclaredFree("x")) {
        try r.proposition(trueprop(app(const("ZF_Base.mem"), free("x"), free("a"))), frees: [("a", i)])
    }
}

@Test func aLambdaWhereAPropositionIsExpectedIsMalformed() throws {
    var r = try Reading()
    #expect(throws: MalformedExport.unexpectedAbstraction(expected: .o)) {
        try r.proposition(trueprop(lam("x", i, const("IFOL.False"))))
    }
}
