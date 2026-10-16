import IR

/// A table holding the logic's definitions as the reader hands them.
struct LogicTable {
    var t = Table()

    mutating func bound(_ k: Int, _ T: IRType) throws -> NodeID { try t.intern(.isaBound(k, T)) }
    mutating func bottom() throws -> NodeID { try t.intern(.folBottom) }
    mutating func imp(_ a: NodeID, _ b: NodeID) throws -> NodeID { try t.intern(.folImplies(a, b)) }
    mutating func and(_ a: NodeID, _ b: NodeID) throws -> NodeID { try t.intern(.folAnd(a, b)) }
    mutating func all(_ T: IRType, _ body: NodeID) throws -> NodeID { try t.intern(.ifolAll(T, body: body)) }
    mutating func lam(_ T: IRType, _ body: NodeID) throws -> NodeID { try t.intern(.isaAbs(T, body: body)) }
    mutating func const(_ c: Constant, _ T: IRType, _ xs: NodeID...) throws -> NodeID { try t.intern(.isaConst(c, T, args: xs)) }
    mutating func mem(_ x: NodeID, _ y: NodeID) throws -> NodeID {
        try const(.primitive(.zf(.mem)), .fn(.i, .fn(.i, .o)), x, y)
    }

    mutating func equal(_ T: IRType, _ a: NodeID, _ b: NodeID) throws -> NodeID { try t.equation(T, a, b) }

    mutating func definition(_ c: Defined, _ T: IRType, axiomTypes: [IRType] = [], parameters: Int = 0,
                             _ definiens: NodeID) throws -> Definition {
        Definition(defines: .constant(c), type: T, axiomTypes: axiomTypes, parameters: parameters, definiens: definiens)
    }

    /// `Not ≡ λP. P ⟶ ⊥`
    mutating func not() throws -> Definition {
        try definition(Defined(.ifol, "IFOL.Not", .object), .fn(.o, .o), try lam(.o, try imp(try bound(0, .o), try bottom())))
    }

    /// `iff ≡ λP Q. (P ⟶ Q) ∧ (Q ⟶ P)`
    mutating func iff() throws -> Definition {
        let p = try bound(1, .o), q = try bound(0, .o)
        let body = try and(try imp(p, q), try imp(q, p))
        return try definition(Defined(.ifol, "IFOL.iff", .object), .fn(.o, .fn(.o, .o)), try lam(.o, try lam(.o, body)))
    }

    /// `True ≡ ⊥ ⟶ ⊥`
    mutating func truth() throws -> Definition {
        try definition(Defined(.ifol, "IFOL.True", .object), .o, try imp(try bottom(), try bottom()))
    }

    /// `Ex1 ≡ λP. ∃x. P(x) ∧ (∀y. P(y) ⟶ y = x)`, at `'a := i`
    mutating func ex1() throws -> Definition {
        let P = IRType.fn(.i, .o)
        let px = try t.intern(.isaVarApp(head: try bound(1, P), args: [try bound(0, .i)]))
        let py = try t.intern(.isaVarApp(head: try bound(2, P), args: [try bound(0, .i)]))
        let unique = try all(.i, try imp(py, try equal(.i, try bound(0, .i), try bound(1, .i))))
        let body = try t.intern(.ifolEx(.i, body: try and(px, unique)))
        return try definition(Defined(.ifol, "IFOL.Ex1", .meta), .fn(P, .o), axiomTypes: [.i], try lam(P, body))
    }

    /// `conjunction(A, B) ≡ ⋀C. (A ⟹ B ⟹ C) ⟹ C`: Pure's applied form, of two parameters
    mutating func conjunction() throws -> Definition {
        let body = try conjunctionBody()
        return try definition(Defined(.pure, "Pure.conjunction", .meta), .fn(.o, .fn(.o, .o)), parameters: 2,
                              try lam(.o, try lam(.o, body)))
    }

    /// `⋀C. (A ⟹ B ⟹ C) ⟹ C`, under `A` and `B`
    mutating func conjunctionBody() throws -> NodeID {
        let a = try bound(2, .o), b = try bound(1, .o), c = try bound(0, .o)
        return try all(.o, try imp(try imp(a, try imp(b, c)), c))
    }
}

extension Definition {
    /// The constant a test's definition defines: every `LogicTable` definition but a class's.
    var constant: Defined {
        guard case let .constant(c) = defines else { preconditionFailure("\(defines) defines no constant") }
        return c
    }
}
