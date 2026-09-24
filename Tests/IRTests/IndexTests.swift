import Testing
import IR

private let i = IRType.i
private let o = IRType.o
private func fn(_ a: IRType, _ b: IRType) -> IRType { .fn(a, b) }
private let memT = fn(i, fn(i, o))
private let pairT = fn(i, fn(i, i))

private struct Seeded {
    var state: UInt64
    mutating func next(_ bound: Int) -> Int {
        state = state &* 6364136223846793005 &+ 1442695040888963407
        return Int((state >> 33) % UInt64(bound))
    }
}

/// Random well-typed formulas mixing both dialects; bound indices may be loose.
/// ⚠ A fol variable is instantiated only at a fol variable — an isa term inside a
/// `folPred` is an S1 violation `intern` refuses — so law 3 turns loose fol indices off.
private struct Gen {
    var rng: Seeded
    let frees: [String]
    let looseFol: Bool

    mutating func term(_ t: inout Table, _ depth: Int, _ size: Int) throws -> NodeID {
        switch size <= 0 ? rng.next(2) : rng.next(3) {
        case 0: return try t.intern(.isaFree(frees[rng.next(frees.count)], i))
        case 1: return try t.intern(.isaBound(rng.next(depth + 2), i))
        default:
            let a = try term(&t, depth, size - 1), b = try term(&t, depth, size - 1)
            return try t.intern(.isaConst("QPair.QPair", pairT, args: [a, b]))
        }
    }

    mutating func formula(_ t: inout Table, _ depth: Int, _ size: Int) throws -> NodeID {
        switch size <= 0 ? 0 : rng.next(6) {
        case 0:
            let a = try term(&t, depth, size - 1), b = try term(&t, depth, size - 1)
            return try t.intern(.isaConst("ZF_Base.mem", memT, args: [a, b]))
        case 1: return try t.intern(.folAnd(try formula(&t, depth, size - 1), try formula(&t, depth, size - 1)))
        case 2: return try t.intern(.folNot(try formula(&t, depth, size - 1)))
        case 3: return try t.intern(.ifolAll(i, body: try formula(&t, depth + 1, size - 1)))
        case 4: return try t.intern(.folForall(body: try folAtom(&t, depth + 1)))
        default:
            let body = try term(&t, depth + 1, size - 1)
            let abs = try t.intern(.isaAbs(i, body: body))
            let a = try term(&t, depth, size - 1)
            let repfun = try t.intern(.isaConst("ZF_Base.RepFun", fn(i, fn(fn(i, i), i)), args: [a, abs]))
            return try t.intern(.isaConst("ZF_Base.mem", memT, args: [a, repfun]))
        }
    }

    mutating func folAtom(_ t: inout Table, _ depth: Int) throws -> NodeID {
        let a = try t.intern(.folBound(looseFol ? rng.next(depth + 2) : 0))
        let b = try t.intern(.folBound(looseFol ? rng.next(depth + 2) : 0))
        return try t.intern(.folPred("elem", args: [a, b]))
    }
}

private func samples(_ seed: UInt64, frees: [String] = ["a", "b", "x"], looseFol: Bool = true,
                     _ body: (inout Table, NodeID) throws -> Void) throws {
    var gen = Gen(rng: Seeded(state: seed), frees: frees, looseFol: looseFol)
    for _ in 0..<300 {
        var t = Table()
        let phi = try gen.formula(&t, 0, 5)
        try body(&t, phi)
    }
}

// MARK: laws

@Test func instantiatingAFreshlyShiftedBinderChangesNothing() throws {
    try samples(1) { t, phi in
        let filler = try t.intern(.isaFree("filler", i))
        #expect(try instantiate(try shift(phi, by: 1, in: &t), with: filler, in: &t) == phi)
    }
}

@Test func closingThenReopeningAtTheSameNameChangesNothing() throws {
    try samples(2) { t, phi in
        let x = try t.intern(.isaFree("x", i))
        #expect(try instantiate(try abstract(phi, over: [x], in: &t), with: x, in: &t) == phi)
    }
}

@Test func openingAtAFreshNameThenClosingChangesNothing() throws {
    try samples(3, frees: ["a", "b"], looseFol: false) { t, psi in
        let x = try t.intern(.isaFree("x", i))
        #expect(try abstract(try instantiate(psi, with: x, in: &t), over: [x], in: &t) == psi)
    }
}

@Test func shiftsCompose() throws {
    try samples(4) { t, phi in
        let twice = try shift(try shift(phi, by: 2, in: &t), by: 3, in: &t)
        #expect(twice == (try shift(phi, by: 5, in: &t)))
    }
}

@Test func aClosedFormulaIsUntouched() throws {
    try samples(5) { t, phi in
        var closed = phi
        while t.looseBound(of: closed) > 0 { closed = try t.intern(.folForall(body: closed)) }
        let y = try t.intern(.isaFree("y", i))
        #expect(try shift(closed, by: 4, in: &t) == closed)
        #expect(try instantiate(closed, with: y, in: &t) == closed)
    }
}

// MARK: the worked cases of DESIGN.md §4.4

private func memOf(_ a: NodeID, _ b: NodeID, _ t: inout Table) throws -> NodeID {
    try t.intern(.isaConst("ZF_Base.mem", memT, args: [a, b]))
}

@Test func shiftMovesOnlyLooseIndices() throws {
    var t = Table()
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i)), b2 = try t.intern(.isaBound(2, i))
    let a = try t.intern(.isaFree("a", i))
    #expect(try shift(try memOf(b0, a, &t), by: 1, in: &t) == (try memOf(b1, a, &t)))
    let under = try t.intern(.ifolAll(i, body: try memOf(b0, b1, &t)))
    #expect(try shift(under, by: 1, in: &t) == (try t.intern(.ifolAll(i, body: try memOf(b0, b2, &t)))))
}

/// `∀x.∀y. (mem(x,y) → mem(y,x))` eliminated at `a`: x is 1 inside the inner ∀.
@Test func instantiateReplacesTheIndexEqualToTheDepth() throws {
    var t = Table()
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i))
    let a = try t.intern(.isaFree("a", i))
    let body = try t.intern(.ifolAll(i, body: try t.intern(.folImplies(try memOf(b1, b0, &t), try memOf(b0, b1, &t)))))
    let expected = try t.intern(.ifolAll(i, body: try t.intern(.folImplies(try memOf(a, b0, &t), try memOf(b0, a, &t)))))
    #expect(try instantiate(body, with: a, in: &t) == expected)
}

/// `∀y. mem(x, y)` with x := z, z bound outside: z must not be captured by y.
@Test func instantiateShiftsTheReplacementUnderInnerBinders() throws {
    var t = Table()
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i))
    let body = try t.intern(.ifolAll(i, body: try memOf(b1, b0, &t)))
    #expect(try instantiate(body, with: b0, in: &t) == body)
}

/// `(λx. mem(x, z)) z`: z was 1 only because the λ sat between.
@Test func instantiateLowersIndicesPointingFurtherOut() throws {
    var t = Table()
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i))
    #expect(try instantiate(try memOf(b0, b1, &t), with: b0, in: &t) == (try memOf(b0, b0, &t)))
}

/// `mem(x, A) → ∀. mem(0, x)` closed over x: the one node x becomes 0 here, 1 there.
@Test func abstractNumbersANameByItsDepth() throws {
    var t = Table()
    let x = try t.intern(.isaFree("x", i)), A = try t.intern(.isaFree("A", i))
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i))
    let phi = try t.intern(.folImplies(try memOf(x, A, &t), try t.intern(.ifolAll(i, body: try memOf(b0, x, &t)))))
    let expected = try t.intern(.folImplies(try memOf(b0, A, &t), try t.intern(.ifolAll(i, body: try memOf(b0, b1, &t)))))
    #expect(try abstract(phi, over: [x], in: &t) == expected)
}

/// Frees `[x, A]`, x outermost: `mem(x, A)` → `mem(1, 0)`.
@Test func abstractClosesSeveralNamesInOrder() throws {
    var t = Table()
    let x = try t.intern(.isaFree("x", i)), A = try t.intern(.isaFree("A", i))
    let b0 = try t.intern(.isaBound(0, i)), b1 = try t.intern(.isaBound(1, i))
    #expect(try abstract(try memOf(x, A, &t), over: [x, A], in: &t) == (try memOf(b1, b0, &t)))
}

@Test func instantiateRefusesAReplacementOfTheWrongType() throws {
    var t = Table()
    let b0 = try t.intern(.isaBound(0, i)), a = try t.intern(.isaFree("a", i))
    let formula = try memOf(a, a, &t)
    #expect(throws: IRRefusal.instantiateType(expected: i, found: o)) {
        try instantiate(try memOf(b0, a, &t), with: formula, in: &t)
    }
}
