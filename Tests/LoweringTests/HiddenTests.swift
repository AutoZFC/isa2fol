import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o

private func lowered(_ l: LogicTable, _ statements: [Statement]) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements)
    try pipeline(b).run(&unit)
    return unit
}

/// `⋀Q. (∀h::T. Q) ⟶ Q`, proved at the variable only its proof uses: `isaHidden(T, …)` below the letter, the premise
/// instantiated at the hidden variable, η-long at a function type (DESIGN "Step 7").
private func instantiatedAtTheHiddenVariable(_ T: IRType, _ l: inout LogicTable) throws -> Statement {
    let binder = { (body: NodeID, l: inout LogicTable) throws -> NodeID in
        T == .o ? try l.t.intern(.isaPropAll(body: body)) : try l.all(T, body)
    }
    let stated = try binder(try l.bound(1, o), &l)
    let root = try l.all(o, try l.imp(stated, try l.bound(0, o)))
    let premise = try binder(try l.bound(2, o), &l)
    let hidden: NodeID =
        switch T {
        case .o: try l.t.intern(.isaPropBound(0))
        case .fn(let A, _): try l.lam(A, try l.t.intern(.isaVarApp(head: try l.bound(1, T), args: [try l.bound(0, A)])))
        case .i, .variable: try l.bound(0, T)
        }
    let instance = try l.t.intern(.isaAllElim(try l.t.intern(.hyp(0, premise)), hidden))
    let proof = try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaHidden(
        T,
        body: try l.t.intern(.folImpliesIntro(premise, body: instance)),
    ))))
    return Statement(name: "T.hidden", root: root, proof: proof, theory: "Test")
}

/// At each object type the hidden variable is the witness of `exists_elim` over its type's inhabitation, with its guard
/// where the type has one; at `o`, a truth set, read `holds(E)`. The kernel proves each.
@Test
func aHiddenVariableIsTheWitnessOfItsTypesInhabitation() throws {
    for T in [i, .fn(i, i), .fn(i, o), o] {
        var l = LogicTable()
        let thm = try instantiatedAtTheHiddenVariable(T, &l)
        let unit = try lowered(l, [thm])
        #expect(unit.refused.isEmpty, "\(T): \(unit.refused)")
        try kernelChecks(unit)
    }
}
