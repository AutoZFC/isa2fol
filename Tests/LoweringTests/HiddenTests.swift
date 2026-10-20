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
/// instantiated at the hidden variable (DESIGN "Step 7").
private func instantiatedAtTheHiddenVariable(_ T: IRType, _ l: inout LogicTable) throws -> Statement {
    let binder = { (body: NodeID, l: inout LogicTable) throws -> NodeID in
        T == .o ? try l.t.intern(.isaPropAll(body: body)) : try l.all(T, body)
    }
    let stated = try binder(try l.bound(1, o), &l)
    let root = try l.all(o, try l.imp(stated, try l.bound(0, o)))
    let premise = try binder(try l.bound(2, o), &l)
    let hidden = T == .o ? try l.t.intern(.isaPropBound(0)) : try l.bound(0, T)
    let instance = try l.t.intern(.isaAllElim(try l.t.intern(.hyp(0, premise)), hidden))
    let proof = try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaHidden(
        T,
        body: try l.t.intern(.folImpliesIntro(premise, body: instance)),
    ))))
    return Statement(name: "T.hidden", root: root, proof: proof, theory: "Test")
}

/// The reader binds a variable only the proof uses at `i` and at `o` alone: at `i` the witness of `exists_elim` over
/// `set_inhabited`, its guard `set`; at `o` a truth set, read `holds(E)`. The kernel proves each.
@Test
func aHiddenVariableIsTheWitnessOfItsTypesInhabitation() throws {
    for T in [i, o] {
        var l = LogicTable()
        let thm = try instantiatedAtTheHiddenVariable(T, &l)
        let unit = try lowered(l, [thm])
        #expect(unit.refused.isEmpty, "\(T): \(unit.refused)")
        try kernelChecks(unit)
    }
}

/// `int_all_simps`'s first goal in miniature, `⋀Q P. (∀x. P(x) ∧ Q) ⟶ Q`: the premise at the proof's witness, which
/// iprover leaves applied to `P` and `Q` and the reader reads at `i` (DESIGN "A variable only the proof uses, constant
/// in its arguments"). The kernel proves it.
@Test
func aWitnessAppliedToTheStatementsClassAndLetterIsTheProofsVariableAtI() throws {
    var l = LogicTable()
    let classType = IRType.fn(i, o)
    func premise(_ p: Int, _ l: inout LogicTable) throws -> NodeID {
        let atX = try l.t.intern(.isaVarApp(head: try l.bound(p + 1, classType), args: [try l.bound(0, i)]))
        return try l.all(i, try l.and(atX, try l.bound(p + 2, o)))
    }
    let root = try l.all(o, try l.all(classType, try l.imp(try premise(0, &l), try l.bound(1, o))))
    let assumed = try premise(1, &l)
    let atH = try l.t.intern(.isaAllElim(try l.t.intern(.hyp(0, assumed)), try l.bound(0, i)))
    let proof = try l.t.intern(.isaAllIntro(o, body: try l.t.intern(.isaAllIntro(
        classType,
        body: try l.t.intern(.isaHidden(
            i,
            body: try l.t.intern(.folImpliesIntro(assumed, body: try l.t.intern(.folAndElimR(atH)))),
        )),
    ))))
    #expect(l.t.conclusion(of: proof) == root)
    let unit = try lowered(l, [Statement(name: "T.witness", root: root, proof: proof, theory: "Test")])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
