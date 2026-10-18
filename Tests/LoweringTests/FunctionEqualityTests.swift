import IR
import Lowering
import Testing

private let i = IRType.i
private let o = IRType.o
private let P = IRType.fn(.i, .o)
private func fn(_ a: IRType, _ b: IRType) -> IRType {
    .fn(a, b)
}

private func lowered(_ l: LogicTable, _ statements: [Statement], _ definitions: [Definition] = []) throws -> Unit {
    var l = l
    let b = try base(in: &l.t)
    var unit = Unit(table: l.t, statements: statements, definitions: definitions)
    try pipeline(b).run(&unit)
    return unit
}

private func pow(_ x: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.const(.primitive(.zf(.pow)), fn(i, i), x)
}

private func applied(_ head: NodeID, _ x: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.t.intern(.isaVarApp(head: head, args: [x]))
}

private func iff(_ a: NodeID, _ b: NodeID, _ l: inout LogicTable) throws -> NodeID {
    try l.t.intern(.folIff(a, b))
}

/// `⋀` over `T` `n` times, in a statement's root and in its proof alike.
private func closed(
    _ n: Int,
    _ T: IRType,
    _ root: NodeID,
    _ proof: NodeID,
    _ l: inout LogicTable,
) throws -> (root: NodeID, proof: NodeID) {
    var r = root
    var p = proof
    for _ in 0..<n { (r, p) = (try l.all(T, r), try l.t.intern(.isaAllIntro(T, body: p))) }
    return (r, p)
}

private func statement(_ name: String, _ closed: (root: NodeID, proof: NodeID)) -> Statement {
    Statement(name: name, root: closed.root, proof: closed.proof, theory: "Test")
}

/// `λQ. ∀y. y ∈ A ⟶ Q(y)`, a function of classes, `A` the bound variable `k` outside it.
private func bounded(_ k: Int, _ l: inout LogicTable) throws -> NodeID {
    try l.lam(P, try l.all(i, try l.imp(
        try l.mem(try l.bound(0, i), try l.bound(k + 2, i)),
        try applied(try l.bound(1, P), try l.bound(0, i), &l),
    )))
}

/// `T.ball ≡ λA P. ∀x. x ∈ A ⟶ P(x)`: a constant taking a class.
private func ball(_ l: inout LogicTable) throws -> Definition {
    let x = try l.bound(0, i)
    return try l.definition(
        Defined(.zf, "T.ball", .object),
        fn(i, fn(P, o)),
        try l.lam(i, try l.lam(P, try l.all(i, try l.imp(
            try l.mem(x, try l.bound(2, i)),
            try applied(try l.bound(1, P), x, &l),
        )))),
    )
}

/// Decision 1: `f ≡ g` and `⋀x. f x ≡ g x` are one formula — at a predicate, at a function and at a function of
/// classes.
@Test
func anEquationBetweenFunctionsIsItsPointwiseFormula() throws {
    var l = LogicTable()
    let b = try base(in: &l.t)
    let x = try l.bound(0, i)
    let inA = try l.lam(i, try l.mem(x, try l.bound(2, i)))
    let inB = try l.lam(i, try l.mem(x, try l.bound(1, i)))
    let predicates = try l.all(i, try l.all(i, try l.equal(P, inA, inB)))
    let pointwisePredicates = try l.all(i, try l.all(i, try l.all(
        i,
        try iff(try l.mem(x, try l.bound(2, i)), try l.mem(x, try l.bound(1, i)), &l),
    )))
    let powers = try l.equal(fn(i, i), try l.lam(i, try pow(x, &l)), try l.lam(i, try pow(x, &l)))
    let pointwisePowers = try l.all(i, try l.equal(i, try pow(x, &l), try pow(x, &l)))
    let classes = try l.all(i, try l.equal(fn(P, o), try bounded(0, &l), try bounded(0, &l)))
    let body = try l.all(i, try l.imp(
        try l.mem(try l.bound(0, i), try l.bound(2, i)),
        try applied(try l.bound(1, P), try l.bound(0, i), &l),
    ))
    let pointwiseClasses = try l.all(i, try l.all(P, try iff(body, body, &l)))
    let out = try Logic(base: b).run(
        [predicates, pointwisePredicates, powers, pointwisePowers, classes, pointwiseClasses],
        [],
        in: &l.t,
    )
    #expect(out[0] == out[1])
    #expect(out[2] == out[3])
    #expect(out[4] == out[5])
}

/// `reflexive` at a predicate, a function and a function of classes, `symmetric` and `transitive` at a predicate: each
/// the base type's rule under the pointwise binders. The kernel proves the unit.
@Test
func reflexiveSymmetricAndTransitiveAtAFunctionArePointwise() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let inA = try l.lam(i, try l.mem(x, try l.bound(1, i)))
    let atPredicate = try closed(1, i, try l.equal(P, inA, inA), try l.t.intern(.isaReflexive(inA)), &l)
    let power = try l.lam(i, try pow(x, &l))
    let atFunction = (root: try l.equal(fn(i, i), power, power), proof: try l.t.intern(.isaReflexive(power)))
    let classes = try bounded(0, &l)
    let atClasses = try closed(
        1,
        i,
        try l.equal(fn(P, o), classes, classes),
        try l.t.intern(.isaReflexive(classes)),
        &l,
    )
    let fA = try l.lam(i, try l.mem(x, try l.bound(3, i)))
    let fB = try l.lam(i, try l.mem(x, try l.bound(2, i)))
    let fC = try l.lam(i, try l.mem(x, try l.bound(1, i)))
    let ab = try l.equal(P, fA, fB)
    let bc = try l.equal(P, fB, fC)
    let symmetric = try closed(3, i, try l.imp(ab, try l.equal(P, fB, fA)), try l.t.intern(.folImpliesIntro(
        ab,
        body: try l.t.intern(.isaSymmetric(P, try l.t.intern(.hyp(0, ab)))),
    )), &l)
    let transitive = try closed(
        3,
        i,
        try l.imp(ab, try l.imp(bc, try l.equal(P, fA, fC))),
        try l.t.intern(.folImpliesIntro(ab, body: try l.t.intern(.folImpliesIntro(
            bc,
            body: try l.t.intern(.isaTransitive(P, try l.t.intern(.hyp(1, ab)), try l.t.intern(.hyp(0, bc)))),
        )))),
        &l,
    )
    let unit = try lowered(l, [
        statement("T.atPredicate", atPredicate),
        statement("T.atFunction", atFunction),
        statement("T.atClasses", atClasses),
        statement("T.symmetric", symmetric),
        statement("T.transitive", transitive),
    ])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `abstract_rule` from `⋀x. x ∈ A ↔ x ∈ B` concludes `(λx. x ∈ A) ≡ (λx. x ∈ B)`: one formula, so its proof is its
/// premise's. The kernel proves the unit.
@Test
func abstractRuleConcludesItsPremise() throws {
    var l = LogicTable()
    let x = try l.bound(0, i)
    let premise = try l.all(i, try iff(try l.mem(x, try l.bound(2, i)), try l.mem(x, try l.bound(1, i)), &l))
    let abstracted = try l.equal(P, try l.lam(i, try l.mem(x, try l.bound(2, i))), try l.lam(
        i,
        try l.mem(x, try l.bound(1, i)),
    ))
    let rule = try l.t.intern(.isaAbstract(P, try l.t.intern(.hyp(0, premise))))
    let proof = try closed(2, i, try l.imp(premise, abstracted), try l.t.intern(.folImpliesIntro(
        premise,
        body: rule,
    )), &l)
    var logic = l
    let out = try Logic(base: try base(in: &logic.t)).run([rule, premise], [], in: &logic.t)
    #expect(out[0] == (try logic.t.intern(.hyp(0, out[1]))))
    let unit = try lowered(l, [statement("T.abstract", proof)])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `combination` at a set argument: the premise at the argument, then the argument's equation substituted into the
/// function — `a ∈ A ↔ a ∈ B` through the curried chain of `mem`, at a compound argument (`Pow(a) ∈ B`), and at a
/// function's value (`Pow(a) = Pow(b)`). The kernel proves the unit.
@Test
func combinationAtASetArgumentSubstitutesIntoTheFunction() throws {
    var l = LogicTable()
    let mem = try l.lam(i, try l.lam(i, try l.mem(try l.bound(1, i), try l.bound(0, i))))
    let AB = try l.equal(i, try l.bound(1, i), try l.bound(0, i))
    let section = try l.t.intern(.isaCombination(
        fn(i, P),
        try l.t.intern(.isaReflexive(mem)),
        try l.t.intern(.isaReflexive(try l.bound(2, i))),
    ))
    let rewritten = try l.t.intern(.isaCombination(P, section, try l.t.intern(.hyp(0, AB))))
    let members = try closed(
        3,
        i,
        try l.imp(AB, try iff(
            try l.mem(try l.bound(2, i), try l.bound(1, i)),
            try l.mem(try l.bound(2, i), try l.bound(0, i)),
            &l,
        )),
        try l.t.intern(.folImpliesIntro(AB, body: rewritten)),
        &l,
    )
    let ab = try l.equal(i, try l.bound(2, i), try l.bound(1, i))
    let inB = try l.lam(i, try l.mem(try pow(try l.bound(0, i), &l), try l.bound(1, i)))
    let compound = try closed(
        3,
        i,
        try l.imp(ab, try iff(
            try l.mem(try pow(try l.bound(2, i), &l), try l.bound(0, i)),
            try l.mem(try pow(try l.bound(1, i), &l), try l.bound(0, i)),
            &l,
        )),
        try l.t.intern(.folImpliesIntro(
            ab,
            body: try l.t.intern(.isaCombination(P, try l.t.intern(.isaReflexive(inB)), try l.t.intern(.hyp(0, ab)))),
        )),
        &l,
    )
    let ab2 = try l.equal(i, try l.bound(1, i), try l.bound(0, i))
    let power = try l.lam(i, try pow(try l.bound(0, i), &l))
    let value = try closed(
        2,
        i,
        try l.imp(ab2, try l.equal(i, try pow(try l.bound(1, i), &l), try pow(try l.bound(0, i), &l))),
        try l.t.intern(.folImpliesIntro(
            ab2,
            body: try l.t.intern(.isaCombination(
                fn(i, i),
                try l.t.intern(.isaReflexive(power)),
                try l.t.intern(.hyp(0, ab2)),
            )),
        )),
        &l,
    )
    let unit = try lowered(l, [
        statement("T.members", members),
        statement("T.compound", compound),
        statement("T.value", value),
    ])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `combination` at a class argument, `combination (reflexive g) (abstract_rule q)` with `g` a function of classes: one
/// applying its class variable, `λQ. ∀y. y ∈ A ⟶ Q(y)`, and one putting it in a constant's class slot,
/// `λQ. T.ball(A, λx. Q(x))`. Substitution walks `g`'s body, its holes the class variable's units. The kernel proves
/// the unit.
@Test
func combinationAtAClassArgumentSubstitutesIntoTheFunctionOfClasses() throws {
    var l = LogicTable()
    let ballDefinition = try ball(&l)
    let x = try l.bound(0, i)
    let premise = try l.all(i, try iff(try l.mem(x, try l.bound(2, i)), try l.mem(x, try l.bound(1, i)), &l))
    let abstracted = try l.t.intern(.isaAbstract(P, try l.t.intern(.hyp(0, premise))))
    let applying = try l.t.intern(.isaCombination(
        fn(P, o),
        try l.t.intern(.isaReflexive(try bounded(2, &l))),
        abstracted,
    ))
    let below = { (k: Int, l: inout LogicTable) throws -> NodeID in
        try l.all(i, try l.imp(try l.mem(try l.bound(0, i), try l.bound(3, i)), try l.mem(
            try l.bound(0, i),
            try l.bound(k, i),
        )))
    }
    let bounds = try closed(
        3,
        i,
        try l.imp(premise, try iff(try below(2, &l), try below(1, &l), &l)),
        try l.t.intern(.folImpliesIntro(premise, body: applying)),
        &l,
    )
    let slot = try l.lam(i, try applied(try l.bound(1, P), try l.bound(0, i), &l))
    let ballOf = { (A: NodeID, lambda: NodeID, l: inout LogicTable) throws -> NodeID in
        try l.const(.defined(ballDefinition.constant), fn(i, fn(P, o)), A, lambda)
    }
    let g = try l.lam(P, try ballOf(try l.bound(3, i), slot, &l))
    let slotted = try l.t.intern(.isaCombination(fn(P, o), try l.t.intern(.isaReflexive(g)), abstracted))
    let inB = try l.lam(i, try l.mem(x, try l.bound(2, i)))
    let inC = try l.lam(i, try l.mem(x, try l.bound(1, i)))
    let slots = try closed(
        3,
        i,
        try l.imp(premise, try iff(
            try ballOf(try l.bound(2, i), inB, &l),
            try ballOf(try l.bound(2, i), inC, &l),
            &l,
        )),
        try l.t.intern(.folImpliesIntro(premise, body: slotted)),
        &l,
    )
    let unit = try lowered(l, [statement("T.bounds", bounds), statement("T.slots", slots)], [ballDefinition])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}

/// `reflexive (λA. PrimReplace(A, λx y. y ∈ Pow(x)))` at `i ⇒ i`: the instance at the term reads it as Isabelle states
/// it, so its EX names the inner λ's class from the λ itself, never from the walk's naming of its body.
@Test
func reflexiveAtAFunctionInstantiatesTheTermAsStated() throws {
    var l = LogicTable()
    let y = try l.bound(0, i)
    let x = try l.bound(1, i)
    let relation = try l.lam(i, try l.lam(i, try l.mem(y, try pow(x, &l))))
    let replaced = try l.lam(i, try l.const(
        .primitive(.zf(.primReplace)),
        fn(i, fn(fn(i, fn(i, o)), i)),
        try l.bound(0, i),
        relation,
    ))
    let root = try l.equal(fn(i, i), replaced, replaced)
    let proof = try l.t.intern(.isaReflexive(replaced))
    let unit = try lowered(l, [Statement(name: "T.replaced", root: root, proof: proof, theory: "Test")])
    #expect(unit.refused.isEmpty, "\(unit.refused)")
    try kernelChecks(unit)
}
