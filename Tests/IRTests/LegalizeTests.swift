import Testing
import IR

private let o = IRType.o

/// A schema's letter, as fol-zfc writes one: `⋀P::o`, its ⋀-intro and the letter `isaBound(k, o)`.
private struct L {
    var t = Table()
    mutating func n(_ node: Node) throws -> NodeID { try t.intern(node) }
    mutating func letter() throws -> NodeID { try n(.isaBound(0, o)) }
    /// `⋀P. P ⟹ P`
    mutating func identity() throws -> NodeID { try n(.ifolAll(o, body: try n(.folImplies(try letter(), try letter())))) }
    /// its proof: the letter's intro, `⟹`-intro, the hypothesis
    mutating func identityProof() throws -> NodeID {
        try n(.isaAllIntro(o, body: try n(.folImpliesIntro(try letter(), body: try n(.hyp(0, try letter()))))))
    }
}

/// `∀x. set(x) → ⋀P. P ⟹ P` and its proof: Fol's guard keeps the letter on its statement's spine, and the letter's
/// intro on its proof's.
@Test func aLetterUnderFolsGuardIsOnItsSpine() throws {
    var l = L()
    let set = try l.n(.folPred("set", args: [try l.n(.folBound(0))]))
    let root = try l.n(.folForall(body: try l.n(.folImplies(set, try l.identity()))))
    let proof = try l.n(.folForallIntro(body: try l.n(.folImpliesIntro(set, body: try l.identityProof()))))
    #expect(l.t.conclusion(of: proof) == root)
    #expect(misplacedLetters([root, proof], in: l.t).isEmpty)
}

/// `(⋀P. P ⟹ P) ⟹ ⊥`: a letter binder on the left of `⟹` has no schema to bind it.
@Test func aLetterBinderOnTheLeftOfAnImplicationIsOffItsSpine() throws {
    var l = L()
    let root = try l.n(.folImplies(try l.identity(), try l.n(.folBottom)))
    #expect(misplacedLetters([root], in: l.t) == [.ifolAll(o, body: o)])
}

/// `((⋀P. P ⟹ P) ⟹ ⊥) ⟹ ⊥`, by applying the hypothesis to the letter's own proof: that proof is no schema's, and the
/// hypothesis binds a letter below its top.
@Test func aLettersIntroInsideAProofIsOffItsSpine() throws {
    var l = L()
    let h = try l.n(.folImplies(try l.identity(), try l.n(.folBottom)))
    let proof = try l.n(.folImpliesIntro(h, body: try l.n(.folImpliesElim(try l.n(.hyp(0, h)), try l.identityProof()))))
    #expect(misplacedLetters([proof], in: l.t) == [.ifolAll(o, body: o), .isaAllIntro(o, body: o)])
}

/// An instantiation stands on a citation's spine, through `forall_elim` and `implies_elim`; one of a hypothesis
/// does not.
@Test func anInstantiationOfACitationIsOnItsSpineAndOfAHypothesisIsNot() throws {
    var l = L()
    let s = try l.identity(), c = try l.n(.folPred("C", args: []))
    #expect(misplacedLetters([try l.n(.folSchemaInst(try l.n(.use(.theorem("id"), [], s)), c))], in: l.t).isEmpty)
    let x = try l.n(.folBound(0)), set = try l.n(.folPred("set", args: [x]))
    let guarded = try l.n(.folForall(body: try l.n(.folImplies(set, s))))
    let atX = try l.n(.folImpliesElim(try l.n(.folForallElim(try l.n(.use(.theorem("gid"), [], guarded)), x)), try l.n(.hyp(0, set))))
    #expect(misplacedLetters([try l.n(.folSchemaInst(atX, c))], in: l.t).isEmpty)
    let ofHypothesis = try l.n(.folImpliesIntro(s, body: try l.n(.folSchemaInst(try l.n(.hyp(0, s)), c))))
    #expect(misplacedLetters([ofHypothesis], in: l.t) == [.ifolAll(o, body: o), .folSchemaInst(o, o)])
}
