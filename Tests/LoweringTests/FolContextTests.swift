import IR
import Testing
@testable import Lowering

private struct Walk {
    init() throws {
        var t = Table()
        rule = FolRule(base: try base(in: &t))
        bottom = try t.intern(.folBottom)
        assumption = .folImpliesIntro(bottom, body: try t.intern(.hyp(0, bottom)))
        let x = try t.intern(.isaBound(0, .i))
        quantifier = .ifolAll(.i, body: try t.intern(.folPred(.base("set"), args: [x])))
        fix = .folForallIntro(body: try t.intern(.hyp(0, bottom)))
        self.t = t
    }

    var t: Table
    let rule: FolRule
    let bottom: NodeID
    let assumption: Node
    let quantifier: Node
    let fix: Node

    func entered(_ c: FolRule.Context, _ binders: [Node]) -> FolRule.Context {
        binders.reduce(c) { c, b in
            rule.enter(c, b, b == assumption ? .hyp : .term, in: t)
        }
    }

    mutating func citing(hypothesis k: Int) throws -> NodeID {
        try t.intern(.hyp(k, bottom))
    }

    mutating func instance(atTerm k: Int) throws -> NodeID {
        let p = try t.intern(.use(.theorem("p"), [], try t.intern(.ifolAll(.i, body: bottom))))
        return try t.intern(.isaAllElim(p, try t.intern(.isaBound(k, .i))))
    }
}

/// ⚠ A CONTEXT COPIED INTO EACH KEY IS AS LONG AS THE PROOF IS DEEP: `Bin.integ_of_add`'s keys held up to 2,271
/// binders each, 9 GB across one walk.
@Test
func aStepsContextHoldsTheBindersItWasEnteredWithNeverACopy() throws {
    var w = try Walk()
    let c = w.entered(w.rule.start, Array(repeating: w.assumption, count: 1000))
    let narrowed = w.rule.narrow(c, try w.citing(hypothesis: 999), in: w.t)
    #expect(narrowed.reach == 1000)
    #expect(narrowed.innermost === c.innermost)
    #expect(w.rule.narrow(c, try w.citing(hypothesis: 2), in: w.t).innermost === c.innermost)
}

@Test
func twoChainsAlikeWithinAStepsReachAreOneKeyWhateverLiesOutsideIt() throws {
    var w = try Walk()
    let three = Array(repeating: w.assumption, count: 3)
    let underATerm = w.entered(w.entered(w.rule.start, [w.fix]), three)
    let underAHypothesis = w.entered(w.entered(w.rule.start, [w.assumption]), three)
    let step = try w.citing(hypothesis: 2)
    let a = w.rule.narrow(underATerm, step, in: w.t)
    let b = w.rule.narrow(underAHypothesis, step, in: w.t)
    #expect(a.innermost !== b.innermost)
    #expect(a == b)
    #expect(a.hashValue == b.hashValue)
    #expect(Set([a, b]).count == 1)
}

@Test
func twoChainsUnlikeWithinAStepsReachAreTwoKeys() throws {
    var w = try Walk()
    let instance = try w.instance(atTerm: 0)
    let guarded = w.rule.narrow(w.entered(w.rule.start, [w.quantifier]), instance, in: w.t)
    let unguarded = w.rule.narrow(w.entered(w.rule.start, [w.fix]), instance, in: w.t)
    #expect(guarded.reach == 1)
    #expect(unguarded.reach == 1)
    #expect(guarded != unguarded)
}

@Test
func aFormulasContextIsTheEmptyOne() throws {
    var w = try Walk()
    let c = w.entered(w.rule.start, [w.fix, w.assumption, w.fix])
    let formula = try w.t.intern(.folPred(.base("set"), args: [try w.t.intern(.folBound(1))]))
    #expect(w.rule.narrow(c, formula, in: w.t) == w.rule.start)
    #expect(w.rule.narrow(c, try w.instance(atTerm: 1), in: w.t) != w.rule.start)
}
