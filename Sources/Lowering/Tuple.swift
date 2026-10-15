import IR

func tuple(_ xs: [NodeID], _ target: NodeID, in t: inout Table) throws -> NodeID {
    guard let last = xs.last else { return try t.intern(.folPred(.base("zero"), args: [target])) }
    var c = Chain()
    let empty = c.bind(.set)
    c.constrain(empty, try c.predicate(.base("zero"), [empty], in: &t))
    var index = empty, prefix = empty
    for x in xs.dropLast() {
        let next = c.bind(.set)
        c.constrain(next, try c.predicate(.base("nsucc"), [index, next], in: &t))
        let grown = c.bind(.set)
        c.constrain(grown, try c.predicate(.base("snoc"), [prefix, index, .outer(x), grown], in: &t))
        (index, prefix) = (next, grown)
    }
    return try c.formula(try c.predicate(.base("snoc"), [prefix, index, .outer(last), .outer(target)], in: &t), in: &t)
}
