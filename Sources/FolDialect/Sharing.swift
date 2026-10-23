import IR

struct Loose {
    let terms: [Int32]
    let hyps: [Int32]
}

enum Occurrence: Hashable {
    case bound(key: Int32, hyp: Bool)
    case closed(NodeID, hyp: Bool, index: Int32)
}

struct Key: Hashable {
    let node: NodeID
    let occurrences: [Int32]
}

private struct Shifted: Hashable {
    let node: NodeID
    let terms: Int
    let hyps: Int
}

struct Closure {
    let terms: [Int32]
    let hyps: [Int32]
    let block: Int32
    let key: Int32
}

/// Each step of a proof as the writer meets it — its node and the binders its loose indices name, a key — gathered
/// before writing: a key is placed in the innermost block holding its uses, and a node met under keys that differ is
/// closed over the indices they differ in where that writes fewer lines.
final class Sharing {
    init(_ root: NodeID, in t: Table) throws {
        self.t = t
        parent = [-1]
        depth = [0]
        try survey(root)
    }

    let t: Table
    private(set) var loose = [NodeID: Loose]()
    private(set) var keys = [Key: Int32]()
    private(set) var placement = [Int32]()
    private(set) var opened = [Int32]()
    private(set) var parent: [Int32]
    private(set) var closures = [NodeID: Closure]()

    func occurrence(_ o: Occurrence) -> Int32 {
        if let k = occurrences[o] { return k }
        let k = Int32(occurrences.count)
        occurrences[o] = k
        return k
    }

    /// A hypothesis node of `x`'s proof naming `x`'s loose hypothesis `j`, and the term binders between it and `x`.
    func hypothesis(_ x: NodeID, _ j: Int32) throws -> (formula: NodeID, below: Int) {
        var seen = Set<Shifted>()
        var work = [(x, 0, 0)]
        while let (y, st, sh) = work.popLast() {
            guard seen.insert(Shifted(node: y, terms: st, hyps: sh)).inserted else { continue }
            if case .hyp(let k, let a) = t[y], k == Int(j) + sh { return (a, st) }
            for (c, binds) in premises(y) where loose[c]?.hyps.contains(j + Int32(sh + binds.hyps)) == true {
                work.append((c, st + binds.terms, sh + binds.hyps))
            }
        }
        throw RenderError.unsurveyed(x)
    }

    func looseSet(_ x: NodeID) throws -> Loose {
        if let l = loose[x] { return l }
        var work = [(x, false)]
        while let (y, done) = work.popLast() {
            if loose[y] != nil { continue }
            let n = t[y]
            if !done {
                work.append((y, true))
                n.forEachChild { c, _ in if loose[c] == nil { work.append((c, false)) } }
                continue
            }
            var terms = Set<Int32>()
            var hyps = Set<Int32>()
            if let v = n.boundVariable {
                if v.namespace == .term { terms.insert(Int32(v.index)) } else { hyps.insert(Int32(v.index)) }
            }
            var missing = false
            n.forEachChild { c, binds in
                guard let lc = loose[c] else {
                    missing = true
                    return
                }
                for j in lc.terms where j >= binds.terms { terms.insert(j - Int32(binds.terms)) }
                for j in lc.hyps where j >= binds.hyps { hyps.insert(j - Int32(binds.hyps)) }
            }
            if missing { throw RenderError.unsurveyed(y) }
            loose[y] = Loose(terms: terms.sorted(), hyps: hyps.sorted())
        }
        guard let l = loose[x] else { throw RenderError.unsurveyed(x) }
        return l
    }

    func premises(_ x: NodeID) -> [(NodeID, Binds)] {
        switch t[x] {
        case .folAndIntro(let p, let q), .folImpliesElim(let p, let q), .folNotElim(let p, let q),
             .folIffIntro(let p, let q), .folIffElimL(let p, let q), .folIffElimR(let p, let q):
            [(p, .none), (q, .none)]

        case .folAndElimL(let p), .folAndElimR(let p), .folOrIntroL(let p, _), .folForallElim(let p, _),
             .folExistsIntro(let p, _), .folBottomElim(let p, _):
            [(p, .none)]

        case .folOrIntroR(_, let q):
            [(q, .none)]

        case .folOrElim(let p, let q, let r):
            [(p, .none), (q, .none), (r, .none)]

        case .folImpliesIntro(_, let body), .folNotIntro(_, let body), .folClassicalAbsurd(_, let body):
            [(body, .hyp)]

        case .folForallIntro(let body), .isaAllIntro(.o, let body):
            [(body, .term)]

        case .folExistsElim(let p, let body):
            [(p, .none), (body, .termAndHyp)]

        case .folCut(let p, let body):
            [(p, .none), (body, .hyp)]

        case .valueElim(_, let p, let body):
            [(p, .none), (body, .none)]

        case .folSchemaInst:
            chain(x).premises.map { ($0, .none) }

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
             .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies,
             .folAnd, .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .value,
             .valueFact, .folNot, .folBound, .folPred, .folForall, .folExists, .folLetterAll, .folLetter,
             .folLetterAbs:
            []
        }
    }

    /// A schema instance's links below `x`, the premises its `implies_elim`s cite.
    func chain(_ x: NodeID) -> (links: Int, premises: [NodeID]) {
        var links = 0
        var found = [NodeID]()
        var head = x
        while true {
            if case .folSchemaInst(let p, _) = t[head] {
                head = p
            } else if case .folForallElim(let p, _) = t[head] {
                links += 1
                head = p
            } else if case .folImpliesElim(let p, let q) = t[head] {
                links += 1
                found.append(q)
                head = p
            } else {
                return (links, found.reversed())
            }
        }
    }

    private var occurrences = [Occurrence: Int32]()
    private var keyOccurrences = [[Int32]]()
    private var formulaNodes = [NodeID: Int]()
    private var depth: [Int32]

    private func survey(_ root: NodeID) throws {
        var uses: [NodeID: [(occurrences: [Int32], block: Int32)]] = [root: [([], 0)]]
        for x in try order(root) {
            guard let met = uses.removeValue(forKey: x) else { continue }
            _ = try looseSet(x)
            var distinct = [[Int32]]()
            var blocks = [[Int32]: [Int32]]()
            for (o, b) in met {
                if blocks[o] == nil { distinct.append(o) }
                blocks[o, default: []].append(b)
            }
            var placed = [(key: Int32, block: Int32, occurrences: [Int32])]()
            if distinct.count > 1, let c = try closure(x, distinct, blocks) {
                placed = [(c.key, c.block, keyOccurrences[Int(c.key)])]
            } else {
                for o in distinct {
                    let b = try lca(blocks[o]!)
                    placed.append((try keyed(x, o, at: b), b, o))
                }
            }
            for (k, b, o) in placed {
                var inner = b
                if opensABlock(t[x]) {
                    inner = newBlock(under: b)
                    opened[Int(k)] = inner
                }
                for (c, binds) in premises(x) {
                    let childOccurrences = try resolved(c, under: binds, from: x, o, k)
                    uses[c, default: []].append((childOccurrences, isInside(c, of: x, binds) ? inner : b))
                }
            }
        }
    }

    /// Whether `c`, a premise of `x`, stands in the block `x` opens: a binder's body — `valueElim`'s too, binding no
    /// index.
    private func isInside(_ c: NodeID, of x: NodeID, _ binds: Binds) -> Bool {
        if case .valueElim(_, _, let body) = t[x] { return c == body }
        return binds != .none
    }

    private func closure(_ x: NodeID, _ distinct: [[Int32]], _ blocks: [[Int32]: [Int32]]) throws
        -> Closure?
    {
        let l = try looseSet(x)
        var dTerms = [Int32]()
        var dHyps = [Int32]()
        for p in 0..<(l.terms.count + l.hyps.count) where distinct.contains(where: { $0[p] != distinct[0][p] }) {
            if p < l.terms.count { dTerms.append(l.terms[p]) } else { dHyps.append(l.hyps[p - l.terms.count]) }
        }
        let d = dTerms.count + dHyps.count
        var cost = dTerms.count * (fixBytes + lineBytes) + distinct.count * d * lineBytes
        for j in dHyps { cost += 2 * lineBytes + formulaBytes(try hypothesis(x, j).formula) }
        let needed = cost / (distinct.count - 1) + 1
        guard try dependentBytes(x, Set(dTerms), Set(dHyps), upTo: needed) >= needed else { return nil }
        var instances = [Int32]()
        for o in distinct {
            let b = try lca(blocks[o]!)
            _ = try keyed(x, o, at: b)
            instances.append(b)
        }
        let block = newBlock(under: try lca(instances))
        var closed = distinct[0]
        for (p, j) in (l.terms + l.hyps).enumerated() where distinct.contains(where: { $0[p] != distinct[0][p] }) {
            closed[p] = occurrence(.closed(x, hyp: p >= l.terms.count, index: j))
        }
        let c = Closure(
            terms: dTerms.sorted(by: >),
            hyps: dHyps.sorted(by: >),
            block: block,
            key: try keyed(x, closed, at: block),
        )
        closures[x] = c
        return c
    }

    private func keyed(_ x: NodeID, _ o: [Int32], at block: Int32) throws -> Int32 {
        let key = Key(node: x, occurrences: o)
        if let k = keys[key] { return k }
        let k = Int32(placement.count)
        keys[key] = k
        keyOccurrences.append(o)
        placement.append(block)
        opened.append(-1)
        return k
    }

    private func newBlock(under b: Int32) -> Int32 {
        parent.append(b)
        depth.append(depth[Int(b)] + 1)
        return Int32(parent.count - 1)
    }

    private func lca(_ blocks: [Int32]) throws -> Int32 {
        guard var a = blocks.first else { throw RenderError.unsurveyed(nil) }
        for var b in blocks.dropFirst() {
            while depth[Int(a)] > depth[Int(b)] { a = parent[Int(a)] }
            while depth[Int(b)] > depth[Int(a)] { b = parent[Int(b)] }
            while a != b {
                a = parent[Int(a)]
                b = parent[Int(b)]
            }
        }
        return a
    }

    /// `c`'s occurrences below `x`, keyed `k` at `o`: an index `x` binds over `c` names `x`'s own binder there.
    private func resolved(_ c: NodeID, under binds: Binds, from x: NodeID, _ o: [Int32], _ k: Int32) throws
        -> [Int32]
    {
        let lx = try looseSet(x)
        let lc = try looseSet(c)
        var found = [Int32]()
        for j in lc.terms {
            if j < binds.terms {
                found.append(occurrence(.bound(key: k, hyp: false)))
            } else {
                guard let p = lx.terms.firstIndex(of: j - Int32(binds.terms)) else { throw RenderError.unsurveyed(c) }
                found.append(o[p])
            }
        }
        for j in lc.hyps {
            if j < binds.hyps {
                found.append(occurrence(.bound(key: k, hyp: true)))
            } else {
                guard let p = lx.hyps.firstIndex(of: j - Int32(binds.hyps)) else { throw RenderError.unsurveyed(c) }
                found.append(o[lx.terms.count + p])
            }
        }
        return found
    }

    /// The text `x`'s proof writes again under each key its indices `terms` and `hyps` tell apart, estimated, counted
    /// up
    /// to `limit`.
    private func dependentBytes(_ x: NodeID, _ terms: Set<Int32>, _ hyps: Set<Int32>, upTo limit: Int) throws -> Int {
        var bytes = 0
        var seen = Set<Shifted>()
        var work = [(x, 0, 0)]
        while bytes < limit, let (y, st, sh) = work.popLast() {
            guard seen.insert(Shifted(node: y, terms: st, hyps: sh)).inserted else { continue }
            let l = try looseSet(y)
            let depends = l.terms.contains { $0 >= st && terms.contains($0 - Int32(st)) }
                || l.hyps.contains { $0 >= sh && hyps.contains($0 - Int32(sh)) }
            guard depends else { continue }
            bytes += weight(y)
            for (c, binds) in premises(y) { work.append((c, st + binds.terms, sh + binds.hyps)) }
        }
        return bytes
    }

    private func order(_ root: NodeID) throws -> [NodeID] {
        var post = [NodeID]()
        var state = [NodeID: Bool]()
        var work = [(root, false)]
        while let (x, done) = work.popLast() {
            if done {
                post.append(x)
                continue
            }
            guard state[x] == nil else { continue }
            state[x] = true
            work.append((x, true))
            for (c, _) in premises(x).reversed() where state[c] == nil { work.append((c, false)) }
        }
        return post.reversed()
    }

    /// The text `x` writes itself, estimated: a line, and the formulas its lines state.
    private func weight(_ x: NodeID) -> Int {
        switch t[x] {
        case .folImpliesIntro(let a, _), .folNotIntro(let a, _), .folClassicalAbsurd(let a, _), .folOrIntroL(_, let a),
             .folOrIntroR(let a, _), .folBottomElim(_, let a):
            2 * lineBytes + formulaBytes(a)

        case .folForallIntro:
            fixBytes + lineBytes

        case .folExistsElim, .valueElim:
            2 * lineBytes

        case .folSchemaInst:
            (1 + chain(x).links) * lineBytes + letterInstances(x).reduce(0) { $0 + formulaBytes($1) }

        case .folCut, .hyp, .isaAllIntro, .valueFact:
            0

        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllElim,
             .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies,
             .folAnd, .folOr, .folIff, .folBottom, .use, .isaGuard, .isaExIntro, .isaExElim, .value,
             .folNot, .folBound, .folPred, .folForall, .folExists, .folLetterAll, .folLetter,
             .folLetterAbs, .folImpliesElim, .folAndIntro, .folAndElimL, .folAndElimR, .folOrElim, .folNotElim,
             .folIffIntro, .folIffElimL, .folIffElimR, .folForallElim, .folExistsIntro:
            lineBytes
        }
    }

    private func letterInstances(_ x: NodeID) -> [NodeID] {
        var found = [NodeID]()
        var head = x
        while true {
            switch t[head] {
            case .folSchemaInst(let p, let a):
                found.append(a)
                head = p

            case .folForallElim(let p, _), .folImpliesElim(let p, _):
                head = p

            case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
                 .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract,
                 .isaClassical, .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound,
                 .isaHidden, .folImplies, .folAnd, .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro,
                 .isaExElim, .value, .valueFact, .valueElim, .folNot, .folBound, .folPred, .folForall, .folExists,
                 .folLetterAll, .folLetter, .folLetterAbs, .folImpliesIntro, .folAndIntro, .folAndElimL,
                 .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
                 .folIffElimL, .folIffElimR, .folForallIntro, .folExistsIntro, .folExistsElim, .folCut,
                 .folBottomElim, .folClassicalAbsurd:
                return found
            }
        }
    }

    /// A formula's text, estimated by its nodes as a tree.
    private func formulaBytes(_ x: NodeID) -> Int {
        var work = [(x, false)]
        while let (y, done) = work.popLast() {
            if formulaNodes[y] != nil { continue }
            if case .value = t[y] {
                formulaNodes[y] = 1
                continue
            }
            if !done {
                work.append((y, true))
                t[y].forEachChild { c, _ in if formulaNodes[c] == nil { work.append((c, false)) } }
                continue
            }
            var n = 1
            t[y].forEachChild { c, _ in n = min(n + (formulaNodes[c] ?? 0), 1 << 40) }
            formulaNodes[y] = n
        }
        return nodeBytes * (formulaNodes[x] ?? 0)
    }
}

private let lineBytes = 32
private let fixBytes = 12
private let nodeBytes = 7

func opensABlock(_ n: Node) -> Bool {
    switch n {
    case .folForallIntro, .folImpliesIntro, .folNotIntro, .folClassicalAbsurd, .folExistsElim, .valueElim:
        true
    case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
         .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
         .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies,
         .folAnd, .folOr, .folIff, .folBottom, .use, .hyp, .isaGuard, .isaExIntro, .isaExElim, .value,
         .valueFact, .folNot, .folBound, .folPred, .folForall, .folExists, .folLetterAll, .folLetter,
         .folLetterAbs, .folImpliesElim, .folAndIntro, .folAndElimL, .folAndElimR, .folOrIntroL, .folOrIntroR,
         .folOrElim, .folNotElim, .folIffIntro, .folIffElimL, .folIffElimR, .folForallElim, .folExistsIntro,
         .folCut, .folBottomElim, .folSchemaInst:
        false
    }
}
