@frozen
public enum TableError: Error, Equatable, Sendable {
    case unknownNode(NodeID)
    case negativeIndex(Int)
    case childType(expected: IRType, found: IRType)
    case predicateArgumentNotVariable(NodeID)
    case propositionAsTerm(NodeID)
    case functionArgumentNotAbstraction(NodeID)
    case arityMismatch(expected: Int, found: Int)
    case varAppHeadNotVariable(NodeID)
    case expectedValue(NodeID)
    case expectedStep(NodeID)
    case principalConnective(NodeID)
    case premiseMismatch(expected: NodeID, found: NodeID)
    case notATermVariable(NodeID)
    case witnessEscapes(NodeID)
    case notAFunctionType(IRType)
    case letterArity(NodeID)
}

public struct Table: Sendable {
    public init() { }

    public var count: Int {
        nodes.count
    }

    public subscript(_ id: NodeID) -> Node {
        nodes[Int(id.raw)]
    }

    public func type(of id: NodeID) -> IRType? {
        if case .value(let T) = sorts[Int(id.raw)] { return T }
        return nil
    }

    public func conclusion(of id: NodeID) -> NodeID? {
        if case .step(let c) = sorts[Int(id.raw)] { return c }
        return nil
    }

    public mutating func equation(_ T: IRType, _ a: NodeID, _ b: NodeID) throws -> NodeID {
        switch T {
        case .o: try intern(.folIff(a, b))
        case .i: try intern(.isaConst(.primitive(.ifol(.eq)), .fn(.i, .fn(.i, .o)), args: [a, b]))
        case .fn, .variable: try intern(.isaConst(.primitive(.pure(.eq)), .fn(T, .fn(T, .o)), args: [a, b]))
        }
    }

    public func sides(ofEquation formula: NodeID) -> (type: IRType, left: NodeID, right: NodeID)? {
        switch self[formula] {
        case .folIff(let a, let b):
            (.o, a, b)
        case .isaConst(.primitive(.ifol(.eq)), _, let args) where args.count == 2:
            (.i, args[0], args[1])
        case .isaConst(.primitive(.pure(.eq)), .fn(let T, _), let args) where args.count == 2:
            (T, args[0], args[1])
        case .ifolAll, .ifolEx, .isaConst, .isaFree, .isaBound, .isaVarApp, .isaAbs, .isaOfClass, .isaAllIntro,
             .isaAllElim, .isaReflexive, .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical,
             .isaIffReflection, .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImplies,
             .folAnd, .folOr, .folBottom, .folImpliesIntro, .folImpliesElim, .use, .hyp, .folIffIntro, .folIffElimL,
             .isaGuard, .isaExIntro, .isaExElim, .folNot, .folBound, .folPred, .folForall, .folExists, .folAndIntro,
             .folAndElimL, .folAndElimR,
             .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffElimR, .folForallIntro,
             .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim, .folClassicalAbsurd, .folSchemaInst,
             .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
            nil
        }
    }

    public func looseBound(of id: NodeID) -> Int {
        looseTerms[Int(id.raw)]
    }

    public func looseHyps(of id: NodeID) -> Int {
        looseHypotheses[Int(id.raw)]
    }

    public mutating func intern(_ n: Node) throws -> NodeID {
        if let id = index[n] { return id }
        try n.forEachChild { c, _ in
            guard Int(c.raw) < nodes.count else { throw TableError.unknownNode(c) }
        }
        let sort = try sortOf(n)
        var terms = 0
        var hyps = 0
        if let v = n.boundVariable {
            guard v.index >= 0 else { throw TableError.negativeIndex(v.index) }
            switch v.namespace {
            case .term: terms = v.index + 1
            case .hyp: hyps = v.index + 1
            }
        }
        n.forEachChild { c, binds in
            terms = max(terms, looseBound(of: c) - binds.terms)
            hyps = max(hyps, looseHyps(of: c) - binds.hyps)
        }
        let id = NodeID(raw: UInt32(nodes.count))
        nodes.append(n)
        sorts.append(sort)
        looseTerms.append(terms)
        looseHypotheses.append(hyps)
        index[n] = id
        return id
    }

    /// ⚠ NOT SWIFT'S `Hasher`: it is seeded per process, and a name made from it changes from run to run, silently.
    public func fingerprint(of id: NodeID) -> UInt64 {
        var known = [NodeID: UInt64]()
        return fingerprint(id, &known)
    }

    func patternType(of id: NodeID) -> IRType {
        switch sorts[Int(id.raw)] {
        case .value(let T): T
        case .step: .o
        }
    }

    private enum Sort: Sendable {
        case value(IRType)
        case step(concluding: NodeID)
    }

    private var nodes = [Node]()
    private var sorts = [Sort]()
    private var looseTerms = [Int]()
    private var looseHypotheses = [Int]()
    private var index = [Node: NodeID]()

    private mutating func sortOf(_ n: Node) throws -> Sort {
        switch n {
        case .folBound:
            return .value(.i)

        case .folPred(_, let xs):
            for x in xs { try termArgument(x, else: .predicateArgumentNotVariable(x)) }
            return .value(.o)

        case .folAnd(let a, let b), .folOr(let a, let b), .folImplies(let a, let b), .folIff(let a, let b):
            try expect(.o, a)
            try expect(.o, b)
            return .value(.o)

        case .folNot(let a), .folForall(let a), .folExists(let a),
             .ifolAll(_, let a), .ifolEx(_, let a):
            try expect(.o, a)
            return .value(.o)

        case .folBottom:
            return .value(.o)

        case .isaConst(_, let T, let xs):
            return .value(try apply(T, xs))

        case .isaFree(_, let T), .isaBound(_, let T):
            return .value(T)

        case .isaVarApp(let h, let xs):
            if case .isaFree = self[h] { return .value(try apply(try value(h), xs)) }
            if case .isaBound = self[h] { return .value(try apply(try value(h), xs)) }
            throw TableError.varAppHeadNotVariable(h)

        case .isaAbs(let T, let b):
            return .value(.fn(T, try value(b)))

        case .isaOfClass:
            return .value(.o)

        case .use(_, _, let a), .hyp(_, let a):
            try expect(.o, a)
            return .step(concluding: a)

        case .isaGuard(let x, let g):
            guard case .isaBound = self[x] else { throw TableError.notATermVariable(x) }
            try expect(.o, g)
            return .step(concluding: g)

        case .folAndIntro(let p, let q):
            return .step(concluding: try intern(.folAnd(try premise(p), try premise(q))))

        case .folAndElimL(let p):
            guard case .folAnd(let x, _) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            return .step(concluding: x)

        case .folAndElimR(let p):
            guard case .folAnd(_, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            return .step(concluding: y)

        case .folOrIntroL(let p, let b):
            try expect(.o, b)
            return .step(concluding: try intern(.folOr(try premise(p), b)))

        case .folOrIntroR(let a, let q):
            try expect(.o, a)
            return .step(concluding: try intern(.folOr(a, try premise(q))))

        case .folOrElim(let p, let q, let r):
            guard case .folOr(let x, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            let fromX = try implication(q, from: x)
            try same(fromX, try implication(r, from: y))
            return .step(concluding: fromX)

        case .folImpliesIntro(let a, let body):
            try expect(.o, a)
            return .step(concluding: try intern(.folImplies(a, try premise(body))))

        case .folImpliesElim(let p, let q):
            guard case .folImplies(let x, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            try same(x, try premise(q))
            return .step(concluding: y)

        case .folNotIntro(let a, let body):
            try expect(.o, a)
            try absurd(body)
            return .step(concluding: try intern(.folNot(a)))

        case .folNotElim(let p, let q):
            guard case .folNot(let x) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            try same(x, try premise(q))
            return .step(concluding: try intern(.folBottom))

        case .folIffIntro(let p, let q):
            guard case .folImplies(let x, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            try same(x, try implication(q, from: y))
            return .step(concluding: try intern(.folIff(x, y)))

        case .folIffElimL(let p, let q):
            guard case .folIff(let x, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            try same(x, try premise(q))
            return .step(concluding: y)

        case .folIffElimR(let p, let q):
            guard case .folIff(let x, let y) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            try same(y, try premise(q))
            return .step(concluding: x)

        case .folForallIntro(let body):
            return .step(concluding: try intern(.folForall(body: try premise(body))))

        case .folForallElim(let p, let v):
            try termArgument(v, else: .notATermVariable(v))
            let premised = try premise(p)
            if case .folForall(let body) = self[premised] { return .step(concluding: try instantiate(
                body,
                with: v,
                in: &self,
            )) }
            guard
                case .ifolAll(let T, let body) = self[premised],
                isObject(T)
            else { throw TableError.principalConnective(p) }
            return .step(concluding: try instantiate(try guardedBody(T, body, in: &self), with: v, in: &self))

        case .folExistsIntro(let p, let v):
            let k = try termVariable(v, else: .notATermVariable(v))
            return .step(concluding: try intern(.folExists(body: try abstractIndex(try premise(p), k, in: &self))))

        case .folExistsElim(let p, let body):
            guard case .folExists = self[try premise(p)] else { throw TableError.principalConnective(p) }
            return .step(concluding: try witnessed(body))

        case .isaExIntro(let p, let x, let body):
            let T = try value(x)
            guard T != .o else { throw TableError.propositionAsTerm(x) }
            try expect(.o, body)
            try same(try instantiate(body, with: x, in: &self), try premise(p))
            return .step(concluding: try intern(.ifolEx(T, body: body)))

        case .isaExElim(let T, let p, let body):
            guard case .ifolEx(T, _) = self[try premise(p)] else { throw TableError.principalConnective(p) }
            return .step(concluding: try witnessed(body))

        case .folBottomElim(let p, let c):
            try absurd(p)
            try expect(.o, c)
            return .step(concluding: c)

        case .folClassicalAbsurd(let a, let body):
            try expect(.o, a)
            try absurd(body)
            return .step(concluding: a)

        case .folSchemaInst(let p, let a):
            let schema = try premise(p)
            if case .folLetterAll(let k, let body) = self[schema] {
                try letterInstance(a, arity: k)
                return .step(concluding: try instantiate(body, with: a, in: &self))
            }
            guard case .ifolAll(.o, let body) = self[schema] else { throw TableError.principalConnective(p) }
            try expect(.o, a)
            return .step(concluding: try instantiate(body, with: a, in: &self))

        case .folLetterAll(_, let b):
            try expect(.o, b)
            return .value(.o)

        case .folLetter(let h, let xs):
            guard case .folBound = self[h] else { throw TableError.varAppHeadNotVariable(h) }
            for x in xs { try termArgument(x, else: .predicateArgumentNotVariable(x)) }
            return .value(.o)

        case .folLetterAbs(let b):
            try expect(.o, b)
            return .value(.o)

        case .isaReflexive(let x):
            return .step(concluding: try equation(try value(x), x, x))

        case .isaSymmetric(let T, let p):
            let (a, b) = try sides(p, at: T)
            return .step(concluding: try equation(T, b, a))

        case .isaTransitive(let T, let p, let q):
            let (a, b) = try sides(p, at: T), (b2, c) = try sides(q, at: T)
            try same(b, b2)
            return .step(concluding: try equation(T, a, c))

        case .isaCombination(let F, let p, let q):
            guard case .fn(let T, let U) = F else { throw TableError.notAFunctionType(F) }
            let (f, g) = try sides(p, at: F), (x, y) = try sides(q, at: T)
            return .step(concluding: try equation(U, try applied(f, x), try applied(g, y)))

        case .isaAbstract(let F, let p):
            guard case .fn(let T, let U) = F else { throw TableError.notAFunctionType(F) }
            guard
                case .ifolAll(let T2, let body) = self[try premise(p)], T2 == T,
                let (V, a, b) = sides(ofEquation: body), V == U
            else { throw TableError.principalConnective(p) }
            return .step(concluding: try equation(F, try intern(.isaAbs(T, body: a)), try intern(.isaAbs(T, body: b))))

        case .isaClassical(let a, let h):
            try expect(.o, a)
            guard case .folImplies(_, let c) = self[try premise(h)] else { throw TableError.principalConnective(h) }
            try same(a, c)
            return .step(concluding: a)

        case .isaIffReflection(let a, let b, let h):
            try expect(.o, a)
            try expect(.o, b)
            _ = try premise(h)
            return .step(concluding: try intern(.folIff(a, b)))

        case .isaAllIntro(let T, let body):
            return .step(concluding: try intern(.ifolAll(T, body: try premise(body))))

        case .isaPropIntro(let body):
            return .step(concluding: try intern(.isaPropAll(body: try premise(body))))

        case .isaHidden(_, let body):
            return .step(concluding: try witnessed(body))

        case .isaPropAll(let b):
            try expect(.o, b)
            return .value(.o)

        case .isaPropBound:
            return .value(.o)

        case .isaAllElim(let p, let x):
            if case .isaPropAll(let body) = self[try premise(p)] {
                try expect(.o, x)
                return .step(concluding: try instantiate(body, with: x, in: &self))
            }
            return .step(concluding: try instance(try premise(p), at: x, blaming: p))

        case .isaValue(let x):
            try expect(.i, x)
            return .value(.i)

        case .isaValueFact(let v, let a):
            guard case .isaValue = self[v] else { throw TableError.notATermVariable(v) }
            try expect(.o, a)
            return .step(concluding: a)

        case .isaDefinition(_, _, _, let stated, let xs):
            try expect(.o, stated)
            var concluded = stated
            for x in xs { concluded = try instance(concluded, at: x, blaming: stated) }
            return .step(concluding: concluded)
        }
    }

    private mutating func instance(_ formula: NodeID, at x: NodeID, blaming step: NodeID) throws -> NodeID {
        guard case .ifolAll(let T, let body) = self[formula] else { throw TableError.principalConnective(step) }
        try expect(T, x)
        if case .fn = T, !isAbstraction(x) { throw TableError.functionArgumentNotAbstraction(x) }
        return try instantiate(body, with: x, in: &self)
    }

    @discardableResult
    private func letterInstance(_ a: NodeID, arity k: Int) throws {
        var inner = a
        for _ in 0..<k {
            guard case .folLetterAbs(let b) = self[inner] else { throw TableError.letterArity(a) }
            inner = b
        }
        if case .folLetterAbs = self[inner] { throw TableError.letterArity(a) }
    }

    private func termArgument(_ x: NodeID, else notVariable: TableError) throws {
        if case .isaValue = self[x] { return }
        _ = try termVariable(x, else: notVariable)
    }

    @discardableResult
    private func termVariable(_ x: NodeID, else notVariable: TableError) throws -> Int {
        if case .folBound(let k) = self[x] { return k }
        guard case .isaBound(let k, let T) = self[x] else { throw notVariable }
        guard T != .o else { throw TableError.propositionAsTerm(x) }
        return k
    }

    private func fingerprint(_ id: NodeID, _ known: inout [NodeID: UInt64]) -> UInt64 {
        if let h = known[id] { return h }
        var h: UInt64 = 0xcbf2_9ce4_8422_2325
        func mix(_ bytes: some Sequence<UInt8>) {
            for b in bytes { h = (h ^ UInt64(b)) &* 0x100_0000_01b3 }
        }
        mix(String(describing: self[id].mapChildren { _, _ in NodeID(raw: 0) }).utf8)
        self[id].forEachChild { c, _ in withUnsafeBytes(of: fingerprint(c, &known).littleEndian) { mix($0) } }
        known[id] = h
        return h
    }

    private mutating func witnessed(_ body: NodeID) throws -> NodeID {
        do {
            return try unshift(try premise(body), in: &self)
        } catch IRRefusal.indexOccurs {
            throw TableError.witnessEscapes(body)
        }
    }

    private func value(_ c: NodeID) throws -> IRType {
        guard let T = type(of: c) else { throw TableError.expectedValue(c) }
        return T
    }

    private func sides(_ p: NodeID, at T: IRType) throws -> (NodeID, NodeID) {
        guard let (U, a, b) = sides(ofEquation: try premise(p)) else { throw TableError.principalConnective(p) }
        guard U == T else { throw TableError.childType(expected: T, found: U) }
        return (a, b)
    }

    private mutating func applied(_ f: NodeID, _ x: NodeID) throws -> NodeID {
        guard case .isaAbs(_, let body) = self[f] else { throw TableError.functionArgumentNotAbstraction(f) }
        return try instantiate(body, with: x, in: &self)
    }

    private func premise(_ c: NodeID) throws -> NodeID {
        guard let concluded = conclusion(of: c) else { throw TableError.expectedStep(c) }
        return concluded
    }

    private func expect(_ expected: IRType, _ c: NodeID) throws {
        let found = try value(c)
        guard found == expected else { throw TableError.childType(expected: expected, found: found) }
    }

    private func same(_ expected: NodeID, _ found: NodeID) throws {
        guard expected == found else { throw TableError.premiseMismatch(expected: expected, found: found) }
    }

    private func implication(_ step: NodeID, from antecedent: NodeID) throws -> NodeID {
        guard case .folImplies(let x, let y) = self[try premise(step)]
        else { throw TableError.principalConnective(step) }
        try same(antecedent, x)
        return y
    }

    private func absurd(_ step: NodeID) throws {
        guard case .folBottom = self[try premise(step)] else { throw TableError.principalConnective(step) }
    }

    private func apply(_ f: IRType, _ xs: [NodeID]) throws -> IRType {
        var result = f
        for x in xs {
            guard case .fn(let domain, let codomain) = result else {
                throw TableError.arityMismatch(expected: arity(f), found: xs.count)
            }
            try expect(domain, x)
            if case .fn = domain, !isAbstraction(x) { throw TableError.functionArgumentNotAbstraction(x) }
            result = codomain
        }
        if case .fn = result { throw TableError.arityMismatch(expected: arity(f), found: xs.count) }
        return result
    }

    private func isAbstraction(_ x: NodeID) -> Bool {
        if case .isaAbs = self[x] { return true }
        return false
    }

    private func arity(_ T: IRType) -> Int {
        if case .fn(_, let rest) = T { return 1 + arity(rest) }
        return 0
    }
}

public func fingerprint(_ x: NodeID, _ t: Table) -> String {
    let hex = String(t.fingerprint(of: x), radix: 16)
    return String(repeating: "0", count: 16 - hex.count) + hex
}
