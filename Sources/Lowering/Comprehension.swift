import IR

@frozen
public enum ComprehensionError: Error, Equatable, Sendable {
    case unread(NodeID)
    case misread(NodeID)
    case noEntry(Int)
}

struct Row: Hashable {
    let cls: Int
    let hyp: Int
}

/// ⚠ AN ENTRY'S FACT AT A RECORD IS CARRIED THERE ONCE, AT THE RECORD'S EXTENSION, AND ONLY IF A READ BELOW TAKES IT:
/// read back through the parents instead, an atom paid one step per binder in scope.
final class Record {
    init(_ variable: Int, tuple: Fact, entries: [Int] = [], facts: [Int: Fact] = [:]) {
        (self.variable, self.tuple, self.entries, self.facts, link) = (variable, tuple, entries, facts, nil)
    }

    init(_ parent: Record, value: Int, variable: Int, snoc: Fact, tuple: Fact, newest: Fact, facts: [Int: Fact]) {
        (self.variable, self.tuple, entries, self.facts, link) = (
            variable,
            tuple,
            parent.entries + [value],
            facts,
            (parent, snoc, newest),
        )
    }

    let variable: Int
    let tuple: Fact
    let entries: [Int]
    let facts: [Int: Fact]
    let link: (parent: Record, snoc: Fact, newest: Fact)?

    var length: Int {
        entries.count
    }

}

enum Role {
    case entry(Int)
    case fixed(Int)
    case binder(Int)
    case section(Int)
}

enum Connective: Hashable {
    case and
    case or
    case iff
    case not
    case implies
}

enum Witness {
    case fixed
    case property(Int)
    case opened(binder: Int, Constant, IRType, Row)
}

struct Lambda {
    let bundle: Built
    let outside: Int
}

struct Lift {
    let constant: Constant
    let type: IRType
    let cls: Row
    let lambdas: [Int]
}

struct Section {
    let cls: Int
    let function: Bool
    let record: Int
    let index: Int
    let next: Int
}

indirect enum Built {
    case connective(Connective, Row, [Built])
    case exists(Row, Built)
    case all(Row, Built)
    case bottom(Int)
    case atom(Row, [Int], Witness)
    case tuple(Row, [Int])
    case unfolded(BaseStatement, Built)
    case sectioned(Int, Built)
    case opened(binder: Int, Row, Built)
    case lambda(binder: Int, Lambda, Built)
    case lifted(binder: Int, Lift, Built)
    case liftedAtom(binder: Int, Int)

    var cls: Int {
        switch self {
        case .connective(_, let row, _), .exists(let row, _), .all(let row, _), .atom(let row, _, _),
             .tuple(let row, _):
            row.cls
        case .unfolded(_, let inner), .sectioned(_, let inner), .opened(_, _, let inner), .lambda(_, _, let inner),
             .lifted(_, _, let inner):
            inner.cls
        case .bottom(let empty), .liftedAtom(_, let empty): empty
        }
    }

    /// The record entries the reading below takes.
    var needs: Set<Int> {
        switch self {
        case .connective(_, _, let parts): parts.reduce(into: Set<Int>()) { $0.formUnion($1.needs) }
        case .exists(_, let inner), .all(_, let inner), .unfolded(_, let inner), .sectioned(_, let inner),
             .opened(_, _, let inner), .lifted(_, _, let inner):
            inner.needs
        case .lambda(_, let l, let inner): inner.needs.union(l.bundle.needs)
        case .atom(_, let es, _), .tuple(_, let es): Set(es)
        case .bottom, .liftedAtom: []
        }
    }
}

struct Bound {
    let variable: Int
    let constraint: Int
    let approximation: Int?
    let record: Record?
}

struct Env {
    var binders = [Int: Bound]()
    var sections = [Int: Int]()
}

struct Numerals {
    var levels: [Int]
    var successors: [Int]
    let first: Int
    let zero: Int?

    func successor(_ k: Int) throws -> Int {
        guard k >= first, k - first < successors.count else { throw ComprehensionError.noEntry(k) }
        return successors[k - first]
    }
}

enum Raw {
    case formula(NodeID)
    case body(ClassBody)
}

private enum StandIn {
    case opened(Constant, IRType, Row)
    case lambda(Int)
    case lifted(Lift)
}

private enum Key: Hashable {
    case read([Int], Int)
    case tupleRow([Int], Int)
    case connective(Connective, [Int])
    case exists(Int, Int)
    case all(Int, Int)
    case witness(BaseStatement)
    case applied(Int)
    case setConstant(Constant)
    case constantClass(Constant, IRType)
    case lifted(Constant, IRType, Int, [Int])
}

private let relations: [String: BaseStatement] = [
    "Pow": .powDef,
    "Union": .unionDef,
    "holds": .holdsDef,
    "truth": .truthOfSet,
]

struct Comprehension {
    init(base: Base, top: Frame, in t: inout Table) throws {
        var top = top
        let (n0, h0) = try top.open(try base.cite(.zeroEX, in: &t), in: &t)
        let n = try top.variable(n0, in: &t)
        let def = try eliminated(try base.cite(.zeroDef, in: &t), at: [n], in: &t)
        let isEmpty = try t.intern(.folIffElimL(def, try top.hypothesis(h0, in: &t)))
        let tuple = try eliminated(try base.cite(.tupleZero, in: &t), at: [n], premises: [isEmpty], in: &t)
        let empty = Record(n0, tuple: .hypothesis(try top.have(tuple, in: &t)))
        (self.base, self.top, numerals, self.empty) = (
            base,
            top,
            Numerals(levels: [n0], successors: [], first: 0, zero: h0),
            empty,
        )
    }

    init(base: Base, top: Frame, positions: [Int], length: Int) {
        (self.base, self.top, empty) = (base, top, nil)
        numerals = Numerals(levels: positions + [length], successors: [], first: positions.count, zero: nil)
    }

    let base: Base
    var top: Frame

    var reading: Reading {
        Reading(base: base, numerals: numerals, empty: empty)
    }

    mutating func numeral(_ j: Int, _ t: inout Table) throws -> Int {
        while numerals.levels.count <= j {
            let last = try top.variable(numerals.levels[numerals.levels.count - 1], in: &t)
            let (n, h) = try top.open(try eliminated(try base.cite(.nsuccEX, in: &t), at: [last], in: &t), in: &t)
            numerals.levels.append(n)
            numerals.successors.append(h)
        }
        return numerals.levels[j]
    }

    mutating func context(_ values: [Int], _ t: inout Table) throws -> Record {
        _ = try numeral(values.count, &t)
        let reading = reading
        return try reading.record(values, in: &top, &t)
    }

    mutating func classParameter(_ A: Int, function: Bool, record: Int, index: Int, next: Int) -> Int {
        let s = sections.count
        sections[s] = Section(cls: A, function: function, record: record, index: index, next: next)
        return s
    }

    mutating func section(
        raw: Raw,
        named: NodeID,
        outside: Int,
        roles: [Role],
        depth: Int,
        context c: Record,
        _ t: inout Table,
    ) throws -> NodeID {
        let k = c.length
        _ = try numeral(k + outside, &t)
        let built = try build(raw, roles + (0..<outside).map { Role.entry(k + $0) }, k + outside, &t)
        var g = Frame(top.scope)
        let values = (0..<outside).map { _ in g.fix(.i) }
        let records = (0..<outside).map { _ in g.fix(.i) }
        var snocs = [Int]()
        for j in 0..<outside {
            let prefix = j == 0 ? c.variable : records[j - 1]
            let snoc = try [prefix, numerals.levels[k + j], values[j], records[j]].map { try g.variable($0, in: &t) }
            snocs.append(g.assume(try t.intern(.folPred(.base("snoc"), args: snoc))))
        }
        let reading = reading
        var r = c
        for j in 0..<outside { r = try reading.extend(
            r,
            value: values[j],
            record: records[j],
            snoc: .hypothesis(snocs[j]),
            needs: built.needs,
            in: &g,
            &t,
        ) }
        let phi = try substituted(named, try ((0..<depth) + values).map { try g.variable($0, in: &t) }, in: &t)
        let premise = try g.close(try reading.read(phi, built, g, r, Env(), &t), in: &t)
        var s = top.scope
        let parameters = (0..<outside).map { _ in s.fix(.i) }
        var letter = try substituted(named, try ((0..<depth) + parameters).map { try s.variable($0, in: &t) }, in: &t)
        for _ in 0..<outside { letter = try t.intern(.folLetterAbs(body: letter)) }
        let schema = try base.instance(outside == 1 ? .memberClass : .graphClass, [letter], in: &t)
        let at = try ((0..<outside).map { numerals.levels[k + $0] } + [built.cls, c.variable]).map { try top.variable(
            $0,
            in: &t,
        ) }
        return try eliminated(schema, at: at, premises: [premise], in: &t)
    }

    mutating func build(_ raw: Raw, _ roles: [Role], _ k: Int, _ t: inout Table) throws -> Built {
        switch raw {
        case .formula(let phi): try build(phi, roles, k, &t)
        case .body(let b): try built(b, roles, k, &t)
        }
    }

    mutating func build(_ phi: NodeID, _ roles: [Role], _ k: Int, _ t: inout Table) throws -> Built {
        switch t[phi] {
        case .folAnd(let a, let b): return try binary(.and, a, b, roles, k, &t)

        case .folOr(let a, let b): return try binary(.or, a, b, roles, k, &t)

        case .folIff(let a, let b): return try binary(.iff, a, b, roles, k, &t)

        case .folImplies(let a, let b): return try binary(.implies, a, b, roles, k, &t)

        case .folNot(let a):
            let x = try build(a, roles, k, &t)
            return try connective(.not, [x], &t)

        case .folBottom:
            guard numerals.zero != nil else { throw ComprehensionError.unread(phi) }
            return .bottom(numerals.levels[0])

        case .ifolEx(.i, let body):
            let x = try build(body, roles + [.entry(k)], k + 1, &t)
            return try exists(x, k, &t)

        case .ifolAll(.i, let body):
            let x = try build(body, roles + [.entry(k)], k + 1, &t)
            return try all(x, k, &t)

        case .folPred(let p, let args):
            return try atom(phi, p, args, roles, k, &t)

        case .isaConst, .isaVarApp:
            var naming = Naming()
            let core = try naming.atom(t[phi], in: &t)
            let named = try naming.chain.formula(core, in: &t)
            return try chain(named, naming.pieces[...], [:], roles, k, &t)

        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .isaHidden, .folImpliesIntro, .folImpliesElim,
             .use, .hyp,
             .isaGuard, .isaExIntro, .isaExElim, .folBound, .folForall, .folExists, .folAndIntro, .folAndElimL,
             .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
             .folIffElimL,
             .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folCut, .folBottomElim,
             .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs, .isaValue, .isaValueFact:
            throw ComprehensionError.unread(phi)
        }
    }

    private let empty: Record?
    private var numerals: Numerals
    private var memo = [Key: Row]()
    private var standIns = [Int: StandIn]()
    private var sections = [Int: Section]()

    private mutating func built(_ b: ClassBody, _ roles: [Role], _ k: Int, _ t: inout Table) throws -> Built {
        let inner = roles + (0..<b.arity).map { Role.entry(k + $0) }
        let xs = try (0..<b.arity).map { try t.intern(.isaBound(b.arity - 1 - $0, .i)) }
        let argument = try tupled(
            xs + [try t.intern(.isaBound(b.arity + b.outside - 1, .i))],
            inner,
            k + b.arity,
            &t,
        )
        var built = try connective(.and, [argument, try build(b.member, inner, k + b.arity, &t)], &t)
        for j in (0..<b.arity).reversed() { built = try exists(built, k + j, &t) }
        return built
    }

    private mutating func tupled(_ args: [NodeID], _ roles: [Role], _ k: Int, _ t: inout Table) throws -> Built {
        let es = try entries(args, roles, t)
        let positions = try es.map { try numeral($0, &t) }
        let length = try numeral(k, &t)
        let row = try open(.tupleRow(positions, length), &t) { top, t in
            let f = TupleFact(arity: es.count - 1, fact: .row)
            return try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: try (positions + [length]).map { try top.variable($0, in: &t) },
                in: &t,
            )
        }
        return .tuple(row, es)
    }

    private func role(_ x: NodeID, _ roles: [Role], _ t: Table) throws -> Role {
        let d: Int
        switch t[x] {
        case .isaBound(let j, _): d = j
        case .folBound(let j): d = j
        default: throw ComprehensionError.unread(x)
        }
        guard d < roles.count else { throw ComprehensionError.unread(x) }
        return roles[roles.count - 1 - d]
    }

    private func entries(_ args: [NodeID], _ roles: [Role], _ t: Table) throws -> [Int] {
        try args.map { x in
            guard case .entry(let j) = try role(x, roles, t) else { throw ComprehensionError.unread(x) }
            return j
        }
    }

    private mutating func binary(
        _ c: Connective,
        _ a: NodeID,
        _ b: NodeID,
        _ roles: [Role],
        _ k: Int,
        _ t: inout Table,
    ) throws -> Built {
        let x = try build(a, roles, k, &t)
        let y = try build(b, roles, k, &t)
        return try connective(c, [x, y], &t)
    }

    /// A universal naming, binder by binder: a set piece `∀v. c → rest` by `row_all` and `B_imp`, a class piece
    /// `∀C. c → rest` as `rest` at its stand-in.
    private mutating func chain(
        _ phi: NodeID,
        _ pieces: ArraySlice<NamedPiece>,
        _ ids: [Int: Int],
        _ roles: [Role],
        _ k: Int,
        _ t: inout Table,
    ) throws -> Built {
        guard let piece = pieces.first else { return try build(phi, roles, k, &t) }
        let position = pieces.startIndex
        let rest = pieces.dropFirst()
        switch piece {
        case .setConstant(let c):
            guard
                case .ifolAll(.i, let body) = t[phi],
                case .folImplies(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let S = try setConstantClass(c, &t)
            let constraint = Built.atom(try readRow([k], S.cls, &t), [k], .property(S.hyp))
            let remaining = try chain(after, rest, ids, roles + [.entry(k)], k + 1, &t)
            return try all(try connective(.implies, [constraint, remaining], &t), k, &t)

        case .truthSet(let proposition):
            guard
                case .ifolAll(.i, let body) = t[phi],
                case .folImplies(let c, let after) = t[body],
                case .folAnd(let truthAtom, let held) = t[c],
                case .folIff(let holdsAtom, _) = t[held]
            else { throw ComprehensionError.unread(phi) }
            let inner = roles + [.entry(k)]
            let read = try build(try shift(proposition, by: position + 1, in: &t), inner, k + 1, &t)
            let holding = try connective(.iff, [try build(holdsAtom, inner, k + 1, &t), read], &t)
            let constraint = try connective(.and, [try build(truthAtom, inner, k + 1, &t), holding], &t)
            let remaining = try chain(after, rest, ids, inner, k + 1, &t)
            return try all(try connective(.implies, [constraint, remaining], &t), k, &t)

        case .tuple(let refs):
            guard
                case .ifolAll(.i, let body) = t[phi],
                case .folImplies(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let inner = roles + [.entry(k)]
            let args = try refs.map { ref -> NodeID in
                switch ref {
                case .outer(let x): try shift(x, by: position + 1, in: &t)
                case .bound(let j): try t.intern(.isaBound(position - j, .i))
                }
            }
            let constraint = try tupled(args + [try t.intern(.isaBound(0, .i))], inner, k + 1, &t)
            let remaining = try chain(after, rest, ids, inner, k + 1, &t)
            return try all(try connective(.implies, [constraint, remaining], &t), k, &t)

        case .value, .applied:
            guard
                case .ifolAll(.i, let body) = t[phi],
                case .folImplies(let c, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let constraint = try build(c, roles + [.entry(k)], k + 1, &t)
            let remaining = try chain(after, rest, ids, roles + [.entry(k)], k + 1, &t)
            return try all(try connective(.implies, [constraint, remaining], &t), k, &t)

        case .constantClass(let c, let T, let classes):
            guard
                case .folForall(let body) = t[phi],
                case .folImplies(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let m = standIns.count
            if classes.isEmpty {
                let C = try constantClass(c, T, &t)
                standIns[m] = .opened(c, T, C)
                return .opened(binder: m, C, try chain(after, rest, ids, roles + [.binder(m)], k, &t))
            }
            let lambdas = try classes.map { ref -> Int in
                guard case .bound(let j) = ref, let id = ids[j] else { throw ComprehensionError.unread(phi) }
                return id
            }
            let bundles = try lambdas.map { id -> Int in
                guard case .lambda(let A)? = standIns[id] else { throw ComprehensionError.unread(phi) }
                return A
            }
            let lift = Lift(constant: c, type: T, cls: try lifted(c, T, bundles, k, &t), lambdas: lambdas)
            standIns[m] = .lifted(lift)
            return .lifted(binder: m, lift, try chain(after, rest, ids, roles + [.binder(m)], k, &t))

        case .lambdaClass(let lambda):
            guard
                case .folForall(let body) = t[phi],
                case .folImplies(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let raw = try classBody(try shift(lambda, by: position, in: &t), raw: true, in: &t)
            _ = try numeral(k + raw.outside, &t)
            let bundle = try built(raw, roles + (0..<raw.outside).map { Role.entry(k + $0) }, k + raw.outside, &t)
            let m = standIns.count
            standIns[m] = .lambda(bundle.cls)
            var bound = ids
            bound[position] = m
            return .lambda(
                binder: m,
                Lambda(bundle: bundle, outside: raw.outside),
                try chain(after, rest, bound, roles + [.binder(m)], k, &t),
            )
        }
    }

    private mutating func atom(
        _ phi: NodeID,
        _ p: Predicate,
        _ args: [NodeID],
        _ roles: [Role],
        _ k: Int,
        _ t: inout Table,
    ) throws -> Built {
        guard case .base(let name) = p else { throw ComprehensionError.unread(phi) }
        if let def = relations[name] { return try unfolded(def, args, roles, k, &t) }
        let rs = try args.map { try role($0, roles, t) }
        switch (name, rs.count) {
        case ("eq", 2): return try witnessed(try witness(.clsDiag, &t), try entries(args, roles, t), &t)

        case ("zero", 1): return try witnessed(try witness(.clsZero, &t), try entries(args, roles, t), &t)

        case ("nsucc", 2): return try witnessed(try witness(.clsNsucc, &t), try entries(args, roles, t), &t)

        case ("snoc", 4): return try witnessed(try snocs(&t), try entries(args, roles, t), &t)

        case ("elem", 2), ("pmem", 3), ("apply", 3):
            let es = try entries(Array(args.dropLast()), roles, t)
            switch rs[rs.count - 1] {
            case .entry(let j):
                guard name == "elem" else { throw ComprehensionError.unread(phi) }
                return try witnessed(try membership(&t), es + [j], &t)

            case .fixed(let level):
                if name == "apply" { return try witnessed(try applied(level, &t), es, &t) }
                return .atom(try readRow(es, level, &t), es, .fixed)

            case .binder(let m):
                switch (name, standIns[m]) {
                case ("elem", .opened(let c, let T, let C)?), ("pmem", .opened(let c, let T, let C)?):
                    return .atom(try readRow(es, C.cls, &t), es, .opened(binder: m, c, T, C))
                case ("elem", .lifted(let lift)?), ("pmem", .lifted(let lift)?):
                    return .liftedAtom(binder: m, lift.cls.cls)
                default:
                    throw ComprehensionError.unread(phi)
                }

            case .section(let s):
                guard let section = sections[s] else { throw ComprehensionError.unread(phi) }
                if name == "apply" { return try unfolded(.applyDef, args, roles, k, &t) }
                guard (name == "pmem") == section.function else { throw ComprehensionError.unread(phi) }
                return .sectioned(s, try sectioned(section, es, k, &t))
            }

        default:
            throw ComprehensionError.unread(phi)
        }
    }

    private mutating func unfolded(
        _ def: BaseStatement,
        _ args: [NodeID],
        _ roles: [Role],
        _ k: Int,
        _ t: inout Table,
    ) throws -> Built {
        let instance = try eliminated(try base.cite(def, in: &t), at: args, in: &t)
        return .unfolded(def, try build(try sides(instance, t).right, roles, k, &t))
    }

    private mutating func sectioned(_ s: Section, _ es: [Int], _ k: Int, _ t: inout Table) throws -> Built {
        let member = Built.atom(try readRow([k + es.count - 1], s.cls, &t), [k + es.count - 1], .fixed)
        var inner = member
        if s.function {
            let snoc = try witnessed(try snocs(&t), [k, s.next, es[1], k + 1], &t)
            inner = try exists(try connective(.and, [snoc, member], &t), k + 1, &t)
        }
        let snoc = try witnessed(try snocs(&t), [s.record, s.index, es[0], k], &t)
        return try exists(try connective(.and, [snoc, inner], &t), k, &t)
    }

    private mutating func witnessed(_ w: Row, _ es: [Int], _ t: inout Table) throws -> Built {
        .atom(try readRow(es, w.cls, &t), es, .property(w.hyp))
    }

    private mutating func open(
        _ key: Key,
        _ t: inout Table,
        _ statement: (Frame, inout Table) throws -> NodeID,
    ) throws -> Row {
        if let row = memo[key] { return row }
        let (c, h) = try top.open(try statement(top, &t), in: &t)
        memo[key] = Row(cls: c, hyp: h)
        return Row(cls: c, hyp: h)
    }

    private mutating func connective(_ c: Connective, _ children: [Built], _ t: inout Table) throws -> Built {
        let classes = children.map(\.cls)
        let s: BaseStatement =
            switch c {
            case .and: .b2
            case .or: .bOr
            case .iff: .bIff
            case .not: .b3
            case .implies: .bImp
            }
        let base = base
        let row = try open(.connective(c, classes), &t) { top, t in
            try eliminated(try base.cite(s, in: &t), at: try classes.map { try top.variable($0, in: &t) }, in: &t)
        }
        return .connective(c, row, children)
    }

    private mutating func exists(_ child: Built, _ k: Int, _ t: inout Table) throws -> Built {
        .exists(try quantifierRow(.rowEx, child, k, &t), child)
    }

    private mutating func all(_ child: Built, _ k: Int, _ t: inout Table) throws -> Built {
        .all(try quantifierRow(.rowAll, child, k, &t), child)
    }

    private mutating func quantifierRow(_ s: BaseStatement, _ child: Built, _ k: Int, _ t: inout Table) throws -> Row {
        let n = try numeral(k, &t)
        let A = child.cls
        _ = try numeral(k + 1, &t)
        let base = base
        return try open(s == .rowEx ? .exists(n, A) : .all(n, A), &t) { top, t in
            try eliminated(
                try base.cite(s, in: &t),
                at: [try top.variable(n, in: &t), try top.variable(A, in: &t)],
                in: &t,
            )
        }
    }

    private mutating func readRow(_ es: [Int], _ cls: Int, _ t: inout Table) throws -> Row {
        let s: BaseStatement
        switch es.count {
        case 1: s = .read1
        case 2: s = .read2
        case 4: s = .read4
        default: throw ComprehensionError.noEntry(es.count)
        }
        let ns = try es.map { try numeral($0, &t) }
        let base = base
        return try open(.read(ns, cls), &t) { top, t in
            try eliminated(try base.cite(s, in: &t), at: try (ns + [cls]).map { try top.variable($0, in: &t) }, in: &t)
        }
    }

    private mutating func witness(_ s: BaseStatement, _ t: inout Table) throws -> Row {
        let base = base
        return try open(.witness(s), &t) { _, t in try base.cite(s, in: &t) }
    }

    private mutating func membership(_ t: inout Table) throws -> Row {
        if let row = memo[.witness(.b1)] { return row }
        let (E, h) = try top.open(try base.cite(.b1, in: &t), in: &t)
        var g = Frame(top.scope)
        let ul = g.fix(.i)
        let vl = g.fix(.i)
        let u = try g.variable(ul, in: &t)
        let v = try g.variable(vl, in: &t)
        let exact = try eliminated(
            try g.hypothesis(h, in: &t),
            at: [u, v],
            premises: [try isaGuard(u, .i, &t), try isaGuard(v, .i, &t)],
            in: &t,
        )
        let row = Row(cls: E, hyp: try top.have(try g.close(exact, in: &t), in: &t))
        memo[.witness(.b1)] = row
        return row
    }

    private mutating func snocs(_ t: inout Table) throws -> Row {
        if let row = memo[.witness(.clsSnoc4)] { return row }
        let (S, h) = try top.open(try base.cite(.clsSnoc4, in: &t), in: &t)
        let keyed = try eliminated(
            try base.cite(.rsKey, in: &t),
            at: [try top.variable(S, in: &t)],
            premises: [try top.hypothesis(h, in: &t)],
            in: &t,
        )
        let row = Row(cls: S, hyp: try top.have(keyed, in: &t))
        memo[.witness(.clsSnoc4)] = row
        return row
    }

    private mutating func applied(_ f: Int, _ t: inout Table) throws -> Row {
        let base = base
        return try open(.applied(f), &t) { top, t in
            try eliminated(try base.cite(.clsApply, in: &t), at: [try top.variable(f, in: &t)], in: &t)
        }
    }

    private mutating func setConstantClass(_ c: Constant, _ t: inout Table) throws -> Row {
        try open(.setConstant(c), &t) { _, t in
            let f = ConstantFact(constant: c, type: .i, fact: .classExists)
            return try cited(f, try statement(f, in: &t), &t)
        }
    }

    private mutating func constantClass(_ c: Constant, _ T: IRType, _ t: inout Table) throws -> Row {
        try open(.constantClass(c, T), &t) { _, t in
            let f = ConstantFact(constant: c, type: T, fact: .classExists)
            return try cited(f, try statement(f, in: &t), &t)
        }
    }

    private mutating func lifted(
        _ c: Constant,
        _ T: IRType,
        _ bundles: [Int],
        _ k: Int,
        _ t: inout Table,
    ) throws -> Row {
        let n = try numeral(k, &t)
        let n1 = try numeral(k + 1, &t)
        _ = try numeral(k + 2, &t)
        let successor = try numerals.successor(k)
        return try open(.lifted(c, T, k, bundles), &t) { top, t in
            let f = ConstantFact(constant: c, type: T, fact: .lift)
            let at = try eliminated(
                try cited(f, try statement(f, in: &t), &t),
                at: [try top.variable(n, in: &t), try top.variable(n1, in: &t)],
                premises: [try top.hypothesis(successor, in: &t)],
                in: &t,
            )
            return try eliminated(at, at: try bundles.map { try top.variable($0, in: &t) }, in: &t)
        }
    }
}

/// A formula's exactness at a record, `elem(r, A) ↔ φ`, as two walks, each built from the one below it: `down` from
/// the membership to φ, `up` back. Each level uses its row at the record as it stands and states no subformula; only
/// an assumption the kernel needs writes its formula — the antecedent an implication or a negation discharges.
struct Reading {
    let base: Base
    let numerals: Numerals
    let empty: Record?

    func extend(
        _ r: Record,
        value v: Int,
        record b: Int,
        snoc s: Fact,
        needs: Set<Int>,
        in f: inout Frame,
        _ t: inout Table,
    ) throws -> Record {
        let k = r.length
        let at = try [r.variable, numerals.levels[k], numerals.levels[k + 1], v, b].map { try f.variable($0, in: &t) }
        let facts = try eliminated(
            try base.cite(.snocFacts, in: &t),
            at: at,
            premises: [
                try f.proof(r.tuple, in: &t),
                try f.hypothesis(try numerals.successor(k), in: &t),
                try f.proof(s, in: &t),
            ],
            in: &t,
        )
        let h = Fact.hypothesis(try f.have(facts, in: &t))
        var carried = [Int: Fact]()
        for j in needs.filter({ $0 < k }).sorted() {
            let moved = try eliminated(
                try f.proof(.right(.right(h)), in: &t),
                at: [try f.variable(numerals.levels[j], in: &t), try f.variable(r.entries[j], in: &t)],
                premises: [try entry(j, of: r, in: f.scope, &t)],
                in: &t,
            )
            carried[j] = .hypothesis(try f.have(moved, in: &t))
        }
        return Record(r, value: v, variable: b, snoc: s, tuple: .left(h), newest: .left(.right(h)), facts: carried)
    }

    /// ⚠ OPENS ITS PREFIXES, FIXING ONE VARIABLE PER ENTRY: a formula taken in `f` before it is that many levels
    /// shallow.
    func record(_ values: [Int], in f: inout Frame, _ t: inout Table) throws -> Record {
        guard var r = empty else { throw ComprehensionError.noEntry(0) }
        let every = Set(values.indices)
        for v in values {
            let at = try [r.variable, numerals.levels[r.length], v].map { try f.variable($0, in: &t) }
            let (b, s) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
            r = try extend(r, value: v, record: b, snoc: .hypothesis(s), needs: every, in: &f, &t)
        }
        return r
    }

    /// `tuple(entries, r)` at the record's chain: the empty record, the numerals its indices, its prefixes the records.
    func tupled(_ r: Record, in s: Scope, _ t: inout Table) throws -> NodeID {
        var records = [r]
        while let link = records[0].link { records.insert(link.parent, at: 0) }
        guard let last = r.link, let zero = numerals.zero else { throw ComprehensionError.noEntry(0) }
        let n = r.length
        let chain = try TupleChain(
            zero: (numerals.levels[0], .hypothesis(zero)),
            indices: (1..<n).map { (numerals.levels[$0], .hypothesis(try numerals.successor($0 - 1))) },
            prefixes: (1..<n).map { j in
                guard let link = records[j].link else { throw ComprehensionError.noEntry(j) }
                return (records[j].variable, link.snoc)
            },
            last: last.snoc,
        )
        return try universalTuple(r.entries, r.variable, chain, base: base, in: s, &t)
    }

    func entry(_ j: Int, of r: Record, in s: Scope, _ t: inout Table) throws -> NodeID {
        if let link = r.link, j == r.length - 1 { return try s.proof(link.newest, in: &t) }
        guard let fact = r.facts[j] else { throw ComprehensionError.noEntry(j) }
        return try s.proof(fact, in: &t)
    }

    /// `elem(r, A) ↔ φ`: the two walks, each discharged once.
    func read(_ phi: NodeID, _ b: Built, _ f: Frame, _ r: Record, _ env: Env, _ t: inout Table) throws -> NodeID {
        let member = try pred("elem", [r.variable, b.cls], at: f.scope, &t)
        var there = Frame(f.scope)
        let h = there.assume(member)
        let forward = try there.close(try down(phi, b, there, r, env, try there.hypothesis(h, in: &t), &t), in: &t)
        var back = Frame(f.scope)
        let h2 = back.assume(phi)
        let backward = try back.close(try up(phi, b, back, r, env, try back.hypothesis(h2, in: &t), &t), in: &t)
        return try t.intern(.folIffIntro(forward, backward))
    }

    /// From `p`, `elem(r, A)` at `f`, the formula `φ` the class reads.
    func down(_ phi: NodeID, _ b: Built, _ f: Frame, _ r: Record, _ env: Env, _ p: NodeID, _ t: inout Table) throws
        -> NodeID
    {
        switch b {
        case .connective(let c, let row, let children):
            let parts = try operands(c, phi, t)
            let q = try t.intern(.folIffElimL(try at(row, f, r, &t), p))
            switch c {
            case .and:
                return try t.intern(.folAndIntro(
                    try down(parts[0], children[0], f, r, env, try t.intern(.folAndElimL(q)), &t),
                    try down(parts[1], children[1], f, r, env, try t.intern(.folAndElimR(q)), &t),
                ))

            case .or:
                let branch = { (j: Int, t: inout Table) throws -> NodeID in
                    var g = Frame(f.scope)
                    let h = g.assume(try pred("elem", [r.variable, children[j].cls], at: g.scope, &t))
                    let x = try down(parts[j], children[j], g, r, env, try g.hypothesis(h, in: &t), &t)
                    return try g.close(
                        try t.intern(j == 0 ? .folOrIntroL(x, parts[1]) : .folOrIntroR(parts[0], x)),
                        in: &t,
                    )
                }
                return try t.intern(.folOrElim(q, try branch(0, &t), try branch(1, &t)))

            case .iff:
                let one = { (from: Int, to: Int, t: inout Table) throws -> NodeID in
                    var g = Frame(f.scope)
                    let h = g.assume(parts[from])
                    let x = try up(parts[from], children[from], g, r, env, try g.hypothesis(h, in: &t), &t)
                    let lq = try lifted(q, from: f.scope, to: g.scope, in: &t)
                    let y = try t.intern(from == 0 ? .folIffElimL(lq, x) : .folIffElimR(lq, x))
                    return try g.close(try down(parts[to], children[to], g, r, env, y, &t), in: &t)
                }
                return try t.intern(.folIffIntro(try one(0, 1, &t), try one(1, 0, &t)))

            case .not:
                var g = Frame(f.scope)
                let h = g.assume(parts[0])
                let x = try up(parts[0], children[0], g, r, env, try g.hypothesis(h, in: &t), &t)
                let absurd = try t.intern(.folNotElim(try lifted(q, from: f.scope, to: g.scope, in: &t), x))
                return try t.intern(.folNotIntro(parts[0], body: absurd))

            case .implies:
                var g = Frame(f.scope)
                let h = g.assume(parts[0])
                let x = try up(parts[0], children[0], g, r, env, try g.hypothesis(h, in: &t), &t)
                let y = try t.intern(.folImpliesElim(try lifted(q, from: f.scope, to: g.scope, in: &t), x))
                return try g.close(try down(parts[1], children[1], g, r, env, y, &t), in: &t)
            }

        case .exists(let row, let child):
            guard case .ifolEx(.i, _) = t[phi] else { throw ComprehensionError.misread(phi) }
            var g = Frame(f.scope)
            let (v, hv) = try g.open(try t.intern(.folIffElimL(try at(row, f, r, &t), p)), in: &t)
            let (w, hw) = try g.open(try g.hypothesis(hv, in: &t), in: &t)
            let longer = try extend(
                r,
                value: v,
                record: w,
                snoc: .left(.hypothesis(hw)),
                needs: child.needs,
                in: &g,
                &t,
            )
            let some = try g.scope.lift(phi, from: f.scope.depth, in: &t)
            guard case .ifolEx(.i, let body) = t[some] else { throw ComprehensionError.misread(phi) }
            let x = try g.variable(v, in: &t)
            let inner = try down(
                try instantiate(body, with: x, in: &t),
                child,
                g,
                longer,
                env,
                try g.proof(.right(.hypothesis(hw)), in: &t),
                &t,
            )
            return try g.close(try t.intern(.isaExIntro(inner, x, body: body)), in: &t)

        case .all(let row, let child):
            guard case .ifolAll(.i, _) = t[phi] else { throw ComprehensionError.misread(phi) }
            let q = try t.intern(.folIffElimL(try at(row, f, r, &t), p))
            var g = Frame(f.scope)
            let v = g.fix(.i)
            let (w, hw) = try g.open(try snocExists(r, v, g, &t), in: &t)
            let longer = try extend(r, value: v, record: w, snoc: .hypothesis(hw), needs: child.needs, in: &g, &t)
            let lq = try lifted(q, from: f.scope, to: g.scope, in: &t)
            let member = try t.intern(.folImpliesElim(
                try t.intern(.isaAllElim(try t.intern(.isaAllElim(lq, try g.variable(v, in: &t))), try g.variable(
                    w,
                    in: &t,
                ))),
                try g.hypothesis(hw, in: &t),
            ))
            let every = try g.scope.lift(phi, from: f.scope.depth, in: &t)
            guard case .ifolAll(.i, let body) = t[every] else { throw ComprehensionError.misread(phi) }
            let at = try instantiate(body, with: try g.variable(v, in: &t), in: &t)
            return try g.close(try down(at, child, g, longer, env, member, &t), in: &t)

        case .bottom:
            return try t.intern(.folIffElimL(try bottom(f, r, &t), p))

        case .atom(let row, let es, let witness):
            let (read, property) = try atomParts(row, es, witness, f, r, env, &t)
            let w = try t.intern(.folIffElimL(read, p))
            guard let property else { return w }
            return try t.intern(.folIffElimL(property, w))

        case .tuple(let row, let es):
            return try t.intern(.folIffElimL(try tupleRead(row, es, f, r, &t), p))

        case .unfolded(let def, let inner):
            guard case .folPred(_, let args) = t[phi] else { throw ComprehensionError.misread(phi) }
            let definition = try eliminated(try base.cite(def, in: &t), at: args, in: &t)
            let d = try sides(definition, t).right
            return try t.intern(.folIffElimR(definition, try down(d, inner, f, r, env, p, &t)))

        case .sectioned(let s, let inner):
            let section = try sectionAt(s, phi, f, env, &t)
            let d = try sides(section, t).right
            return try t.intern(.folIffElimR(section, try down(d, inner, f, r, env, p, &t)))

        case .opened(let m, _, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(let c, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            var g = Frame(f.scope)
            let cv = g.fix(nil)
            let hc = g.assume(c)
            var bound = env
            bound.binders[m] = Bound(variable: cv, constraint: hc, approximation: nil, record: nil)
            let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
            return try g.close(try down(rest, inner, g, r, bound, lp, &t), in: &t)

        case .lambda(let m, let lambda, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(let definition, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            let exact = try lambdaExactness(definition, lambda, f, r, env, &t)
            var g = Frame(f.scope)
            let K = g.fix(nil)
            let hc = g.assume(definition)
            let approximation = try joined(
                try g.hypothesis(hc, in: &t),
                try lifted(exact, from: f.scope, to: g.scope, in: &t),
                lambda.outside,
                g,
                symmetric: true,
                &t,
            )
            var bound = env
            bound.binders[m] = Bound(
                variable: K,
                constraint: hc,
                approximation: try g.have(approximation, in: &t),
                record: nil,
            )
            let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
            return try g.close(try down(rest, inner, g, r, bound, lp, &t), in: &t)

        case .lifted(let m, let lift, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(let c, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            var g = Frame(f.scope)
            let C = g.fix(nil)
            let hc = g.assume(c)
            var bound = env
            bound.binders[m] = try liftedBound(phi, lift, C, hc, &g, r, env, &t)
            let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
            return try g.close(try down(rest, inner, g, r, bound, lp, &t), in: &t)

        case .liftedAtom(let m, let U):
            return try t.intern(.folIffElimL(try liftedAtom(phi, m, U, f, r, env, &t), p))
        }
    }

    /// From `p`, the formula `φ` at `f`, the membership `elem(r, A)`.
    func up(_ phi: NodeID, _ b: Built, _ f: Frame, _ r: Record, _ env: Env, _ p: NodeID, _ t: inout Table) throws
        -> NodeID
    {
        switch b {
        case .connective(let c, let row, let children):
            let parts = try operands(c, phi, t)
            let member = { (j: Int, s: Scope, t: inout Table) throws -> NodeID in
                try pred("elem", [r.variable, children[j].cls], at: s, &t)
            }
            let q: NodeID
            switch c {
            case .and:
                q = try t.intern(.folAndIntro(
                    try up(parts[0], children[0], f, r, env, try t.intern(.folAndElimL(p)), &t),
                    try up(parts[1], children[1], f, r, env, try t.intern(.folAndElimR(p)), &t),
                ))

            case .or:
                let branch = { (j: Int, t: inout Table) throws -> NodeID in
                    var g = Frame(f.scope)
                    let h = g.assume(parts[j])
                    let x = try up(parts[j], children[j], g, r, env, try g.hypothesis(h, in: &t), &t)
                    let other = try member(1 - j, g.scope, &t)
                    return try g.close(
                        try t.intern(j == 0 ? .folOrIntroL(x, other) : .folOrIntroR(other, x)),
                        in: &t,
                    )
                }
                q = try t.intern(.folOrElim(p, try branch(0, &t), try branch(1, &t)))

            case .iff:
                let one = { (from: Int, to: Int, t: inout Table) throws -> NodeID in
                    var g = Frame(f.scope)
                    let h = g.assume(try member(from, g.scope, &t))
                    let x = try down(parts[from], children[from], g, r, env, try g.hypothesis(h, in: &t), &t)
                    let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
                    let y = try t.intern(from == 0 ? .folIffElimL(lp, x) : .folIffElimR(lp, x))
                    return try g.close(try up(parts[to], children[to], g, r, env, y, &t), in: &t)
                }
                q = try t.intern(.folIffIntro(try one(0, 1, &t), try one(1, 0, &t)))

            case .not:
                var g = Frame(f.scope)
                let held = try member(0, g.scope, &t)
                let h = g.assume(held)
                let x = try down(parts[0], children[0], g, r, env, try g.hypothesis(h, in: &t), &t)
                let absurd = try t.intern(.folNotElim(try lifted(p, from: f.scope, to: g.scope, in: &t), x))
                q = try t.intern(.folNotIntro(held, body: absurd))

            case .implies:
                var g = Frame(f.scope)
                let h = g.assume(try member(0, g.scope, &t))
                let x = try down(parts[0], children[0], g, r, env, try g.hypothesis(h, in: &t), &t)
                let y = try t.intern(.folImpliesElim(try lifted(p, from: f.scope, to: g.scope, in: &t), x))
                q = try g.close(try up(parts[1], children[1], g, r, env, y, &t), in: &t)
            }
            return try t.intern(.folIffElimR(try at(row, f, r, &t), q))

        case .exists(let row, let child):
            guard case .ifolEx(.i, _) = t[phi] else { throw ComprehensionError.misread(phi) }
            let rowAt = try at(row, f, r, &t)
            var g = Frame(f.scope)
            let (x, hx) = try g.open(p, in: &t)
            let (w, hw) = try g.open(try snocExists(r, x, g, &t), in: &t)
            let longer = try extend(r, value: x, record: w, snoc: .hypothesis(hw), needs: child.needs, in: &g, &t)
            let some = try g.scope.lift(phi, from: f.scope.depth, in: &t)
            guard case .ifolEx(.i, let body) = t[some] else { throw ComprehensionError.misread(phi) }
            let member = try up(
                try instantiate(body, with: try g.variable(x, in: &t), in: &t),
                child,
                g,
                longer,
                env,
                try g.hypothesis(hx, in: &t),
                &t,
            )
            let target = try g.scope.lift(try sides(rowAt, t).right, from: f.scope.depth, in: &t)
            guard case .ifolEx(.i, let outer) = t[target] else { throw ComprehensionError.misread(phi) }
            let atX = try instantiate(outer, with: try g.variable(x, in: &t), in: &t)
            guard case .ifolEx(.i, let inner) = t[atX] else { throw ComprehensionError.misread(phi) }
            let both = try t.intern(.folAndIntro(try g.hypothesis(hw, in: &t), member))
            let some2 = try t.intern(.isaExIntro(both, try g.variable(w, in: &t), body: inner))
            let some1 = try t.intern(.isaExIntro(some2, try g.variable(x, in: &t), body: outer))
            return try t.intern(.folIffElimR(rowAt, try g.close(some1, in: &t)))

        case .all(let row, let child):
            guard case .ifolAll(.i, _) = t[phi] else { throw ComprehensionError.misread(phi) }
            let rowAt = try at(row, f, r, &t)
            var g = Frame(f.scope)
            let v = g.fix(.i)
            let w = g.fix(.i)
            let snoc = try [r.variable, numerals.levels[r.length], v, w].map { try g.variable($0, in: &t) }
            let hs = g.assume(try t.intern(.folPred(.base("snoc"), args: snoc)))
            let longer = try extend(r, value: v, record: w, snoc: .hypothesis(hs), needs: child.needs, in: &g, &t)
            let every = try g.scope.lift(phi, from: f.scope.depth, in: &t)
            guard case .ifolAll(.i, let body) = t[every] else { throw ComprehensionError.misread(phi) }
            let x = try g.variable(v, in: &t)
            let atV = try t.intern(.isaAllElim(try lifted(p, from: f.scope, to: g.scope, in: &t), x))
            let member = try up(try instantiate(body, with: x, in: &t), child, g, longer, env, atV, &t)
            return try t.intern(.folIffElimR(rowAt, try g.close(member, in: &t)))

        case .bottom:
            return try t.intern(.folIffElimR(try bottom(f, r, &t), p))

        case .atom(let row, let es, let witness):
            let (read, property) = try atomParts(row, es, witness, f, r, env, &t)
            let w = try property.map { try t.intern(.folIffElimR($0, p)) } ?? p
            return try t.intern(.folIffElimR(read, w))

        case .tuple(let row, let es):
            return try t.intern(.folIffElimR(try tupleRead(row, es, f, r, &t), p))

        case .unfolded(let def, let inner):
            guard case .folPred(_, let args) = t[phi] else { throw ComprehensionError.misread(phi) }
            let definition = try eliminated(try base.cite(def, in: &t), at: args, in: &t)
            let d = try sides(definition, t).right
            return try up(d, inner, f, r, env, try t.intern(.folIffElimL(definition, p)), &t)

        case .sectioned(let s, let inner):
            let section = try sectionAt(s, phi, f, env, &t)
            let d = try sides(section, t).right
            return try up(d, inner, f, r, env, try t.intern(.folIffElimL(section, p)), &t)

        case .opened(let m, let C, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(_, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            let c0 = try f.variable(C.cls, in: &t)
            let at = try t.intern(.folImpliesElim(
                try t.intern(.folForallElim(p, c0)),
                try f.hypothesis(C.hyp, in: &t),
            ))
            var bound = env
            bound.binders[m] = Bound(variable: C.cls, constraint: C.hyp, approximation: nil, record: nil)
            return try up(try instantiate(rest, with: c0, in: &t), inner, f, r, bound, at, &t)

        case .lambda(let m, let lambda, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(let definition, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            let exact = try lambdaExactness(definition, lambda, f, r, env, &t)
            var g = Frame(f.scope)
            let n = numerals.levels[r.length]
            let n1 = numerals.levels[r.length + 1]
            let witnessAt = try (lambda.outside == 1 ? [n] : [n, n1]).map { try g.variable($0, in: &t) }
                + [try g.variable(lambda.bundle.cls, in: &t), try g.variable(r.variable, in: &t)]
            let (K0, hK0) = try g.open(
                try eliminated(
                    try base.cite(lambda.outside == 1 ? .lamPred : .lamClass, in: &t),
                    at: witnessAt,
                    in: &t,
                ),
                in: &t,
            )
            let k0 = try g.variable(K0, in: &t)
            let defined = try joined(
                try g.hypothesis(hK0, in: &t),
                try lifted(exact, from: f.scope, to: g.scope, in: &t),
                lambda.outside,
                g,
                symmetric: false,
                &t,
            )
            let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
            let at = try t.intern(.folImpliesElim(try t.intern(.folForallElim(lp, k0)), defined))
            var bound = env
            bound.binders[m] = Bound(variable: K0, constraint: hK0, approximation: hK0, record: nil)
            let liftedRest = try g.scope.lift(try t.intern(.folForall(body: rest)), from: f.scope.depth, in: &t)
            guard case .folForall(let restBody) = t[liftedRest] else { throw ComprehensionError.misread(phi) }
            _ = definition
            let member = try up(try instantiate(restBody, with: k0, in: &t), inner, g, r, bound, at, &t)
            return try g.close(member, in: &t)

        case .lifted(let m, let lift, let inner):
            guard case .folForall(let all) = t[phi], case .folImplies(_, let rest) = t[all] else {
                throw ComprehensionError.misread(phi)
            }
            let lambdas = try lift.lambdas.map { id -> Int in
                guard let b = env.binders[id] else { throw ComprehensionError.misread(phi) }
                return b.variable
            }
            var g = Frame(f.scope)
            let fact = ConstantFact(constant: lift.constant, type: lift.type, fact: .classExists)
            let (C0, hC0) = try g.open(
                try eliminated(
                    try cited(fact, try statement(fact, in: &t), &t),
                    at: try lambdas.map { try g.variable($0, in: &t) },
                    in: &t,
                ),
                in: &t,
            )
            let c0 = try g.variable(C0, in: &t)
            var bound = env
            bound.binders[m] = try liftedBound(phi, lift, C0, hC0, &g, r, env, &t)
            let lp = try lifted(p, from: f.scope, to: g.scope, in: &t)
            let at = try t.intern(.folImpliesElim(try t.intern(.folForallElim(lp, c0)), try g.hypothesis(hC0, in: &t)))
            let liftedRest = try g.scope.lift(try t.intern(.folForall(body: rest)), from: f.scope.depth, in: &t)
            guard case .folForall(let restBody) = t[liftedRest] else { throw ComprehensionError.misread(phi) }
            let member = try up(try instantiate(restBody, with: c0, in: &t), inner, g, r, bound, at, &t)
            return try g.close(member, in: &t)

        case .liftedAtom(let m, let U):
            return try t.intern(.folIffElimR(try liftedAtom(phi, m, U, f, r, env, &t), p))
        }
    }

    /// `∀v⃗. (∃b⃗. snoc ∧ … ∧ elem(b, A)) ↔ ψ(v⃗)`: a λ's body exact at each extension of `r`, each direction a walk.
    func extensions(
        _ psi: NodeID,
        _ child: Built,
        _ outside: Int,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        var each = Frame(f.scope)
        let values = (0..<outside).map { _ in each.fix(.i) }
        func chained(_ j: Int, _ prefix: Int, _ s: Scope, _ t: inout Table) throws -> NodeID {
            var inner = s
            let b = inner.fix(.i)
            let snoc = try pred("snoc", [prefix, numerals.levels[r.length + j], values[j], b], at: inner, &t)
            let rest = j == outside - 1
                ? try pred("elem", [b, child.cls], at: inner, &t)
                : try chained(j + 1, b, inner, &t)
            return try t.intern(.ifolEx(.i, body: try t.intern(.folAnd(snoc, rest))))
        }
        let left = try chained(0, r.variable, each.scope, &t)
        var forward = Frame(each.scope)
        let h = forward.assume(left)
        var current = Fact.hypothesis(h)
        var longer = r
        var opened = [Int]()
        for j in 0..<outside {
            let (w, hw) = try forward.open(try forward.proof(current, in: &t), in: &t)
            opened.append(w)
            longer = try extend(
                longer,
                value: values[j],
                record: w,
                snoc: .left(.hypothesis(hw)),
                needs: child.needs,
                in: &forward,
                &t,
            )
            current = .right(.hypothesis(hw))
        }
        let psiForward = try forward.scope.lift(psi, from: each.scope.depth, in: &t)
        let reached = try down(psiForward, child, forward, longer, env, try forward.proof(current, in: &t), &t)
        let there = try forward.close(reached, in: &t)
        var backward = Frame(each.scope)
        let h2 = backward.assume(psi)
        var built = r
        var made = [(record: Int, snoc: Int)]()
        for j in 0..<outside {
            let prefix = j == 0 ? r.variable : made[j - 1].record
            let at = try [prefix, numerals.levels[r.length + j], values[j]].map { try backward.variable($0, in: &t) }
            let (w, hw) = try backward.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
            made.append((w, hw))
            built = try extend(
                built,
                value: values[j],
                record: w,
                snoc: .hypothesis(hw),
                needs: child.needs,
                in: &backward,
                &t,
            )
        }
        let psiBackward = try backward.scope.lift(psi, from: each.scope.depth, in: &t)
        var proof = try up(psiBackward, child, backward, built, env, try backward.hypothesis(h2, in: &t), &t)
        let target = try backward.scope.lift(left, from: each.scope.depth, in: &t)
        var shapes = [NodeID]()
        var level = target
        for j in 0..<outside {
            guard case .ifolEx(.i, let body) = t[level] else { throw ComprehensionError.misread(target) }
            shapes.append(body)
            let at = try instantiate(body, with: try backward.variable(made[j].record, in: &t), in: &t)
            guard case .folAnd(_, let rest) = t[at] else { throw ComprehensionError.misread(target) }
            level = rest
        }
        for j in (0..<outside).reversed() {
            let both = try t.intern(.folAndIntro(try backward.hypothesis(made[j].snoc, in: &t), proof))
            proof = try t.intern(.isaExIntro(both, try backward.variable(made[j].record, in: &t), body: shapes[j]))
        }
        let back = try backward.close(proof, in: &t)
        return try each.close(try t.intern(.folIffIntro(there, back)), in: &t)
    }

    private func lambdaExactness(
        _ definition: NodeID,
        _ lambda: Lambda,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        var body = definition
        for _ in 0..<lambda.outside {
            guard case .ifolAll(.i, let b) = t[body] else { throw ComprehensionError.misread(definition) }
            body = b
        }
        let psi = try dropping(try iff(body, t).right, lambda.outside, in: &t)
        return try extensions(psi, lambda.bundle, lambda.outside, f, r, env, &t)
    }

    private func liftedBound(
        _ phi: NodeID,
        _ lift: Lift,
        _ C: Int,
        _ hc: Int,
        _ g: inout Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> Bound {
        let lambdas = try lift.lambdas.map { id -> (variable: Int, approximation: Int) in
            guard let b = env.binders[id], let a = b.approximation else { throw ComprehensionError.misread(phi) }
            return (b.variable, a)
        }
        var p = try t.intern(.isaAllElim(try g.hypothesis(lift.cls.hyp, in: &t), try g.variable(r.variable, in: &t)))
        p = try t.intern(.folImpliesElim(p, try g.proof(r.tuple, in: &t)))
        p = try eliminated(
            p,
            at: try lambdas.map { try g.variable($0.variable, in: &t) },
            premises: try lambdas.map { try g.hypothesis($0.approximation, in: &t) },
            in: &t,
        )
        p = try eliminated(p, at: [try g.variable(C, in: &t)], premises: [try g.hypothesis(hc, in: &t)], in: &t)
        return Bound(variable: C, constraint: hc, approximation: try g.have(p, in: &t), record: r)
    }

    private func sectionAt(_ s: Int, _ phi: NodeID, _ f: Frame, _ env: Env, _ t: inout Table) throws -> NodeID {
        guard
            let approximation = env.sections[s],
            case .folPred(_, let args) = t[phi]
        else { throw ComprehensionError.misread(phi) }
        return try eliminated(try f.hypothesis(approximation, in: &t), at: Array(args.dropLast()), in: &t)
    }

    /// `snoc_EX` at the record, its next index and `v`: `∃b. snoc(r, n, v, b)`.
    private func snocExists(_ r: Record, _ v: Int, _ f: Frame, _ t: inout Table) throws -> NodeID {
        let at = try [r.variable, numerals.levels[r.length], v].map { try f.variable($0, in: &t) }
        return try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t)
    }

    /// An atom's read row at the record, `elem(r, A) ↔ W(y⃗)`, and its witness's property, `W(y⃗) ↔ atom(y⃗)`, if the
    /// witness is not the atom itself.
    private func atomParts(
        _ row: Row,
        _ es: [Int],
        _ witness: Witness,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> (NodeID, NodeID?) {
        let sized = try t.intern(.folForallElim(
            try at(row, f, r, &t),
            try f.variable(numerals.levels[r.length], in: &t),
        ))
        let p = try entries(es, try t.intern(.folImpliesElim(sized, try f.proof(r.tuple, in: &t))), f, r, &t)
        let values = try es.map { try f.variable(r.entries[$0], in: &t) }
        switch witness {
        case .fixed:
            return (p, nil)
        case .property(let h):
            return (p, try eliminated(try f.hypothesis(h, in: &t), at: values, in: &t))
        case .opened(let m, let c, let T, let C):
            guard let bound = env.binders[m] else { throw ComprehensionError.noEntry(m) }
            if bound.variable == C.cls { return (p, nil) }
            let fact = ConstantFact(constant: c, type: T, fact: .agreement)
            let agree = try eliminated(
                try cited(fact, try statement(fact, in: &t), &t),
                at: [try f.variable(C.cls, in: &t), try f.variable(bound.variable, in: &t)],
                premises: [
                    try f.hypothesis(C.hyp, in: &t),
                    try f.hypothesis(bound.constraint, in: &t),
                ],
                in: &t,
            )
            return (p, try eliminated(agree, at: values, in: &t))
        }
    }

    private func tupleRead(_ row: Row, _ es: [Int], _ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        try entries(es, try t.intern(.folImpliesElim(try at(row, f, r, &t), try f.proof(r.tuple, in: &t))), f, r, &t)
    }

    private func entries(_ es: [Int], _ p: NodeID, _ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        var p = p
        for j in es {
            guard j < r.length else { throw ComprehensionError.noEntry(j) }
            p = try eliminated(
                p,
                at: [try f.variable(r.entries[j], in: &t)],
                premises: [try entry(j, of: r, in: f.scope, &t)],
                in: &t,
            )
        }
        return p
    }

    private func operands(_ c: Connective, _ phi: NodeID, _ t: Table) throws -> [NodeID] {
        switch (c, t[phi]) {
        case (.and, .folAnd(let a, let b)), (.or, .folOr(let a, let b)), (.iff, .folIff(let a, let b)),
             (.implies, .folImplies(let a, let b)): return [a, b]
        case (.not, .folNot(let a)): return [a]
        default: throw ComprehensionError.misread(phi)
        }
    }

    private func at(_ row: Row, _ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        try t.intern(.isaAllElim(try f.hypothesis(row.hyp, in: &t), try f.variable(r.variable, in: &t)))
    }

    private func bottom(_ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        guard let zero = numerals.zero else { throw ComprehensionError.noEntry(0) }
        let notMember = { (s: Scope, t: inout Table) throws -> NodeID in
            let n0 = try s.variable(numerals.levels[0], in: &t)
            let def = try eliminated(try base.cite(.zeroDef, in: &t), at: [n0], in: &t)
            let none = try t.intern(.folIffElimL(def, try s.hypothesis(zero, in: &t)))
            return try t.intern(.isaAllElim(none, try s.variable(r.variable, in: &t)))
        }
        let member = try t.intern(.folPred(
            .base("elem"),
            args: [try f.variable(r.variable, in: &t), try f.variable(numerals.levels[0], in: &t)],
        ))
        var there = Frame(f.scope)
        let h = there.assume(member)
        let absurd = try t.intern(.folNotElim(try notMember(there.scope, &t), try there.hypothesis(h, in: &t)))
        var back = Frame(f.scope)
        let h2 = back.assume(try t.intern(.folBottom))
        let any = try t.intern(.folBottomElim(try back.hypothesis(h2, in: &t), member))
        return try t.intern(.folIffIntro(try there.close(absurd, in: &t), try back.close(any, in: &t)))
    }

    /// `∀t⃗. X(t⃗) ↔ Y(t⃗)` from `∀t⃗. X ↔ Z` and `∀t⃗. Z ↔ Y` — the second taken the other way round with `symmetric`.
    private func joined(
        _ first: NodeID,
        _ second: NodeID,
        _ outside: Int,
        _ f: Frame,
        symmetric: Bool,
        _ t: inout Table,
    ) throws -> NodeID {
        var each = Frame(f.scope)
        let values = try (0..<outside).map { _ in each.fix(.i) }.map { try each.variable($0, in: &t) }
        let a = try eliminated(try lifted(first, from: f.scope, to: each.scope, in: &t), at: values, in: &t)
        var b = try eliminated(try lifted(second, from: f.scope, to: each.scope, in: &t), at: values, in: &t)
        if symmetric { b = try base.applied(.iffSymm, [try sides(b, t).left, try sides(b, t).right], [b], in: &t) }
        return try each.close(try chained(a, b, &t), in: &t)
    }

    private func liftedAtom(
        _ phi: NodeID,
        _ m: Int,
        _ U: Int,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        guard
            let bound = env.binders[m], let approximation = bound.approximation, let site = bound.record,
            case .folPred(_, let args) = t[phi]
        else { throw ComprehensionError.misread(phi) }
        var chain = [r]
        while chain.count < args.count {
            guard let link = chain[0].link else { throw ComprehensionError.misread(phi) }
            chain.insert(link.parent, at: 0)
        }
        guard chain[0] === site else { throw ComprehensionError.misread(phi) }
        let values = try chain.dropFirst().map { r -> NodeID in
            guard let v = r.entries.last else { throw ComprehensionError.misread(phi) }
            return try f.variable(v, in: &t)
        }
        let at = try eliminated(try f.hypothesis(approximation, in: &t), at: values, in: &t)
        let same = try unique(chain, U, 0, site.variable, { s, t in
            try eliminated(try base.cite(.eqRefl, in: &t), at: [try s.variable(site.variable, in: &t)], in: &t)
        }, f, &t)
        let read = try chained(at, same, &t)
        return try base.applied(.iffSymm, [phi, try sides(read, t).right], [read], in: &t)
    }

    private func unique(
        _ chain: [Record],
        _ U: Int,
        _ j: Int,
        _ x: Int,
        _ prefix: @escaping (Scope, inout Table) throws -> NodeID,
        _ g: Frame,
        _ t: inout Table,
    ) throws -> NodeID {
        let current = chain[j]
        let next = chain[j + 1]
        guard
            let link = next.link, let v = next.entries.last,
            let last = chain.last
        else { throw ComprehensionError.noEntry(j) }
        let n = numerals.levels[current.length]
        var h = Frame(g.scope)
        let b = h.fix(.i)
        let snoc = try [x, n, v, b].map { try h.variable($0, in: &t) }
        let s = h.assume(try t.intern(.folPred(.base("snoc"), args: snoc)))
        let base = base
        let equal = { (sc: Scope, t: inout Table) throws -> NodeID in
            let at = try [current.variable, x, n, n, v, next.variable, b].map { try sc.variable($0, in: &t) }
            let refl = try eliminated(try base.cite(.eqRefl, in: &t), at: [try sc.variable(n, in: &t)], in: &t)
            return try eliminated(
                try base.cite(.snocEQ, in: &t),
                at: at,
                premises: [
                    try prefix(sc, &t),
                    refl,
                    try sc.proof(link.snoc, in: &t),
                    try sc.hypothesis(s, in: &t),
                ],
                in: &t,
            )
        }
        let inner: NodeID
        if j == chain.count - 2 {
            let bv = try h.variable(b, in: &t)
            let lastv = try h.variable(last.variable, in: &t)
            let Uv = try h.variable(U, in: &t)
            let toLast = try eliminated(
                try base.cite(.eqSymm, in: &t),
                at: [lastv, bv],
                premises: [try equal(h.scope, &t)],
                in: &t,
            )
            inner = try eliminated(try base.cite(.congElemL, in: &t), at: [bv, lastv, Uv], premises: [toLast], in: &t)
        } else {
            inner = try unique(chain, U, j + 1, b, equal, h, &t)
        }
        let premise = try h.close(inner, in: &t)
        let member = try t.intern(.folPred(
            .base("elem"),
            args: [try g.variable(last.variable, in: &t), try g.variable(U, in: &t)],
        ))
        let some = try base.instance(
            .snocSome,
            [try t.intern(.folLetterAbs(body: try sides(inner, t).left)), member],
            in: &t,
        )
        return try eliminated(some, at: try [x, n, v].map { try g.variable($0, in: &t) }, premises: [premise], in: &t)
    }

    private func chained(_ p: NodeID, _ q: NodeID, _ t: inout Table) throws -> NodeID {
        let (a, b) = try sides(p, t), c = try sides(q, t).right
        return try base.applied(.iffTrans, [a, b, c], [p, q], in: &t)
    }
}

func iff(_ formula: NodeID, _ t: Table) throws -> (left: NodeID, right: NodeID) {
    guard case .folIff(let a, let b) = t[formula] else { throw TableError.principalConnective(formula) }
    return (a, b)
}

func sides(_ p: NodeID, _ t: Table) throws -> (left: NodeID, right: NodeID) {
    guard case .folIff(let a, let b)? = t.conclusion(of: p).map({ t[$0] })
    else { throw TableError.principalConnective(p) }
    return (a, b)
}

func substituted(_ phi: NodeID, _ terms: [NodeID], in t: inout Table) throws -> NodeID {
    var wrapped = phi
    for _ in terms { wrapped = try t.intern(.isaAbs(.i, body: wrapped)) }
    return try beta(wrapped, terms, in: &t)
}

func dropping(_ phi: NodeID, _ k: Int, in t: inout Table) throws -> NodeID {
    var wrapped = phi
    for _ in 0..<k { wrapped = try t.intern(.isaAbs(.i, body: wrapped)) }
    var dropped = try unshift(wrapped, in: &t)
    for _ in 0..<k {
        guard case .isaAbs(_, let body) = t[dropped] else { throw TableError.principalConnective(dropped) }
        dropped = body
    }
    return dropped
}
