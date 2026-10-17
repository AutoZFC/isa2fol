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

final class Record {
    init(empty variable: Int, tuple: Int) {
        (self.variable, self.tuple, entries, link) = (variable, tuple, [], nil)
    }

    init(_ parent: Record, value: Int, variable: Int, snoc: Int, tuple: Int, newest: Int, keep: Int) {
        (self.variable, self.tuple, entries, link) = (
            variable,
            tuple,
            parent.entries + [value],
            (parent, snoc, newest, keep),
        )
    }

    let variable: Int
    let tuple: Int
    let entries: [Int]
    let link: (parent: Record, snoc: Int, newest: Int, keep: Int)?

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
}

enum Rewrite {
    case forall
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
    case rewritten(Rewrite, Built)
    case bottom(Int)
    case atom(Row, [Int], Witness)
    case unfolded(BaseStatement, Built)
    case sectioned(Int, Built)
    case opened(binder: Int, Row, Built)
    case lambda(binder: Int, Lambda, Built)
    case lifted(binder: Int, Lift, Built)
    case liftedAtom(binder: Int, Int)

    var cls: Int {
        switch self {
        case .connective(_, let row, _), .exists(let row, _), .atom(let row, _, _): row.cls
        case .rewritten(_, let inner), .unfolded(_, let inner), .sectioned(_, let inner), .opened(_, _, let inner),
             .lambda(_, _, let inner), .lifted(_, _, let inner):
            inner.cls
        case .bottom(let empty), .liftedAtom(_, let empty): empty
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
    let zero: Int
}

private enum StandIn {
    case opened(Constant, IRType, Row)
    case lambda(Int)
    case lifted(Lift)
}

private enum Key: Hashable {
    case read([Int], Int)
    case connective(Connective, [Int])
    case exists(Int, Int)
    case witness(BaseStatement)
    case applied(Int)
    case setConstant(Constant)
    case constantClass(Constant, IRType)
    case lifted(Constant, IRType, Int, [Int])
}

private let relations: [String: BaseStatement] = ["Pow": .powDef, "Union": .unionDef]

struct Comprehension {
    init(base: Base, top: Frame, in t: inout Table) throws {
        var top = top
        let (n0, h0) = try top.open(try base.cite(.zeroEX, in: &t), in: &t)
        let n = try top.variable(n0, in: &t)
        let def = try eliminated(try base.cite(.zeroDef, in: &t), at: [n], in: &t)
        let isEmpty = try t.intern(.folIffElimL(def, try top.hypothesis(h0, in: &t)))
        let tuple = try eliminated(try base.cite(.tupleZero, in: &t), at: [n], premises: [isEmpty], in: &t)
        let empty = Record(empty: n0, tuple: try top.have(tuple, in: &t))
        (self.base, self.top, numerals, self.empty) = (
            base,
            top,
            Numerals(levels: [n0], successors: [], zero: h0),
            empty,
        )
    }

    let base: Base
    var top: Frame
    let empty: Record

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
        raw: NodeID,
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
            snoc: snocs[j],
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

    mutating func build(_ phi: NodeID, _ roles: [Role], _ k: Int, _ t: inout Table) throws -> Built {
        switch t[phi] {
        case .folAnd(let a, let b): return try binary(.and, a, b, roles, k, &t)

        case .folOr(let a, let b): return try binary(.or, a, b, roles, k, &t)

        case .folIff(let a, let b): return try binary(.iff, a, b, roles, k, &t)

        case .folNot(let a):
            let x = try build(a, roles, k, &t)
            return try connective(.not, [x], &t)

        case .folImplies(let a, let b):
            let x = try build(a, roles, k, &t)
            let y = try build(b, roles, k, &t)
            let notY = try connective(.not, [y], &t)
            let both = try connective(.and, [x, notY], &t)
            return .rewritten(.implies, try connective(.not, [both], &t))

        case .folBottom:
            return .bottom(numerals.levels[0])

        case .ifolEx(.i, let body):
            let x = try build(body, roles + [.entry(k)], k + 1, &t)
            return try exists(x, k, &t)

        case .ifolAll(.i, let body):
            let x = try build(body, roles + [.entry(k)], k + 1, &t)
            let negated = try connective(.not, [x], &t)
            let some = try exists(negated, k, &t)
            return .rewritten(.forall, try connective(.not, [some], &t))

        case .folPred(let p, let args):
            return try atom(phi, p, args, roles, k, &t)

        case .isaConst, .isaVarApp:
            var naming = Naming()
            let core = try naming.atom(t[phi], in: &t)
            let named = try naming.chain.formula(core, in: &t)
            return try chain(named, naming.pieces[...], [:], roles, k, &t)

        case .ifolAll, .ifolEx, .isaFree, .isaBound, .isaAbs, .isaOfClass, .isaAllIntro, .isaAllElim, .isaReflexive,
             .isaSymmetric, .isaTransitive, .isaCombination, .isaAbstract, .isaClassical, .isaIffReflection,
             .isaDefinition, .isaPropAll, .isaPropIntro, .isaPropBound, .folImpliesIntro, .folImpliesElim, .use, .hyp,
             .isaGuard, .isaExIntro, .isaExElim, .folBound, .folForall, .folExists, .folAndIntro, .folAndElimL,
             .folAndElimR, .folOrIntroL, .folOrIntroR, .folOrElim, .folNotIntro, .folNotElim, .folIffIntro,
             .folIffElimL,
             .folIffElimR, .folForallIntro, .folForallElim, .folExistsIntro, .folExistsElim, .folBottomElim,
             .folClassicalAbsurd, .folSchemaInst, .folLetterAll, .folLetter, .folLetterAbs:
            throw ComprehensionError.unread(phi)
        }
    }

    private var numerals: Numerals
    private var memo = [Key: Row]()
    private var standIns = [Int: StandIn]()
    private var sections = [Int: Section]()

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
                case .ifolEx(.i, let body) = t[phi],
                case .folAnd(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let S = try setConstantClass(c, &t)
            let constraint = Built.atom(try readRow([k], S.cls, &t), [k], .property(S.hyp))
            let remaining = try chain(after, rest, ids, roles + [.entry(k)], k + 1, &t)
            return try exists(try connective(.and, [constraint, remaining], &t), k, &t)

        case .tuple, .value, .applied:
            guard
                case .ifolEx(.i, let body) = t[phi],
                case .folAnd(let c, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let constraint = try build(c, roles + [.entry(k)], k + 1, &t)
            let remaining = try chain(after, rest, ids, roles + [.entry(k)], k + 1, &t)
            return try exists(try connective(.and, [constraint, remaining], &t), k, &t)

        case .constantClass(let c, let T, let classes):
            guard
                case .folExists(let body) = t[phi],
                case .folAnd(_, let after) = t[body]
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
                case .folExists(let body) = t[phi],
                case .folAnd(_, let after) = t[body]
            else { throw ComprehensionError.unread(phi) }
            let (outside, raw) = try classBody(try shift(lambda, by: position, in: &t), raw: true, in: &t)
            _ = try numeral(k + outside, &t)
            let bundle = try build(raw, roles + (0..<outside).map { Role.entry(k + $0) }, k + outside, &t)
            let m = standIns.count
            standIns[m] = .lambda(bundle.cls)
            var bound = ids
            bound[position] = m
            return .lambda(
                binder: m,
                Lambda(bundle: bundle, outside: outside),
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
        let rs = try args.map { x -> Role in
            let d: Int
            switch t[x] {
            case .isaBound(let j, _): d = j
            case .folBound(let j): d = j
            default: throw ComprehensionError.unread(phi)
            }
            guard d < roles.count else { throw ComprehensionError.unread(phi) }
            return roles[roles.count - 1 - d]
        }
        let entries = { (rs: ArraySlice<Role>) throws -> [Int] in
            try rs.map { r -> Int in
                guard case .entry(let j) = r else { throw ComprehensionError.unread(phi) }
                return j
            }
        }
        switch (name, rs.count) {
        case ("eq", 2): return try witnessed(try witness(.clsDiag, &t), try entries(rs[...]), &t)

        case ("zero", 1): return try witnessed(try witness(.clsZero, &t), try entries(rs[...]), &t)

        case ("nsucc", 2): return try witnessed(try witness(.clsNsucc, &t), try entries(rs[...]), &t)

        case ("snoc", 4): return try witnessed(try snocs(&t), try entries(rs[...]), &t)

        case ("elem", 2), ("pmem", 3), ("apply", 3):
            let es = try entries(rs.dropLast())
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
            }
        let base = base
        let row = try open(.connective(c, classes), &t) { top, t in
            try eliminated(try base.cite(s, in: &t), at: try classes.map { try top.variable($0, in: &t) }, in: &t)
        }
        return .connective(c, row, children)
    }

    private mutating func exists(_ child: Built, _ k: Int, _ t: inout Table) throws -> Built {
        let n = try numeral(k, &t)
        let A = child.cls
        _ = try numeral(k + 1, &t)
        let base = base
        let row = try open(.exists(n, A), &t) { top, t in
            try eliminated(
                try base.cite(.rowEx, in: &t),
                at: [try top.variable(n, in: &t), try top.variable(A, in: &t)],
                in: &t,
            )
        }
        return .exists(row, child)
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
        let successor = numerals.successors[k]
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

struct Reading {
    let base: Base
    let numerals: Numerals
    let empty: Record

    func extend(
        _ r: Record,
        value v: Int,
        record b: Int,
        snoc s: Int,
        in f: inout Frame,
        _ t: inout Table,
    ) throws -> Record {
        let k = r.length
        let a = try f.variable(r.variable, in: &t)
        let n = try f.variable(numerals.levels[k], in: &t)
        let m = try f.variable(numerals.levels[k + 1], in: &t)
        let x = try f.variable(v, in: &t)
        let y = try f.variable(b, in: &t)
        let tuple = try eliminated(
            try base.cite(.tupleSnoc, in: &t),
            at: [a, y, n, x, m],
            premises: [
                try f.hypothesis(r.tuple, in: &t),
                try f.hypothesis(numerals.successors[k], in: &t),
                try f.hypothesis(s, in: &t),
            ],
            in: &t,
        )
        let ht = try f.have(tuple, in: &t)
        let new = try eliminated(
            try base.cite(.snocNew, in: &t),
            at: [a, n, x, y],
            premises: [
                try f.hypothesis(s, in: &t),
                try isaGuard(n, .i, &t),
                try isaGuard(x, .i, &t),
            ],
            in: &t,
        )
        let hn = try f.have(new, in: &t)
        let keep = try eliminated(
            try base.cite(.snocKeep, in: &t),
            at: [a, n, x, y],
            premises: [try f.hypothesis(s, in: &t)],
            in: &t,
        )
        let hk = try f.have(keep, in: &t)
        return Record(r, value: v, variable: b, snoc: s, tuple: ht, newest: hn, keep: hk)
    }

    /// ⚠ OPENS ITS PREFIXES, FIXING ONE VARIABLE PER ENTRY: a formula taken in `f` before it is that many levels
    /// shallow.
    func record(_ values: [Int], in f: inout Frame, _ t: inout Table) throws -> Record {
        var r = empty
        for v in values {
            let at = try [r.variable, numerals.levels[r.length], v].map { try f.variable($0, in: &t) }
            let (b, s) = try f.open(try eliminated(try base.cite(.snocEX, in: &t), at: at, in: &t), in: &t)
            r = try extend(r, value: v, record: b, snoc: s, in: &f, &t)
        }
        return r
    }

    func tupled(_ r: Record, in s: Scope, _ t: inout Table) throws -> NodeID {
        var records = [r]
        while let link = records[0].link { records.insert(link.parent, at: 0) }
        let n = r.length
        var witnesses = [try s.variable(numerals.levels[0], in: &t)]
        var constraints = [try s.hypothesis(numerals.zero, in: &t)]
        for j in 1..<n {
            guard let link = records[j].link else { throw ComprehensionError.noEntry(j) }
            witnesses += [try s.variable(numerals.levels[j], in: &t), try s.variable(records[j].variable, in: &t)]
            constraints += [try s.hypothesis(numerals.successors[j - 1], in: &t), try s.hypothesis(link.snoc, in: &t)]
        }
        guard let last = r.link else { throw ComprehensionError.noEntry(0) }
        return try closing(tupleBinders(n), witnesses, constraints, try s.hypothesis(last.snoc, in: &t), in: &t)
    }

    func entry(_ j: Int, of r: Record, in s: Scope, _ t: inout Table) throws -> NodeID {
        guard let link = r.link, j < r.length else { throw ComprehensionError.noEntry(j) }
        if j == r.length - 1 { return try s.hypothesis(link.newest, in: &t) }
        let kept = try entry(j, of: link.parent, in: s, &t)
        return try eliminated(
            try s.hypothesis(link.keep, in: &t),
            at: [
                try s.variable(numerals.levels[j], in: &t),
                try s.variable(r.entries[j], in: &t),
            ],
            premises: [kept],
            in: &t,
        )
    }

    func read(_ phi: NodeID, _ b: Built, _ f: Frame, _ r: Record, _ env: Env, _ t: inout Table) throws -> NodeID {
        let proof: NodeID
        switch b {
        case .connective(let c, let row, let children):
            let parts = try operands(c, phi, t)
            var exact = [NodeID]()
            for (x, child) in zip(parts, children) { exact.append(try read(x, child, f, r, env, &t)) }
            let letters = try zip(exact, parts).flatMap { [try sides($0.0, t).left, $0.1] }
            let congruence: BaseStatement =
                switch c {
                case .and: .congAnd
                case .or: .congOr
                case .iff: .congIff
                case .not: .congNot
                }
            proof = try chained(try at(row, f, r, &t), try base.applied(congruence, letters, exact, in: &t), &t)

        case .exists(let row, let child):
            let atA = try at(row, f, r, &t)
            guard
                case .ifolEx(.i, let body) = t[phi],
                case .ifolEx(.i, let extended) = t[try sides(atA, t).right]
            else {
                throw ComprehensionError.misread(phi)
            }
            let every = try extensions(body, child, 1, f, r, env, &t)
            let moved = try base.applied(
                .congExists,
                [try t.intern(.folLetterAbs(body: extended)), try t.intern(.folLetterAbs(body: body))],
                [every],
                in: &t,
            )
            proof = try chained(atA, moved, &t)

        case .rewritten(let how, let inner):
            let equivalent: NodeID
            let conversion: NodeID
            switch how {
            case .forall:
                guard case .ifolAll(.i, let body) = t[phi] else { throw ComprehensionError.misread(phi) }
                equivalent = try t.intern(.folNot(try t.intern(.ifolEx(.i, body: try t.intern(.folNot(body))))))
                conversion = try base.instance(.forallAsNexists, [try t.intern(.folLetterAbs(body: body))], in: &t)

            case .implies:
                guard case .folImplies(let x, let y) = t[phi] else { throw ComprehensionError.misread(phi) }
                equivalent = try t.intern(.folNot(try t.intern(.folAnd(x, try t.intern(.folNot(y))))))
                conversion = try base.instance(.impAsNand, [x, y], in: &t)
            }
            proof = try chained(try read(equivalent, inner, f, r, env, &t), conversion, &t)

        case .bottom:
            proof = try bottom(f, r, &t)

        case .atom(let row, let es, let witness):
            var p = try t.intern(.folForallElim(
                try at(row, f, r, &t),
                try f.variable(numerals.levels[r.length], in: &t),
            ))
            p = try t.intern(.folImpliesElim(p, try f.hypothesis(r.tuple, in: &t)))
            for j in es {
                guard j < r.length else { throw ComprehensionError.noEntry(j) }
                p = try eliminated(
                    p,
                    at: [try f.variable(r.entries[j], in: &t)],
                    premises: [try entry(j, of: r, in: f.scope, &t)],
                    in: &t,
                )
            }
            let values = try es.map { try f.variable(r.entries[$0], in: &t) }
            switch witness {
            case .fixed:
                proof = p
            case .property(let h):
                proof = try chained(p, try eliminated(try f.hypothesis(h, in: &t), at: values, in: &t), &t)
            case .opened(let m, let c, let T, let C):
                guard let bound = env.binders[m] else { throw ComprehensionError.misread(phi) }
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
                proof = try chained(p, try eliminated(agree, at: values, in: &t), &t)
            }

        case .unfolded(let def, let inner):
            guard case .folPred(_, let args) = t[phi] else { throw ComprehensionError.misread(phi) }
            let definition = try eliminated(try base.cite(def, in: &t), at: args, in: &t)
            let d = try sides(definition, t).right
            proof = try chained(
                try read(d, inner, f, r, env, &t),
                try base.applied(.iffSymm, [phi, d], [definition], in: &t),
                &t,
            )

        case .sectioned(let s, let inner):
            guard
                let approximation = env.sections[s],
                case .folPred(_, let args) = t[phi]
            else { throw ComprehensionError.misread(phi) }
            let section = try eliminated(try f.hypothesis(approximation, in: &t), at: Array(args.dropLast()), in: &t)
            let d = try sides(section, t).right
            proof = try chained(
                try read(d, inner, f, r, env, &t),
                try base.applied(.iffSymm, [phi, d], [section], in: &t),
                &t,
            )

        case .opened(let m, let C, let inner):
            proof = try binder(phi, inner, Frame(f.scope), r, env, &t, bind: { _, c, hc, env, _ in
                var bound = env
                bound.binders[m] = Bound(variable: c, constraint: hc, approximation: nil, record: nil)
                return bound
            }, witness: { _, _ in (C.cls, C.hyp) })

        case .lambda(let m, let lambda, let inner):
            proof = try lambdaBinder(phi, m, lambda, inner, f, r, env, &t)

        case .lifted(let m, let lift, let inner):
            proof = try liftedBinder(phi, m, lift, inner, f, r, env, &t)

        case .liftedAtom(let m, let U):
            proof = try liftedAtom(phi, m, U, f, r, env, &t)
        }
        guard try sides(proof, t).right == phi else { throw ComprehensionError.misread(phi) }
        return proof
    }

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
        return try each.close(try extended(psi, child, values, 0, each, r, env, &t), in: &t)
    }

    private func operands(_ c: Connective, _ phi: NodeID, _ t: Table) throws -> [NodeID] {
        switch (c, t[phi]) {
        case (.and, .folAnd(let a, let b)), (.or, .folOr(let a, let b)), (.iff, .folIff(let a, let b)): return [a, b]
        case (.not, .folNot(let a)): return [a]
        default: throw ComprehensionError.misread(phi)
        }
    }

    private func at(_ row: Row, _ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        try t.intern(.isaAllElim(try f.hypothesis(row.hyp, in: &t), try f.variable(r.variable, in: &t)))
    }

    private func extended(
        _ psi: NodeID,
        _ child: Built,
        _ values: [Int],
        _ j: Int,
        _ g: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        var h = Frame(g.scope)
        let b = h.fix(.i)
        let snoc = try [r.variable, numerals.levels[r.length], values[j], b].map { try h.variable($0, in: &t) }
        let s = h.assume(try t.intern(.folPred(.base("snoc"), args: snoc)))
        let longer = try extend(r, value: values[j], record: b, snoc: s, in: &h, &t)
        let inside = try shift(psi, by: 1, in: &t)
        let inner = j == values.count - 1
            ? try read(inside, child, h, longer, env, &t)
            : try extended(inside, child, values, j + 1, h, longer, env, &t)
        let premise = try h.close(inner, in: &t)
        let some = try base.instance(
            .snocSome,
            [try t.intern(.folLetterAbs(body: try sides(inner, t).left)), psi],
            in: &t,
        )
        let at = try [r.variable, numerals.levels[r.length], values[j]].map { try g.variable($0, in: &t) }
        return try eliminated(some, at: at, premises: [premise], in: &t)
    }

    private func bottom(_ f: Frame, _ r: Record, _ t: inout Table) throws -> NodeID {
        let notMember = { (s: Scope, t: inout Table) throws -> NodeID in
            let n0 = try s.variable(numerals.levels[0], in: &t)
            let def = try eliminated(try base.cite(.zeroDef, in: &t), at: [n0], in: &t)
            let none = try t.intern(.folIffElimL(def, try s.hypothesis(numerals.zero, in: &t)))
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

    private func binder(
        _ phi: NodeID,
        _ inner: Built,
        _ h: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
        bind: (inout Frame, Int, Int, Env, inout Table) throws -> Env,
        witness: (inout Frame, inout Table) throws -> (Int, Int),
    ) throws -> NodeID {
        guard
            case .folExists(let body) = t[phi],
            case .folAnd(let constraint, let rest) = t[body]
        else { throw ComprehensionError.misread(phi) }
        var h = h
        var g = Frame(h.scope)
        let c = g.fix(nil)
        let hc = g.assume(constraint)
        let bound = try bind(&g, c, hc, env, &t)
        let exact = try g.close(try read(rest, inner, g, r, bound, &t), in: &t)
        let every = try h.have(exact, in: &t)
        let member = try t.intern(.folPred(
            .base("elem"),
            args: [try h.variable(r.variable, in: &t), try h.variable(inner.cls, in: &t)],
        ))
        var there = Frame(h.scope)
        let hm = there.assume(member)
        let (w, holds) = try witness(&there, &t)
        let atW = try eliminated(
            try there.hypothesis(every, in: &t),
            at: [try there.variable(w, in: &t)],
            premises: [try there.hypothesis(holds, in: &t)],
            in: &t,
        )
        let restAtW = try t.intern(.folIffElimL(atW, try there.hypothesis(hm, in: &t)))
        let both = try t.intern(.folAndIntro(try there.hypothesis(holds, in: &t), restAtW))
        let forward = try there.close(try t.intern(.folExistsIntro(both, try there.variable(w, in: &t))), in: &t)
        var back = Frame(h.scope)
        let hx = back.assume(phi)
        let (v, hv) = try back.open(try back.hypothesis(hx, in: &t), in: &t)
        let atV = try eliminated(
            try back.hypothesis(every, in: &t),
            at: [try back.variable(v, in: &t)],
            premises: [try t.intern(.folAndElimL(try back.hypothesis(hv, in: &t)))],
            in: &t,
        )
        let backward = try back.close(
            try t.intern(.folIffElimR(atV, try t.intern(.folAndElimR(try back.hypothesis(hv, in: &t))))),
            in: &t,
        )
        return try h.close(try t.intern(.folIffIntro(forward, backward)), in: &t)
    }

    private func lambdaBinder(
        _ phi: NodeID,
        _ m: Int,
        _ lambda: Lambda,
        _ inner: Built,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        guard
            case .folExists(let body) = t[phi],
            case .folAnd(let constraint, _) = t[body]
        else { throw ComprehensionError.misread(phi) }
        var definition = constraint
        for _ in 0..<lambda.outside {
            guard case .ifolAll(.i, let b) = t[definition] else { throw ComprehensionError.misread(phi) }
            definition = b
        }
        let psi = try dropping(try iff(definition, t).right, lambda.outside, in: &t)
        var h = Frame(f.scope)
        let exact = try h.have(try extensions(psi, lambda.bundle, lambda.outside, f, r, env, &t), in: &t)
        let outside = lambda.outside
        let n = numerals.levels[r.length]
        let n1 = numerals.levels[r.length + 1]
        return try binder(phi, inner, h, r, env, &t, bind: { g, K, hc, env, t in
            let approximation = try joined(hc, exact, outside, g, symmetric: true, &t)
            var bound = env
            bound.binders[m] = Bound(
                variable: K,
                constraint: hc,
                approximation: try g.have(approximation, in: &t),
                record: nil,
            )
            return bound
        }, witness: { there, t in
            let at = try (outside == 1 ? [n] : [n, n1]).map { try there.variable($0, in: &t) }
                + [try there.variable(lambda.bundle.cls, in: &t), try there.variable(r.variable, in: &t)]
            let (K0, hK0) = try there.open(
                try eliminated(try base.cite(outside == 1 ? .lamPred : .lamClass, in: &t), at: at, in: &t),
                in: &t,
            )
            return (K0, try there.have(try joined(hK0, exact, outside, there, symmetric: false, &t), in: &t))
        })
    }

    private func liftedBinder(
        _ phi: NodeID,
        _ m: Int,
        _ lift: Lift,
        _ inner: Built,
        _ f: Frame,
        _ r: Record,
        _ env: Env,
        _ t: inout Table,
    ) throws -> NodeID {
        let lambdas = try lift.lambdas.map { id -> (variable: Int, approximation: Int) in
            guard let b = env.binders[id], let a = b.approximation else { throw ComprehensionError.misread(phi) }
            return (b.variable, a)
        }
        return try binder(phi, inner, Frame(f.scope), r, env, &t, bind: { g, C, hc, env, t in
            var p = try t.intern(.isaAllElim(
                try g.hypothesis(lift.cls.hyp, in: &t),
                try g.variable(r.variable, in: &t),
            ))
            p = try t.intern(.folImpliesElim(p, try g.hypothesis(r.tuple, in: &t)))
            p = try eliminated(
                p,
                at: try lambdas.map { try g.variable($0.variable, in: &t) },
                premises: try lambdas.map { try g.hypothesis($0.approximation, in: &t) },
                in: &t,
            )
            p = try eliminated(p, at: [try g.variable(C, in: &t)], premises: [try g.hypothesis(hc, in: &t)], in: &t)
            var bound = env
            bound.binders[m] = Bound(variable: C, constraint: hc, approximation: try g.have(p, in: &t), record: r)
            return bound
        }, witness: { there, t in
            let fact = ConstantFact(constant: lift.constant, type: lift.type, fact: .classExists)
            let at = try lambdas.map { try there.variable($0.variable, in: &t) }
            return try there.open(
                try eliminated(try cited(fact, try statement(fact, in: &t), &t), at: at, in: &t),
                in: &t,
            )
        })
    }

    private func joined(
        _ first: Int,
        _ second: Int,
        _ outside: Int,
        _ f: Frame,
        symmetric: Bool,
        _ t: inout Table,
    ) throws -> NodeID {
        var each = Frame(f.scope)
        let values = try (0..<outside).map { _ in each.fix(.i) }.map { try each.variable($0, in: &t) }
        let a = try eliminated(try each.hypothesis(first, in: &t), at: values, in: &t)
        var b = try eliminated(try each.hypothesis(second, in: &t), at: values, in: &t)
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
                    try sc.hypothesis(link.snoc, in: &t),
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
