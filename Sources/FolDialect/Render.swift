/// ⚠ THE CHECKER'S GRAMMAR IS THE ONLY AUTHORITY on this syntax. The test that
/// matters is that the real `proof_checker` accepts what this emits, never that
/// it matches our own reading of the grammar.
public func render(_ f: Formula) -> String {
    switch f {
    case .predicate(let name, let args, _):
        return args.isEmpty
            ? name
            : "\(name)(\(args.map(\.name).joined(separator: ", ")))"
    case .bottom:
        return "False"
    case .not(let b):
        return "~\(render(b))"
    case .binary(let op, let l, let r):
        let s: String
        switch op {
        case .and: s = "&"
        case .or: s = "|"
        case .implies: s = "->"
        case .iff: s = "<->"
        }
        return "(\(render(l)) \(s) \(render(r)))"
    case .quantified(let q, _, let v, let body):
        let k: String
        switch q {
        case .forAll: k = "forall"
        case .exists: k = "exists"
        }
        return "\(k) \(v). \(render(body))"
    }
}

public func render(_ d: Declaration) -> String {
    switch d {
    case .axiom(let n, let f):
        return "axiom \(n): \(render(f))"
    case .claim(let n, let f):
        return "claim \(n): \(render(f))"
    case .schema(let n, let params, let f):
        let ps = params.map { "\($0.0)(\($0.1))" }.joined(separator: ", ")
        return "schema \(n) [\(ps)]: \(render(f))"
    }
}
