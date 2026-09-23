public enum Declaration: Sendable {
    case axiom(String, Formula)                             // only base/ may emit one
    case claim(String, Formula)
    case schema(String, params: [(String, Int)], Formula)

    public var name: String {
        switch self {
        case .axiom(let n, _), .claim(let n, _), .schema(let n, _, _): return n
        }
    }

    public var statement: Formula {
        switch self {
        case .axiom(_, let f), .claim(_, let f), .schema(_, _, let f): return f
        }
    }
}
