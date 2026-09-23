/// ⚠ A BINDER CARRIES ITS KIND. Without it the guard rule is only half
/// checkable: a class quantifier MUST be unguarded (guarding it makes the claim
/// FALSE, not redundant), and nothing could catch a class that was guarded.
public enum Binder: Sendable {
    case setVar
    case classVar
}

public enum Quantifier: Sendable {
    case forAll
    case exists
}

public enum BinOp: Sendable {
    case and
    case or
    case implies
    case iff
}

public indirect enum Formula: Sendable {
    case predicate(String, args: [Term], isSchema: Bool)
    case bottom
    case not(Formula)
    case binary(BinOp, Formula, Formula)
    case quantified(Quantifier, Binder, String, body: Formula)
}
