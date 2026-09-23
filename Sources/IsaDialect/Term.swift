/// Five cases, not six. The export writes schematic variables as `.free`;
/// `Var` (YXML tag 2) has ZERO occurrences in all 16,798 statements.
///
/// ⚠ That is a fact about the export's PREPROCESSING, not about Isabelle. If a
/// tag 2 ever arrives, reading must fail loudly here rather than be absorbed.
public indirect enum Term: Sendable {
    case constant(String, types: [Sort])        // tag 0 — `types` is its instantiation
    case free(String, sort: Sort)               // tag 1
    case bound(Int)                             // tag 3 — de Bruijn
    case abs(String, sort: Sort, body: Term)    // tag 4 — λ
    case app(Term, Term)                        // tag 5
}
