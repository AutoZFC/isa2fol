/// The Pure frame. `Pure.prop` is the identity on propositions and is ERASED at
/// read time; `Pure.conjunction`, `Pure.sort_constraint` and `Pure.term` are
/// refused by name there. None of them reach a pass.
public indirect enum Prop: Sendable {
    case term(Term)                             // Trueprop t — the o⇒prop coercion
    case imp(Prop, Prop)                        // ⟹
    case all(String, sort: Sort, body: Prop)    // ⋀
    case eq(Term, Term, sort: Sort)             // ≡
    case ofClass(Sort, String)                  // OFCLASS
}
