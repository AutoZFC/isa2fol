public struct ThmID: Hashable, Sendable {
    public let theory: String
    public let serial: String
    public init(theory: String, serial: String) {
        self.theory = theory
        self.serial = serial
    }
}

/// Seven cases, named for what they DO rather than for the export's tags. The
/// export contains no others: MinProof, Hyp, PClass and Oracle have zero
/// occurrences.
public indirect enum Proof: Sendable {
    case hypothesis(Int)                        // PBound
    case theorem(ThmID)                         // PThm
    case axiom(String)                          // PAxm
    case impIntro(Prop, Proof)                  // AbsP
    case impElim(Proof, Proof)                  // AppP
    case allIntro(String, sort: Sort, Proof)    // Abst
    case allElim(Proof, Term)                   // AppT
}
