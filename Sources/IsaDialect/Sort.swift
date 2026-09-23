/// Isabelle's type language, as far as the export uses it.
///
/// `.variable` is the one case a GROUND statement may not contain; see
/// `Statement<Stage>` for how that is enforced at the type level rather than by
/// a check that runs.
public indirect enum Sort: Hashable, Sendable {
    case i                      // ZF_Base.i  — terms
    case o                      // IFOL.o     — formulas
    case prop                   // Pure.prop
    case arrow(Sort, Sort)
    case variable(String)       // 'a

    public var isGround: Bool {
        switch self {
        case .i, .o, .prop: return true
        case .arrow(let a, let b): return a.isGround && b.isGround
        case .variable: return false
        }
    }
}
