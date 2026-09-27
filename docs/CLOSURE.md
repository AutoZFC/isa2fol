# CLOSURE — what every named ZF theorem rests on

**Generated.** `isa2fol closure data/zf_export`. Each named theorem of the ZF sessions is followed through EVERY
citation — named theorems, derived Pure/IFOL/FOL rules, unnamed boxes — down to axioms and
oracles, class discharges included. A definition is an axiom named `*_def` or `*_def_raw` (by
name). Counts are named theorems whose closure contains it.

| session | named theorems |
|---|---:|
| ZF | 3616 |
| ZF-AC | 477 |
| ZF-Coind | 288 |
| ZF-Constructible | 2121 |
| ZF-IMP | 284 |
| ZF-Induct | 1496 |
| ZF-Resid | 340 |
| ZF-UNITY | **not in the export** |
| ZF-ex | 798 |
| **all** | **9420** |

## Oracles — unproved steps

(none)

## Pure — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `Pure.reflexive` | 8843 | 93.9% |
| `Pure.equal_elim` | 8832 | 93.8% |
| `Pure.symmetric` | 8832 | 93.8% |
| `Pure.combination` | 8825 | 93.7% |
| `Pure.transitive` | 8726 | 92.6% |
| `Pure.prop_def` | 8174 | 86.8% |
| `Pure.equal_intr` | 7981 | 84.7% |
| `Pure.conjunction_def` | 7700 | 81.7% |
| `Pure.abstract_rule` | 7627 | 81.0% |
| `Pure.term_def` | 28 | 0.3% |

## IFOL — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `IFOL.impI` | 8047 | 85.4% |
| `IFOL.conjI` | 8042 | 85.4% |
| `IFOL.term_class_def` | 7965 | 84.6% |
| `IFOL.mp` | 7960 | 84.5% |
| `IFOL.conjunct1` | 7893 | 83.8% |
| `IFOL.iff_def_raw` | 7841 | 83.2% |
| `IFOL.FalseE` | 7820 | 83.0% |
| `IFOL.not_def_raw` | 7819 | 83.0% |
| `IFOL.refl` | 7767 | 82.5% |
| `IFOL.conjunct2` | 7759 | 82.4% |
| `IFOL.eq_reflection` | 7751 | 82.3% |
| `IFOL.spec` | 7668 | 81.4% |
| `IFOL.True_def_raw` | 7619 | 80.9% |
| `IFOL.allI` | 7610 | 80.8% |
| `IFOL.subst` | 7607 | 80.8% |
| `IFOL.iff_reflection` | 7572 | 80.4% |
| `IFOL.exI` | 7497 | 79.6% |
| `IFOL.disjE` | 7496 | 79.6% |
| `IFOL.disjI1` | 7496 | 79.6% |
| `IFOL.disjI2` | 7496 | 79.6% |
| `IFOL.exE` | 7495 | 79.6% |
| `IFOL.ex1_def_raw` | 7316 | 77.7% |
| `IFOL.Let_def_raw` | 439 | 4.7% |

## FOL — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `FOL.classical` | 7756 | 82.3% |
| `FOL.induct_implies_def_raw` | 4022 | 42.7% |
| `FOL.induct_forall_def_raw` | 3947 | 41.9% |
| `FOL.induct_equal_def_raw` | 105 | 1.1% |
| `FOL.induct_conj_def_raw` | 2 | 0.0% |

## ZF sessions — axioms that are not definitions

| axiom | theorems reaching it | % |
|---|---:|---:|
| `ZF_Base.replacement` | 7313 | 77.6% |
| `ZF_Base.Union_iff` | 7069 | 75.0% |
| `ZF_Base.extension` | 7048 | 74.8% |
| `ZF_Base.Pow_iff` | 7023 | 74.6% |
| `ZF_Base.foundation` | 6969 | 74.0% |
| `ZF_Base.infinity` | 4129 | 43.8% |
| `AC.AC` | 51 | 0.5% |
| `Language.constNEE` | 9 | 0.1% |
| `Language.c_appI` | 6 | 0.1% |
| `LList.flip_LCons` | 5 | 0.1% |
| `LList.flip_LNil` | 5 | 0.1% |
| `Static.isof_app` | 4 | 0.0% |

Plus **984 definitions** from the ZF sessions; the most-reached is reached by 7461 (`ZF_Base.Ball_def_raw`).

## Monomorphisation

**23 named theorems are polymorphic.** Every other named theorem is ground.
**0 citations use a type variable their citing proof does not bind** — every instance is determined by its citer.
