# CLOSURE — what every named ZF theorem rests on

**Generated.** `isa2fol closure data/zf_export`. Each named theorem of the ZF sessions is followed through every citation — named
theorems, derived Pure/IFOL/FOL rules, unnamed boxes, class discharges — down to axioms. A citation is read as
the reader types it (`DESIGN.md` §4.3b): an axiom of the foundation, a definition, or an axiom a theory above
the foundation states. Counts are named theorems whose closure contains it.

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

The reader refuses none of them, nor any theorem they cite.

## pure — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `Pure.prop_def` | 8174 | 86.8% |
| `Pure.conjunction_def` | 7700 | 81.7% |
| `Pure.term_def` | 28 | 0.3% |

## ifol — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `IFOL.term_class_def` | 7965 | 84.6% |
| `IFOL.iff_def_raw` | 7841 | 83.2% |
| `IFOL.not_def_raw` | 7819 | 83.0% |
| `IFOL.True_def_raw` | 7619 | 80.9% |
| `IFOL.subst` | 7607 | 80.8% |
| `IFOL.exI` | 7497 | 79.6% |
| `IFOL.ex1_def_raw` | 7316 | 77.7% |
| `IFOL.Let_def_raw` | 439 | 4.7% |

## fol — every axiom and definition reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `FOL.induct_implies_def_raw` | 4022 | 42.7% |
| `FOL.induct_forall_def_raw` | 3947 | 41.9% |
| `FOL.induct_equal_def_raw` | 105 | 1.1% |
| `FOL.induct_conj_def_raw` | 2 | 0.0% |

## zf — every axiom reached

| axiom | theorems reaching it | % |
|---|---:|---:|
| `ZF_Base.replacement` | 7313 | 77.6% |
| `ZF_Base.Union_iff` | 7069 | 75.0% |
| `ZF_Base.extension` | 7048 | 74.8% |
| `ZF_Base.Pow_iff` | 7023 | 74.6% |
| `ZF_Base.foundation` | 6969 | 74.0% |
| `ZF_Base.infinity` | 4129 | 43.8% |
| `AC.AC` | 51 | 0.5% |

Plus **984 definitions** of the zf family; the most-reached is reached by 7461 (`ZF_Base.Ball_def_raw`).

## Axioms of theories above the foundation — not ZF's

| axiom | theorems reaching it | % |
|---|---:|---:|
| `Language.constNEE` | 9 | 0.1% |
| `Language.c_appI` | 6 | 0.1% |
| `LList.flip_LCons` | 5 | 0.1% |
| `LList.flip_LNil` | 5 | 0.1% |
| `Static.isof_app` | 4 | 0.0% |

## Type variables

**23 named theorems state a type variable.** A citation at a type variable its citing proof does not
bind stops the read (`undeclaredTypeVariable`), so every instance is determined by its citer.
