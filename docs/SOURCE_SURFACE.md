# SOURCE SURFACE — what IsaDialect must actually model

**Measured, with a standing handle.** Every number below regenerates with

```bash
scripts/source-surface.py
```

which needs `~/repos/isabelle-study/bin/isa-deps` (set `ISA_DEPS` to override)
and refuses rather than guessing if it is absent.

This is a **census, not mathematics**. `docs/FOUNDATION.md` states what the
translation must satisfy; this states what the source corpus actually contains.
Keep them apart: a count never justifies a specification, and FOUNDATION.md
carries no corpus figure with a live handle.

---

## The cut, and why it is the one that matters

Population: the **3,616 named theorems** of the 37 `ZF.*` theories. Two ways to
ask what they rest on, and they differ by 20×:

| | |
|---|---|
| **surface** | the theorem's own proof region, **stopping at every named theorem**. Sees `IFOL.conjI` and stops — never unfolds it into Pure |
| **deep** | the whole DAG, down to the axioms |

**The dialect needs the surface.** A proof cites `IFOL.conjI`; the translation
emits a citation of the target's counterpart. It never replays conjI's own
derivation, so Pure's role *inside* conjI is not the dialect's problem.

> **⚠ A HIGH `deep` PERCENTAGE IS NOT A REQUIREMENT.** `FOL.excluded_middle` is
> reached by **89.7%** of ZF theorems and is cited directly by **none** — ZF's
> proofs cite `FOL.classical`, `ccontr` and `swap` instead. Reading `deep` as
> "needed" would put 64 rules into the dialect that no ZF proof ever names.

> **⚠ `occ` AND `thms` MEASURE DIFFERENT THINGS AND `occ` CAN BE FAR SMALLER.**
> Proof regions overlap, and `occ` counts each shared node once. `Pure.equal_intr`
> is `thms=2027, occ=3`: two thousand theorems reach it through three shared
> nodes. **Rank by `thms`.**

---

## Table 1 — statements

| | constant | thms | % | occ |
|---|---|---:|---:|---:|
| `⌜⌝` | `IFOL.Trueprop` | 3348 | 92.6% | 7767 |
| `⟹` | `Pure.imp` | 2006 | 55.5% | 4452 |
| `=` | `IFOL.eq` | 1687 | 46.7% | 2102 |
| `⟷` | `IFOL.iff` | 486 | 13.4% | 492 |
| `≡` | `Pure.eq` | 288 | 8.0% | 292 |
| `⋀` | `Pure.all` | 261 | 7.2% | 391 |
| `¬` | `IFOL.Not` | 257 | 7.1% | 286 |
| `∧` | `IFOL.conj` | 251 | 6.9% | 362 |
| `∨` | `IFOL.disj` | 148 | 4.1% | 183 |
| `⟶` | `IFOL.imp` | 95 | 2.6% | 146 |
| `∃` | `IFOL.Ex` | 88 | 2.4% | 145 |
| `∀` | `IFOL.All` | 28 | 0.8% | 45 |
| `⊥` | `IFOL.False` | 19 | 0.5% | 19 |
| `⊤` | `IFOL.True` | 16 | 0.4% | 17 |
| `∃!` | `IFOL.Ex1` | 10 | 0.3% | 10 |
| `` | `IFOL.Let` | 3 | 0.1% | 5 |

### Sorts

| sort | thms | % | occ |
|---|---:|---:|---:|
| `ZF_Base.i` | 3554 | 98.3% | 37153 |
| `fun` | 774 | 21.4% | 3570 |
| `IFOL.o` | 448 | 12.4% | 1903 |
| `prop` | 11 | 0.3% | 23 |

Plus **249 distinct ZF mathematical constants** — the 197 term constants and 54
predicates, tabulated in `~/isabelle-object-constants.md`.

### Three findings the dialect rests on

1. **FOL contributes ZERO statement constants.** Classical logic appears only in
   proofs. A statement reader needs Pure + IFOL + ZF and nothing else.
2. **Pure contributes exactly three: `⟹`, `≡`, `⋀`.**
   `Pure.conjunction`, `Pure.prop`, `Pure.term` and `Pure.sort_constraint` are
   absent from every ZF statement — which is why `Prop` has cases for the first
   three and `Refusal.metaConjunction` / `Refusal.pureInternal` for the rest.
   Refusing them is not a gap; it is refusing something that never arrives.
3. **Four sort names, and they are the `Sort` enum.** `ZF_Base.i`, `IFOL.o`,
   `prop`, `fun` — `.i`, `.o`, `.prop`, `.arrow`. `.variable` covers type
   variables, which are not tag-0 names and so do not appear here.

> **⚠ THE CENSUS CANNOT TELL A SORT FROM A TERM CONSTANT BY ITSELF.** YXML tag 0
> is *both* `Type` and `Const` — the variant numbering collides. The four sorts
> above are separated **by name**, in `SORTS` in the script. A fifth sort would
> land silently in the constant column; the reader must decode the tree, not
> match the tag.

---

## Table 2 — proofs

The citation frontier: what a ZF proof names that is not itself a ZF theorem.

### Pure — all 7 axioms, plus 6 derived rules

| rule | kind | thms | occ |
|---|---|---:|---:|
| `Pure.reflexive` | **axiom** | 2835 | 56069 |
| `Pure.combination` | **axiom** | 2835 | 52634 |
| `Pure.equal_elim` | **axiom** | 2837 | 21346 |
| `Pure.transitive` | **axiom** | 2492 | 17360 |
| `Pure.symmetric` | **axiom** | 2718 | 15875 |
| `Pure.protectD` | derived | 2742 | 3175 |
| `Pure.protectI` | derived | 2741 | 3023 |
| `Pure.abstract_rule` | **axiom** | 2059 | 1341 |
| `Pure.conjunctionD2` | derived | 121 | 134 |
| `Pure.conjunctionD1` | derived | 121 | 116 |
| `Pure.conjunctionI` | derived | 135 | 76 |
| `Pure.meta_spec` | derived | 4 | 6 |
| `Pure.equal_intr` | **axiom** | 2027 | 3 |

**Pure is not avoidable, and not because IFOL is defined over it.** These are
cited *directly by ZF's own proofs*, 171,158 times. The equational five —
`reflexive`, `combination`, `equal_elim`, `transitive`, `symmetric` — are 163k of
that, and they are tactic-generated rewriting inside ZF proofs. Any plan that
models IFOL and expects Pure to fall out is wrong by two orders of magnitude.

### ZF axioms — all 7 cited on the surface

| ZF axiom | thms | occ | deep |
|---|---:|---:|---:|
| `ZF_Base.extension` | 1245 | 18 | 82.9% |
| `ZF_Base.Union_iff` | 1579 | 58 | 82.8% |
| `ZF_Base.Pow_iff` | 93 | 244 | 81.4% |
| `ZF_Base.infinity` | 2 | 3 | 37.6% |
| `ZF_Base.foundation` | 621 | 4 | 81.7% |
| `ZF_Base.replacement` | 2 | 2 | 86.4% |
| `AC.AC` | 2 | 3 | 1.2% |

`replacement` is named by **2** theorems yet underlies 86.4% — it is reached
through the definitions of comprehension and `Lambda`, not by citation. Choice is
genuinely isolated at 1.2%.

### IFOL and FOL — 132 rules

60 IFOL + 72 FOL, 107,366 occurrences. The top fifteen:

| rule | thms | occ |
|---|---:|---:|
| `IFOL.eq_reflection` | 2143 | 13957 |
| `IFOL.impI` | 2094 | 11842 |
| `IFOL.iff_reflection` | 2208 | 11765 |
| `IFOL.rev_mp` | 1941 | 11186 |
| `IFOL.iff_reflection_T` | 2116 | 8814 |
| `IFOL.TrueI` | 2218 | 7966 |
| `FOL.swap` | 2200 | 4627 |
| `IFOL.def_imp_iff` | 1879 | 4523 |
| `IFOL.notE` | 2080 | 3453 |
| `FOL.ccontr` | 2087 | 3017 |
| `IFOL.subst` | 1951 | 1604 |
| `IFOL.meta_eq_to_obj_eq` | 1797 | 1600 |
| `IFOL.sym` | 1870 | 1531 |
| `FOL.IFOL_simps(1)` | 1103 | 1463 |
| `IFOL.conjE` | 1964 | 1313 |

### And two populations that are not the frontier

- **207 object definitions** (`*_def_raw`), each cited **exactly once** — one per
  defined constant. These are the `@def` bodies S2/S3 compile from.
- **2,203 ZF theorems** cited by other ZF theorems. That is ZF content, not the
  frontier: the dialect resolves them by `(theory, serial)` like any other.

---

## What the whole surface costs

| | statements | proofs |
|---|---:|---:|
| Pure | 3 constants | 7 axioms + 6 derived rules |
| IFOL | 13 constants | 60 rules |
| FOL | **0** | 72 rules |
| ZF | 249 constants | 7 axioms + 207 definitions |
| sorts | 4 | — |

**64 rules are excluded by the surface cut** — 3 Pure, 61 IFOL/FOL, 0 ZF. Every
ZF axiom is on the surface; nothing about set theory hides below the cut.
