# STATE — isa2fol
HEAD "Class existence at a few steps a node: a tuple one atom, TUPLE_ROW_n; a level one fact, snoc_facts" (parent
"Linear proof size: …") · primitives · 2026-10-19.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `Class existence at a few steps a node: …`, `Linear proof size: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `16727` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 141, 121, 43 passed; Lowering 152 with 2 failing: `infinityReadsSuccByTheTheoremStatingItsMembers`, `anInstanceAtACompoundArgumentIsBetaAtItsValue` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `tuples` Proved 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=80G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (13:48, 45.8 GB peak), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 369`; `refused, named: 3247`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 3239`, led by `ZF_Base.BOX_fe88880df9563825` 595, `FOL.int_ex_simps.2` 296; 35 parts, every one `exit 0  stderr 0`; claims 7969 of 7969, schemas 568 of 568; 272,542,148 bytes; `steps by kind` all 5,166,635 written |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream. The checker is fol-zfc-comb `224d60e`, built only with
`bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Class existence at a few steps a node — a tuple one atom, a level one fact": decisions 1–2, Built,
  Measured, and the paragraph naming the next decisions.
- `Sources/Lowering/Comprehension.swift` — `Raw` (a class body by its parts, or a formula as written), `built` and
  `tupled` (a tuple one `.tuple` atom, `TUPLE_ROW` at its entries' positions and the record's length), `Numerals`
  (`first`; no zero at symbolic positions), `Reading.extend` (`snoc_facts`, one cut), `tupleRead`.
- `Sources/Lowering/Classes.swift` — `ClassProofs.row`: `TUPLE_ROW_n` by the generator at symbolic positions, the record
  given. `Sources/Lowering/Reify.swift` — `ClassBody`, `classBody`.
- `base/tiers/tuples.fol.def` — `snoc_facts`, guarded where `tuple_snoc` is.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| a tuple the class prover builds is one atom, read by `TUPLE_ROW_n`; no `cls_zero`, `cls_nsucc`, `cls_snoc4`, `read4` in a λ's class | `theIdentityClassReadsItsArgumentTupleByItsRow`, `aNamingsTupleIsReadByItsRow` |
| `TUPLE_ROW_0`–`_2` kernel-checked | `theTupleFormulaIsOneRowOverRecordPositions` |
| a ZF axiom cited is its lemma, proved from base's statement in the translator's words | `AxiomTests` (`replacementIsReadFromBasesStatement`) |
| emission cites a step only inside the block that wrote it | `aStepWrittenInAClosedBlockIsDerivedAgain` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**: a shape the β walk cannot align is refused
  unbuilt before the walk (`own`), never left to throw `misaligned` in it.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL**: a change to the naming changes
  them; `replacement_NBG` was left behind once and only the kernel saw it.
- ⚠ **THE COMPLETE RUN NEEDS `MEM=80G`** (45.8 GB peak): the CI's 32 GB kills it.
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it.
- ⚠ **A FORMULA BUILT AT ONE FRAME IS LIFTED BEFORE A DEEPER FRAME READS IT** (`Scope.lift`); ⚠ **`t[try instantiate(…)]`
  READS A COPY TAKEN BEFORE THE MUTATION** (rule 13).
- ⚠ **A STEP-COUNT ESTIMATE IS NOT A MEASUREMENT**: "under 250" for `CLASS ⟨λx. x⟩` measured 365; Fol's `∃`-elim at `i`,
  cuts and carrying are per-level structure no row removes.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**; ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**;
  ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 369 lowered, the same set as before the step; 240 of them `X_def` | §0's complete run; its parts' `claim`/`schema` names diffed |
| the unit: 7,969 claims (5 `TUPLE_ROW_n`), 568 schemas, 272.5 MB; class existence 67% of 5.17M steps | §0's complete run, its `steps by kind` |
| `CLASS ⟨λx. x⟩` 365 steps; λ classes 123 steps a statement binder, growing as binders^1.35 | `theIdentityClassReadsItsArgumentTupleByItsRow`; the emitted `CLASS_*` proofs against their statements |
| `infinity` and `λx. x = x` (a body naming its argument twice) refused unbuilt | the two failing tests of §0 |
| comments 261/16727 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Of the class lemmas' 3.55M steps, cuts and `∃`-elims (`assume`, `implies_intro`, assumptions used) are about 47%: an
  attribution by each step's head, not by the walk's structure.
- The memory peak is the table (119.1M nodes); not profiled.

## 6. Open decisions
- **The next size step**: Fol's `∃`-elim at `i` (about 10 steps each), the cuts the walk writes, the carrying of entries
  per level, what the two walks repeat — which first, from DESIGN's numbers.
- **Memory**: the complete run is above the CI's 32 GB.
- **The two unit tests HEAD fails**: `infinity` needs `c_UNFOLD` at `Inf`; `λx. x = x` needs β to meet a body naming
  its argument twice.

## 7. Next action
Get the user's choice among §6; write its section in `DESIGN.md` and agree it decision by decision before any code. Done
when the user has agreed every decision of that section.
