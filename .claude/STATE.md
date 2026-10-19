# STATE — isa2fol
HEAD "Linear proof size: in a proof a term is its value; a formula meets the values through its lemma, once" (parents
"Proof size: …", "Step 6: …") · primitives · 2026-10-19.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -3 --format=%s` | `Linear proof size: …`, `Proof size: …`, `Step 6: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `16600` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 141, 121, 43 passed; Lowering 149 with 2 failing: `infinityReadsSuccByTheTheoremStatingItsMembers`, `anInstanceAtACompoundArgumentIsBetaAtItsValue` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `zf` Proved 22 of 22 |
| `swift build -c release`, then `MEM=80G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (23:30, 50.4 GB peak), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 369`; `refused, named: 3247`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 3239`, led by `ZF_Base.BOX_fe88880df9563825` 595, `FOL.int_ex_simps.2` 296; 35 parts, every one `exit 0  stderr 0`; claims 7964 of 7964, schemas 568 of 568; 419,775,237 bytes |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Linear proof size — in a proof, a term is its value": decisions 1–4, the Built paragraph, Measured
  (with 5–7), and "The losses, fixed at their providers", 5–7.
- `Sources/Lowering/Meeting.swift` — `met`, the meeting lemma at a site; `Atom.convert`, `own`, `betaBlock`, `applied`:
  β at the class variable's application, its arguments read at their names; `MeetingProver.prove`: only `unmet` is
  unbuilt.
- `Sources/Lowering/Logic.swift` — `finished`, `metBelowLetters`, `letterInstance`: a statement's letters above its
  values. `Sources/Lowering/Values.swift` — a value, its fact, where it is fixed.
- `base/tiers/zf` — `replacement_NBG` in the translator's words, proved from `replacement_ex` by a generated `cong_*`
  walk, `tup2_ue` and `pmem2_ue` at its leaves (the header says so).

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| a statement's letters stay above its values, in its proof and at its citations | `aSchemaHoldingACompoundTermKeepsItsLetterAboveItsValues` |
| β reads the class variable's application at its arguments' names | `anApplicationAtACompoundArgumentOverABoundVariableIsBetaAtItsName`, `aNestedApplicationOfAFunctionLambdaIsBetaAtEachValue`, `aDefinitionApplyingItsFunctionToACompoundArgumentIsItsUnfoldingAtItsTerms` |
| a ZF axiom cited is its lemma, proved from base's statement in the translator's words | `AxiomTests` (`replacementIsReadFromBasesStatement`) |
| emission cites a step only inside the block that wrote it | `aStepWrittenInAClosedBlockIsDerivedAgain` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**: a shape the β walk cannot align is refused
  unbuilt before the walk (`own`), never left to throw `misaligned` in it.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL**: a change to the naming changes
  them; `replacement_NBG` was left behind once and only the kernel saw it.
- ⚠ **THE COMPLETE RUN NEEDS `MEM=80G`** (50.4 GB peak): the CI's 32 GB kills it.
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE**: the count rose over HEAD
  while 25 of the run before were lost.
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it.
- ⚠ **A FORMULA BUILT AT ONE FRAME IS LIFTED BEFORE A DEEPER FRAME READS IT** (`Scope.lift`); ⚠ **`t[try instantiate(…)]`
  READS A COPY TAKEN BEFORE THE MUTATION** (rule 13).
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**; ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**;
  ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 369 lowered — the run before "Linear proof size"'s set exactly, HEAD's 279 among them; 240 of them `X_def` | §0's complete run; its parts' `claim`/`schema` names diffed |
| refused 3,247: no owner 7 (unrestricted type variables), logic 1 (`AC.AC`), 3,239 cite a refused statement | §0's complete run |
| the unit: 7,964 claims, 568 schemas, 419.8 MB; class existence two thirds of it | §0's complete run, its `steps by kind` |
| `infinity` and `λx. x = x` (a body naming its argument twice) refused unbuilt; both passed before "Linear proof size" (`Proof size`, every suite green) | the two failing tests of §0 |
| comments 261/16600 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The class prover's lemmas doubled with decision 3's universal naming (146.5 + 107.8 MB against 73.8 + 56.2 MB, the
  size trace before decisions 5–7): not traced to its cause.
- The memory peak is the table (143.5M nodes) and the emission of 420 MB; not profiled.

## 6. Open decisions
- **Memory and the class prover**: the complete run is above the CI's 32 GB, and class existence doubled — which first.
- **The two unit tests HEAD passed**: `infinity` needs `c_UNFOLD` at `Inf`; `λx. x = x` needs β to meet a body naming
  its argument twice (UNIQ of the second naming).
- **For review**: the build decisions of "Step 6", "Proof size" and "Linear proof size" (DESIGN), and the generated walk
  in `base/tiers/zf`.

## 7. Next action
Get the user's choice among §6's first two; then write its section in `DESIGN.md` and agree it decision by decision
before any code. Done when the user has agreed every decision of that section.
