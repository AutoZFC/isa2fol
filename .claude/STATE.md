# STATE — isa2fol
HEAD "The class of a λ holding a proposition: a letter an atom of a class body, read by base's row_letter" (parent
"Memory: a unit of work's nodes leave with it; …") · primitives · 2026-10-20. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `The class of a λ holding a proposition: …`, `Memory: a unit of work's nodes leave with it; …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17081` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `37ae807` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT, the binary that checked §0's unit |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 132, 47 passed; Lowering 158 with 2 failing: `infinityReadsSuccByTheTheoremStatingItsMembers`, `anInstanceAtACompoundArgumentIsBetaAtItsValue` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `classes` 66 of 66 and 1 schema of 1 (`row_letter`), `tuples` 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (31:05, peak 26.1 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (3:52) | `lowered … 1900`; `refused, named: 1716`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 1708`, led by `Arith.natify_non_succ` 366; `lemmas … unbuilt: 425`; 50 parts, every one `exit 0  stderr 0`; claims 23094 of 23094, schemas 3637 of 3637; 1,413,876,020 bytes; stages `expand 6.8 s, logic 446.8 s, registry 724.0 s, fol 391.1 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb `37ae807`, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`)
is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "The class of a λ holding a proposition": decision 1, Built, the decision made in the build, Measured;
  "Memory — a unit of work's nodes leave with it" before it.
- `base/tiers/classes.fol.def` and `.proof` — `row_letter`, proved by cases.
- `Sources/Lowering/Comprehension.swift` — `build` at `isaBound(_, .o)` (a letter, a `.fixed` role), `Built.letter`,
  its reading each way through `at`.
- `Sources/IR/Pass.swift` — `Pass.walk` / `Walk.run`; `Run.lower`; `Sources/IR/Traversal.swift` — `Memo`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a letter is an atom of a class body, read by base's `row_letter`; a λ's class at a letter is a schema in it | `aLambdaHoldingALetterHasItsClassReadingTheLetterByItsRow`, `aLetterIsAnAtomOfAClassBodyAmongTheOthers`, `anInstanceAtALambdaHoldingALetterIsItsClassThenBeta`, `aLambdaHoldingATruthSetVariableIsASchemaCitedAtItsTruth` |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| a node two units share is lowered once a pass, its form kept where a unit enters it | `aNodeTwoStatementsHoldIsLoweredOnceAPassBothReadingItsForm`, `aNodeEveryUnitReachesBelowAnotherSharedNodeLeavesItsFormWithItsLayer` |
| a lemma two units request is one statement; each request remaps every ID it holds | `aLemmaTwoStatementsRequestInTheirLayersIsOneStatementOfTheUnit`, `eachRequestRemapsEveryIDItHolds` |
| a variable only the proof uses is at `i` or `o`, constant in its arguments | `aVariableOnlyTheProofUsesIsConstantInItsArguments`, `aHiddenVariableIsTheWitnessOfItsTypesInhabitation` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems.
- ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**: bound to a local, each import copied the unit's table whole.
- ⚠ **A PASS'S WALK IS BUILT ONCE A RUN**: built per statement, Expand unfolded every definition it owns per statement.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**: a shape the β walk cannot align is refused
  unbuilt (`unmet`), never left to throw `misaligned`.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL.**
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it; ⚠ **A LINE
  THAT OPENS OR CLOSES A BLOCK IS NEVER SHARED**.
- ⚠ **`t[try instantiate(…)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13); ⚠ **A STEP-COUNT ESTIMATE IS NOT A
  MEASUREMENT**; ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file);
  ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 1,900 lowered, 241 of them `X_def`; the 369 HEAD lowered all kept | §0's complete run; its parts' `claim`/`schema` names diffed against HEAD's run |
| the unit: 23,094 claims, 3,637 schemas, 50 parts, 1.41 GB, all Proved | §0's complete run and check |
| the complete run fits the CI's 32 GB: peak 26.1 GB | §0's run under `/usr/bin/time -v` |
| `infinity` and `λx. x = x` refused unbuilt | the two failing tests of §0 |
| comments 274/17081 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 425 lemmas refused unbuilt are mostly β's: before the step, 424 of the 597 were `BETA_<fp>` — 223 at the check
  that a shared argument is named first in both forms, 92 at the reduced body's comparison, 53 at the λ's arity, 45 at
  an argument named twice — and one `infinity`'s; after it, not traced.
- Logic's quarter over the run before the memory step is a layer's lookup below it and the import's hashing: from a
  profile taken before the import carried sorts.

## 6. Open decisions
- **The next blocker**: trace the 1,716 refused named theorems to their roots — the β shapes, `infinity`, `AC.AC`.
- **Size**: the unit grew from 206 MB to 1.41 GB with 1,531 more named theorems; not measured against Isabelle's size.

## 7. Next action
Get the user's choice among §6. Done when the user has chosen.
