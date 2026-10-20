# STATE — isa2fol
HEAD "Memory: a unit of work's nodes leave with it; a pass's walk once a run, what its units share lowered once"
(parent "A variable only the proof uses, constant in its arguments: …") · primitives · 2026-10-19.  RUN §0 BEFORE
TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `Memory: a unit of work's nodes leave with it; …`, `A variable only the proof uses, constant in its arguments: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17070` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 132, 47 passed; Lowering 155 with 2 failing: `infinityReadsSuccByTheTheoremStatingItsMembers`, `anInstanceAtACompoundArgumentIsBetaAtItsValue` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `tuples` 27 of 27, `metafun` 18 of 18, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (27:33, peak 25.5 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 369`; `refused, named: 3247`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 3239`, led by `Arith.natify_non_succ` 366, `ZF_Base.BOX_190a994237a728ec` 181; `lemmas … unbuilt: 597`; 35 parts, every one `exit 0  stderr 0`; claims 7969 of 7969, schemas 568 of 568; 206,264,082 bytes; stages `expand 6.6 s, logic 417.6 s, registry 654.4 s, fol 333.0 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream. The checker is fol-zfc-comb `224d60e`, built only with
`bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Memory — a unit of work's nodes leave with it": decisions 1–3, Built, the decisions made in the build,
  Measured; "A variable only the proof uses, constant in its arguments" before it.
- `Sources/IR/Table.swift` — `Table(over:)` (a layer), `existing`, `imported` (marks children, a step's conclusion and a
  lemma's request; carries each node's sort); the ⚠ on `imported`.
- `Sources/IR/Traversal.swift` — `Memo` (a node two units reach, kept where a unit enters it), `transform(_:_:sharing:in:)`.
- `Sources/IR/Pass.swift` — `Pass.walk` / `Walk.run`; `Run.lower` (the walk built once a run, the memo counted,
  citation order, a citer of a refused statement refused before the pass), `lowered`.
- `Sources/Reader/Terms.swift` — `hide` and `.hidden`: one variable per result type, `i` or `o`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| a node two units share is lowered once a pass, its form kept where a unit enters it | `aNodeTwoStatementsHoldIsLoweredOnceAPassBothReadingItsForm`, `aNodeEveryUnitReachesBelowAnotherSharedNodeLeavesItsFormWithItsLayer` |
| a lemma two units request is one statement; each request remaps every ID it holds | `aLemmaTwoStatementsRequestInTheirLayersIsOneStatementOfTheUnit`, `eachRequestRemapsEveryIDItHolds` |
| a pass meets a cited statement before its citer, handed its form | `aPassMeetsACitedStatementBeforeItsCiterAndIsHandedItsForm`, `aCitationReadsTheFormItIsHanded` |
| a variable only the proof uses is at `i` or `o`, constant in its arguments | `aVariableOnlyTheProofUsesIsConstantInItsArguments`, `aHiddenVariableIsTheWitnessOfItsTypesInhabitation` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**: bound to a local, each import copied the unit's table whole
  (the ⚠ on `imported`).
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
| ZF (3,616 named): 369 lowered, the set HEAD lowered | §0's complete run; its parts' `claim`/`schema` names diffed against HEAD's run |
| the unit: 7,969 claims, 568 schemas, 206,264,082 bytes, byte-identical to the run before the memo | §0's complete run; the parts' bytes compared |
| the complete run fits the CI's 32 GB: peak 25.5 GB (HEAD 45.8 GB under `MEM=80G`) | §0's run under `/usr/bin/time -v` |
| Logic 417.6 s against HEAD's 321–337 s; Expand 6.6 s against 3.8–4.1 s | §0's stage line |
| `infinity` and `λx. x = x` refused unbuilt | the two failing tests of §0 |
| comments 275/17070 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 597 lemmas refused unbuilt, and what leads the 3,239 citers: not traced.
- Logic's quarter over HEAD is a layer's lookup below it and the import's hashing: from a profile taken before the
  import carried sorts.
- The 25.5 GB peak is a spike between 20-second samples (sampled at most 22.7 GB); where it falls is not traced.

## 6. Open decisions
- **The next blocker**: the 597 lemmas unbuilt behind `Arith.natify_non_succ`, the `ZF_Base` boxes, `FOL.IFOL_simps.32`.
- **Speed**: Logic a quarter over the run before the steps; the registry and Fol carry 3,000 more theorems' lemmas, none
  kept.

## 7. Next action
Trace the 597 lemmas refused unbuilt, and the 3,239 named refused for citing, down to their roots (user: "go ahead").
Done when each root is named with the theorems it blocks, for the user's choice of the next step.
