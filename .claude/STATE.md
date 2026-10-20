# STATE — isa2fol
HEAD "β at values: an application of the class variable meets its arguments' values" (parent "The class of a λ holding
a proposition: …") · primitives · 2026-10-20. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `β at values: …`, `The class of a λ holding a proposition: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `16865` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `37ae807` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT, the binary that checked §0's unit |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 132, 47 passed; Lowering 165 with 1 failing: `infinityReadsSuccByTheTheoremStatingItsMembers` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `classes` 66 of 66 and 1 schema of 1 (`row_letter`), `tuples` 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=64G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (42:49, peak 46.9 GB; killed at 26:22 under `MEM=32G`), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (10:53) | `lowered … 2220`; `refused, named: 1396`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 1388`, led by `Arith.natify_non_succ` 366; `lemmas … unbuilt: 1`; 71 parts, every one `exit 0  stderr 0`; claims 32732 of 32732, schemas 4544 of 4544; 2,999,413,673 bytes; stages `expand 6.7 s, logic 426.7 s, registry 709.3 s, fol 471.4 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb `37ae807`, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`)
is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "β at values": the root cause, decision 1, Built, the decisions made in the build, Measured — its ⚠ on
  the CI's 32 GB.
- `Sources/Lowering/Meeting.swift` — `Meet.applies`, `atValues` (which values it fixes at the atom), `crossed`,
  `betaCore`; `Atom.convert(_:to:…)`.
- `Sources/Lowering/Values.swift` — `fixing` and `existence(ofValue:)`, their `guardOf`.
- `Tests/LoweringTests/LambdaTests.swift` — the eight tests at a compound argument, the nested one last.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| β is at values: an atom applying the class variable crosses to its reduced form's value form, β there at variables, the target's names by the reduced atom's `MEET_<fp>`; it fixes the values only its conversion holds | `LambdaTests`: `anInstanceAtACompoundArgumentIsBetaAtItsValue`, `aSharedArgumentTheBodyNamesBelowAConnectiveIsBetaAtItsValue`, `aBodyNamingItsArgument…`, `aFunctionLambda…`, `anArgumentHoldingTheClassVariable…`, `anApplicationInASlotOfAnAtomApplyingTheClassVariableMeetsTheAtomsValues` |
| a letter is an atom of a class body, read by base's `row_letter`; a λ's class at a letter is a schema in it | `aLambdaHoldingALetterHasItsClassReadingTheLetterByItsRow`, `anInstanceAtALambdaHoldingALetterIsItsClassThenBeta` |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| a lemma two units request is one statement; each request remaps every ID it holds | `aLemmaTwoStatementsRequestInTheirLayersIsOneStatementOfTheUnit`, `eachRequestRemapsEveryIDItHolds` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **A VALUE AN ATOM'S PREMISE OR CONCLUSION HOLDS IS NEVER FIXED AGAIN INSIDE IT**: fixed twice, a hypothesis names
  the outer variable and the proof the inner one, and only the kernel sees it — the table checks no hypothesis against
  its binder.
- ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**: bound to a local, each import copied the unit's table whole.
- ⚠ **A PASS'S WALK IS BUILT ONCE A RUN**: built per statement, Expand unfolded every definition it owns per statement.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**.
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
| ZF (3,616 named): 2,220 lowered; the 1,900 of the step before all kept, each proof byte for byte; 320 added | §0's complete run; its parts' names, and each proof's bytes, diffed against the run before |
| the unit: 32,732 claims, 4,544 schemas, 71 parts, 3.00 GB, all Proved | §0's complete run and check |
| ⚠ the complete run does not fit the CI's 32 GB: killed at 26:22 under `MEM=32G`; peak 46.9 GB under `MEM=64G`, inside Fol | §0's runs under `/usr/bin/time -v`; RSS sampled every 15 s |
| the 320 added theorems' own proofs are 1,335 MB of the 2.89 GB of proofs; 13 write 20 MB or more, `OrderArith.sum_prod_distrib_ord_iso` 200 MB in 2.8M steps, mostly `cong_iff`, `cong_imp`, `iff_trans`, `cong_and`, `iff_reflection` instances and 33,791 `BETA`, 19,513 `CLASS` citations | the emitted parts, each proof's bytes and instructions counted |
| `infinity`'s lemma, the one refused unbuilt, at `Ball(Inf, λy. succ(y) ∈ Inf)`: the axiom reading unfolds a defined predicate only at variables, and `Inf` is a set constant | `infinityReadsSuccByTheTheoremStatingItsMembers` fails `not proved: .unbuilt`; `Sources/Lowering/Axioms.swift:214` |
| comments 274/16865 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 1,388 named theorems citing a refused statement wait on `infinity`'s lemma, 1,345 of them, and `AC.AC`, 44: the
  trace before this step (a throwaway dump, not kept) put 1,345 under `infinity`; the 320 this step added are, name for
  name, the 320 it put under β alone.
- The 13 largest proofs are Pure's equality at `o` walked (`iff_*`, `cong_*`) and an instance at a λ per rewrite, as
  `OrderArith.sum_prod_distrib_ord_iso`'s instructions show; whether each is linear in its Isabelle size is not measured.

## 6. Open decisions
- **Size and memory**: the 320 new theorems double the unit and take the run past 32 GB. The cause the counts point to
  is Pure's equality at `o`, its `iff_*` walks, which "Linear proof size" left for a step of its own.
- **`infinity`'s `Ball(Inf, …)`** (§4): its own step; 1,345 named wait on it (§5).
The order: `infinity` first adds up to 1,345 named theorems to a run already past the CI's 32 GB.

## 7. Next action
Get the user's choice among §6. Done when the user has chosen.
