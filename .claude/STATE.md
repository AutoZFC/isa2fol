# STATE — isa2fol
HEAD "A step written once a proof: closed over the binders its uses differ in; the table's index holds IDs" (parent "β at
values: …") · primitives · 2026-10-20. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `A step written once a proof: …`, `β at values: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17478` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `37ae807` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT, the binary that checked §0's unit |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 133, 51 passed; Lowering 165 with 1 failing: `infinityReadsSuccByTheTheoremStatingItsMembers` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `classes` 66 of 66 and 1 schema of 1 (`row_letter`), `tuples` 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (24:01, peak 17.9 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (4:28) | `lowered … 2220`; `refused, named: 1396`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 1388`, led by `Arith.natify_non_succ` 366; `lemmas … unbuilt: 1`; 48 parts, every one `exit 0  stderr 0`; claims 32732 of 32732, schemas 4544 of 4544; 1,292,735,372 bytes; `theorem: 2870, 9386476, 61646659, 7372065`; stages `expand 5.7 s, logic 344.4 s, registry 574.4 s, fol 395.1 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb `37ae807`, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`)
is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A step written once a proof": the measurement (the text was Isabelle's proof tree; the index doubling),
  decisions 1 and 2, Built, the decisions made in the build, Measured.
- `Sources/FolDialect/Sharing.swift` — the survey: `premises` (the steps each rule cites, as `render` writes them),
  keys and their placement (`lca`), `closure` and its byte estimate (`weight`, `formulaBytes`), `hypothesis`.
- `Sources/FolDialect/Render.swift` — `Writer.step` (by key, at its placement), `at`, `opening`, `closure`,
  `instantiated`, `text` (numbered in reading order).
- `Sources/IR/Table.swift` — `own`, `added`, `place`: the index of IDs.
- `Tests/FolDialectTests/ProofEmissionTests.swift` — the four tests of the step and the three proofs it adds to
  `theRealCheckerProvesWhatEmissionWrites`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a step is written once a proof: placed in the innermost block holding its uses; a node under keys that differ closed over the binders they differ in where that writes less; a one-line step stays at each use | `ProofEmissionTests`: `aStepMetAlikeInTwoSiblingBlocksIsWrittenOnceAboveThem`, `aStepUnderEachBranchsHypothesisIsWrittenOnceClosedOverIt`, `aStepUnderTwoFixedVariablesIsClosedOverTheVariable`, `aOneLineStepUnderTwoHypothesesIsWrittenAtEach`; `EmissionTests`: `aClosedCitationInTwoSiblingScopesIsWrittenOnceAboveThem`, `aStepUnderTwoClosingBlocksIsWrittenOnceBeforeThem` |
| the table holds a node once; its index node IDs | `everyNodeIsFoundAgainAcrossTheIndexsGrowth` |
| β is at values: an atom applying the class variable crosses to its reduced form's value form; it fixes the values only its conversion holds | `LambdaTests`, the eight tests at a compound argument |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| a proof's formulas hold values, linear in Isabelle's steps | `ProofSizeTests` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **THE SURVEY IS A CLASS**: a struct, copied by the writer while it interns occurrences, copies its dictionaries at
  each new binder. ⚠ **`Sharing.premises` IS `render`'s CITATIONS**: a step the writer cites that the survey did not
  walk is `RenderError.unsurveyed`.
- ⚠ **A CLOSURE IS COUNTED IN TEXT, NOT LINES**: counted in lines, closures restating a 2 KB hypothesis to save a dozen
  lines grew 82 `BETA_<fp>` proofs.
- ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**: as a dictionary's key, each node was held twice and the doubling past
  100.6M nodes took the run to 46.9 GB.
- ⚠ **A VALUE AN ATOM'S PREMISE OR CONCLUSION HOLDS IS NEVER FIXED AGAIN INSIDE IT**: only the kernel sees it.
- ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**; ⚠ **A PASS'S WALK IS BUILT ONCE A RUN**.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL.**
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it; ⚠ **A LINE
  THAT OPENS OR CLOSES A BLOCK IS NEVER SHARED**.
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: find a run by `ps`, kill by PID; ⚠ **A VARIABLE SET IN A
  BACKGROUNDED `&&` CHAIN IS NOT SET AFTER IT**.
- ⚠ **`t[try instantiate(…)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13); ⚠ **A STEP-COUNT ESTIMATE IS NOT A
  MEASUREMENT**; ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file);
  ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 2,220 lowered, the named set of the step before name for name | §0's complete run; its parts' names diffed against the run before |
| the unit: 32,732 claims, 4,544 schemas, 48 parts, 1.29 GB, all Proved; its proofs 1.19 GB against 2.89 GB, none of 37,276 longer | §0's complete run and check; each proof's bytes against the run before |
| the complete run fits the CI's `MEM=32G`: 24:01, peak 17.9 GB, at emission; 15.6 GB at the highest inside Fol | §0's run under `/usr/bin/time -v`; RSS sampled every 15 s |
| the largest proofs: `OrderArith.sum_assoc_ord_iso` 23.3 MB, `sum_prod_distrib_ord_iso` 18.0 MB, from 183.6 and 200.2 | the emitted parts, each proof's bytes |
| `infinity`'s lemma, the one refused unbuilt, at `Ball(Inf, λy. succ(y) ∈ Inf)`: the axiom reading unfolds a defined predicate only at variables, and `Inf` is a set constant | `infinityReadsSuccByTheTheoremStatingItsMembers` fails `not proved: .unbuilt`; `Sources/Lowering/Axioms.swift:214` |
| comments 291/17478 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 1,388 named theorems citing a refused statement wait on `infinity`'s lemma, 1,345 of them, and `AC.AC`, 44: a
  trace before "β at values" (throwaway, not kept) put 1,345 under `infinity`.
- Against Isabelle's size (throwaway traces, recorded in `DESIGN.md` "A step written once a proof"): exponent 1.09
  against its DAG, 0.86 against its tree; Logic's own growth, 3–17 distinct steps after Fol per Isabelle step, is what
  is left above linear.

## 6. Open decisions
- **`infinity`'s `Ball(Inf, …)`** (§4): its own step; 1,345 named wait on it (§5).
- **Logic's growth per Isabelle step** (§5): the instances and walks each of Isabelle's steps lowers to.

## 7. Next action
Get the user's choice among §6: `infinity`'s lemma (1,345 named wait; the run has room, 17.9 of 32 GB) or Logic's growth
per Isabelle step. Done when the user has chosen.
