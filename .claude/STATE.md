# STATE — isa2fol
HEAD "`infinity` read: a definition at its terms, by a proof's instance met to the statement's form" (parent "A step
written once a proof: …") · primitives · 2026-10-20. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `` `infinity` read: … ``, `A step written once a proof: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17440` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `37ae807` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT, the binary that checked §0's unit |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 165, 133, 51 passed — none failing |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `classes` 66 of 66 and 1 schema of 1 (`row_letter`), `tuples` 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=64G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (39:49, peak 45.0 GB; killed at 32:51 under `MEM=32G`), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (23:09) | `lowered … 3565`; `refused, named: 51`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 43`, led by `Zorn.AC_well_ord` 7; `lemmas … unbuilt: 0`; 97 parts, every one `exit 0  stderr 0`; claims 49510 of 49510, schemas 6202 of 6202; 4,492,822,269 bytes; `table: 150984076 nodes`; stages `expand 6.1 s, logic 346.5 s, registry 583.5 s, fol 1190.7 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb `37ae807`, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`)
is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "`infinity` read": the root cause, decision 1, Built, Measured — its ⚠ on the CI's 32 GB.
- `Sources/Lowering/Unfolding.swift` — `definition` (the instance a proof takes at a definition's terms, Logic's too)
  and `unfolding` (met to the statement's form, its values fixed).
- `Sources/Lowering/Axioms.swift` — `AxiomReading.unbuilt`, `hole`: the reading that cites `unfolding`.
- `DESIGN.md` "A step written once a proof": the writer (`Sharing`) and the table's index of IDs.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a defined predicate in an axiom is unfolded at its terms as a proof cites it — set terms at their values, λs at their classes — and met to the statement's form | `AxiomTests`, the six axioms, `infinityReadsSuccByTheTheoremStatingItsMembers` among them |
| a step is written once a proof: in the innermost block holding its uses; a node under keys that differ closed where that writes less | `ProofEmissionTests`, the four tests of "A step written once a proof"; `EmissionTests` |
| the table holds a node once; its index node IDs | `everyNodeIsFoundAgainAcrossTheIndexsGrowth` |
| β is at values: an atom applying the class variable crosses to its reduced form's value form | `LambdaTests`, the eight tests at a compound argument |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **AN INSTANCE AT A SET TERM IN STATEMENT FORM IS A PROOF'S INSTANCE MET BACK**: there is no statement-form instance
  at a term; a reading with its own, as `infinity`'s had, refuses every argument that is no variable.
- ⚠ **THE SURVEY IS A CLASS**: a struct copied while the writer interns into it copies its dictionaries at each binder.
  ⚠ **`Sharing.premises` IS `render`'s CITATIONS**; ⚠ **A CLOSURE IS COUNTED IN TEXT, NOT LINES**.
- ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**: as a dictionary's key, each node was held twice, 46.9 GB at the doubling.
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
| ZF (3,616 named): 3,565 lowered — the 2,220 of the step before, name for name, and 1,345 added, `ZF_Base.infinity` and `Nat.nat_bnd_mono` among them | §0's complete run; its parts' names diffed against the run before |
| refused, named: 51 — 7 at a type variable no class restricts (no owner), `AC.AC`, and 43 citing `AC.AC`'s chain | §0's complete run |
| the unit: 49,510 claims, 6,202 schemas, 97 parts, 4.49 GB, all Proved; the 1,345 theorems' own proofs 2,815 MB, `Bin.integ_of_add` 99.3 MB the largest | §0's complete run and check; each proof's bytes |
| ⚠ the complete run does not fit the CI's 32 GB: killed at 32:51 under `MEM=32G`; peak 45.0 GB under `MEM=64G`, at emission; 27.0 GB at 1,186 s inside Fol, from 10.7 GB at 1,066 s | §0's runs under `/usr/bin/time -v`; RSS sampled every 15 s |
| comments 291/17440 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Against Isabelle's size (throwaway traces, recorded in `DESIGN.md` "`infinity` read", Measured): exponent 1.10
  against its DAG over 4,226 statements; the 1,345 added write 1,054 bytes an Isabelle step against the 2,220's 318 —
  Logic's growth per Isabelle step, 3–17 distinct steps after Fol where measured, is what is left above linear.
- The jump inside Fol, 10.7 → 27.0 GB in two minutes, is the table's arrays doubling past 2^27 nodes (the run ends at
  151M): consistent with the samples, not measured as such; the peak at emission, the unit's 4.49 GB of text held.

## 6. Open decisions
- **Memory, the CI's 32 GB** (§4): the table's arrays past 2^27 nodes, and emission holding the unit's text.
- **Logic's growth per Isabelle step** (§5): the 1,345 cost three times the 2,220's per step.
- **`AC.AC`**: Choice, FOUNDATION §1's axiom 19, unpinned; 44 named wait on it. **The 7 at a type variable no class
  restricts**.

## 7. Next action
Get the user's choice among §6 — memory, to bring the complete run under the CI's 32 GB again, is the one recommended
first. Done when the user has chosen.
