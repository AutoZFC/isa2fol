# STATE — isa2fol
HEAD "Memory under the CI's 32 GB: Fol's context held by reference; a node at the width of its common kinds" (parent
"`infinity` read: …") · primitives · 2026-10-20. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `Memory under the CI's 32 GB: …`, `` `infinity` read: … `` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17501` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, the binary that checked §0's unit; `7405a6f` renames a section header |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 169, 134, 51 passed — none failing |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `classes` 66 of 66 and 1 schema of 1 (`row_letter`), `tuples` 27 of 27, `zf` 22 of 22 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (26:04, peak 17.4 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (23:09) | `lowered … 3565`; `refused, named: 51`: no owner 7, `logic, unbuilt: 1` (`AC.AC`), `cites a refused statement: 43`, led by `Zorn.AC_well_ord` 7; `lemmas … unbuilt: 0`; 97 parts, every one `exit 0  stderr 0`; claims 49510 of 49510, schemas 6202 of 6202; 4,492,822,269 bytes; `table: 150984076 nodes`; stages `expand 4.8 s, logic 286.9 s, registry 493.9 s, fol 539.1 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Memory under the CI's 32 GB": the three costs measured, the two root causes, Built, Measured.
- `Sources/Lowering/Fol.swift` — `FolRule.Context`: a reference into the walk's chain of binders, never a copy.
- `Sources/IR/Node.swift` — the twelve kinds held behind a reference (`indirect`); `Sources/IR/IRType.swift`.
- `DESIGN.md` "`infinity` read": the step before, its Measured.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| a node is 16 bytes, a type one word: a wide kind behind a reference | `aNodeIsSixteenBytesAndATypeOneWord` |
| Fol's context is a reference into the walk's chain of binders; a formula's is the empty one | `FolContextTests` (four) |
| a defined predicate in an axiom is unfolded at its terms as a proof cites it and met to the statement's form | `AxiomTests`, the six axioms |
| the table holds a node once; its index node IDs | `everyNodeIsFoundAgainAcrossTheIndexsGrowth` |
| a unit of work's scratch leaves with its layer; the unit's table takes what results and kept forms reach | `aPassesScratchLeavesWithItsLayer`, `anImportAddsExactlyTheNewNodesItsResultsReach` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **A NODE IS 16 BYTES**: a kind wider than three children and a type goes behind `indirect`, or every node pays
  for it (80 bytes, 20.3 GB at 151M nodes). ⚠ **A WALK'S CONTEXT IS NEVER COPIED INTO A KEY**: Fol's keys held 9 GB
  in one walk, and the heap kept it.
- ⚠ **AN INSTANCE AT A SET TERM IN STATEMENT FORM IS A PROOF'S INSTANCE MET BACK**: there is no statement-form instance
  at a term.
- ⚠ **THE SURVEY IS A CLASS**; ⚠ **`Sharing.premises` IS `render`'s CITATIONS**; ⚠ **A CLOSURE IS COUNTED IN TEXT**.
- ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**; ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**; ⚠ **A PASS'S WALK
  IS BUILT ONCE A RUN**.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL.**
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it.
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: find a run by `ps`, kill by PID; ⚠ **A VARIABLE SET IN A
  BACKGROUNDED `&&` CHAIN IS NOT SET AFTER IT** — write the chain as a script.
- ⚠ **`t[try f(…, &t)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13); ⚠ **`pre-commit run --all-files` LINTS
  TRACKED FILES ONLY** (`git add -N` a new file); ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**;
  ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 3,565 lowered, the unit the step before's byte for byte, all 195 files | §0's complete run; its files compared with the run before |
| refused, named: 51 — 7 at a type no class restricts (no owner), `AC.AC`, and 43 citing `AC.AC`'s chain | §0's complete run |
| the complete run fits the CI's `MEM=32G`: 26:04, peak 17.4 GB at emission; lowering under 8.0 GB | §0's run under `/usr/bin/time -v`, RSS sampled every 15 s |
| comments 293/17501 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Against Isabelle's size (throwaway traces, `DESIGN.md` "`infinity` read", Measured): exponent 1.10 against its DAG
  over 4,226 statements; Logic's growth per Isabelle step is what is left above linear.
- Emission adds about 9 GB over lowering: every proof's text held until the last is rendered (4.31 GB) and sixteen
  threads' working memory — the probe's split, not measured since.

## 6. Open decisions
- **`AC.AC`**: Choice, FOUNDATION §1's axiom 19, unpinned; 44 named wait on it.
- **The 7 at a type no class restricts**: no fol-zfc statement of their own.
- **Logic's growth per Isabelle step** (§5); **emission's memory** (§5).

## 7. Next action
Design `AC.AC` in `DESIGN.md` — axiom 19 pinned in FOUNDATION first — and the 7, each agreed with the user decision by
decision, then build. Done when the user has agreed the design.
