# STATE — isa2fol
HEAD "`combination` under a function of a function, read whole; a name segment that is no identifier quoted" (parent
"`AC.AC`: …") · primitives · 2026-10-21. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
The complete run is all eight sessions (user, 2026-10-21); `$ZF`, `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,
ZF-Induct,ZF-Resid,ZF-ex`, runs the ZF session alone, the baseline. Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `` `combination` under a function of a function, read whole; … ``, `` `AC.AC`: … `` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17673` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, quoted name segments read |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all: NBG with Regularity and Choice (Gödel's E), and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 175, 135, 52 passed — none failing |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (27:55, peak 17.4 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (23:31) | `lowered … 3609`; `refused, named: 7`, all `no owner`; `lemmas … unbuilt: 0`; 97 parts, every one `exit 0  stderr 0`; claims 50306 of 50306, schemas 6273 of 6273; `table: 152095892 nodes`; stages `expand 5.1 s, logic 309.8 s, registry 546.3 s, fol 580.7 s` |
| `MEM=16G … lower data/zf_export --theorem Satisfies_absolute.satisfies_MH_def,L_axioms.Triv_reflection --emit DIR --threads 8`, then `check-unit.sh DIR` | lowered 1 (`satisfies_MH_def`); `Triv_reflection` refused, `logic, unbuilt`, `Pure.eq` at `((i ⇒ o) ⇒ o) ⇒ o`; 10 parts, 997 claims and 448 schemas, all Proved |
| `MEM=16G /usr/bin/time -v … lower data/zf_export --through logic --theorem Datatype_absolute.Formula_Rec.MH_rel2` | `1 named theorems stand`; `table: 66325468 nodes`; logic 523 s; maximum resident 13.3 GB |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "`combination` under a function of a function, read whole": the two decisions, Built, the four decisions
  made in the build, Measured — its memory finding is the open question.
- `Sources/Lowering/Functions.swift` — `chain`: the walk over the head's body, holes filled at variables.
- `Sources/Lowering/Logic.swift` — `piece`'s `.pointwise(.chain)`, and `Steps.before` reading the chain at `o`.
- `Sources/Lowering/Values.swift` — `fixing` and `Rebind`: closed values bound at a proof's top as indices.
- `Sources/FolDialect/Render.swift` — `spelled`: a segment after the first that is no identifier, quoted.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms and nothing else | §0's `grep`; `check-base.sh` |
| `combination` at a type with an argument taking a function or a proposition is Logic's, read whole; `symmetric` and `transitive` there Expand's, `t ≡ t` only | `eachPatternHasTheOwnerTheDivisionGivesIt`; `atATypeTakingAFunctionCombinationIsLogicsAndSymmetryReflexivity` and its proposition twin; `aCombinationUnderAFunctionOfAFunctionOfClassesIsReadWhole` and `FunctionEqualityTests`' two others, kernel-checked |
| a name reaches the text unchanged; a segment after the first that is no identifier or is a keyword is written quoted | `RenderTests.aSegmentAfterTheFirstWithAnInnerPrimeIsQuoted`, `theRealCheckerAcceptsWhatRenderEmits` |
| a node is 16 bytes, a type one word: a wide kind behind a reference | `aNodeIsSixteenBytesAndATypeOneWord` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **A CHAIN'S LINK CANNOT WAIT, LOWERED BELOW, FOR ITS CONSUMER**: the table computes a node's conclusion from its
  children's, and a link kept over lowered children is no Pure equation (`principalConnective`).
- ⚠ **A NODE IS 16 BYTES**; ⚠ **A WALK'S CONTEXT IS NEVER COPIED INTO A KEY**; ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**.
- ⚠ **`t[try f(…, &t)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13): bind the interned node first.
- ⚠ **A PROVER WRITES AN ISA PROOF AND LETS LOGIC'S WALK LOWER IT**; ⚠ **A PROVER'S ERROR OTHER THAN
  `MeetingError.unmet` IS FATAL TO THE RUN**, and so is `FunctionsError.noReading`.
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it.
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: find a run by `ps`, kill by PID; ⚠ **A VARIABLE SET IN A
  BACKGROUNDED `&&` CHAIN IS NOT SET AFTER IT** — write the chain as a script.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file); ⚠ **THE RELEASE BINARY IS NOT
  REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 3,609 lowered, every claim and schema name `AC.AC`'s step's, part by part (56,579) | §0's complete run; its parts' names diffed against the run before |
| refused, named: 7 — a type no class restricts, the ceiling | §0's complete run; FOUNDATION §3b |
| ZF-Constructible through Logic, theory by theory: 15 of 18 finish and none stops on `noReading`; Datatype_absolute, DPow_absolute and Satisfies_absolute exceed 30 GB; standing per theory in `DESIGN.md` Measured | `--through logic --theorem` each theory's names, `MEM=12G` (30G for the five largest) |
| `satisfies_MH_def`, the unapplied definition's box, lowers and kernel-checks | §0's row |
| ZF-Constructible exceeds memory: `finished`'s closed values, bound at a proof's top as indices, copy every node holding one at each depth it is met — 97% of `DPow'_iff_sats`' 47.8M nodes | §0's `MH_rel2` row; `DESIGN.md` Measured, from a traced build never committed |
| comments 300/17673 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The six other sessions' 39.4 GB lowering (`--skip ZF-Constructible`, before this step) is the same copying.
- A value fixed at the top and referred to by its level — as the text names it — would be shared at every depth.

## 6. Open decisions
- **Memory before the all-eight complete run**: a value fixed at a proof's top is an index from each use, so its
  holders are copied per depth. The fix and its owner are the user's; until then no complete run of the other sessions
  fits.

## 7. Next action
Get the user's choice on §6. Done when the user has chosen.
