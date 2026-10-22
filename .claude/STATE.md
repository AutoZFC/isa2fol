# STATE — isa2fol
HEAD "A ZF proposition defined with no arguments, named as every defined predicate: ZF-AC whole" (parent "`combination`
under a function of a function, read whole; …") · primitives · 2026-10-21. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
Runs target one session at a time until it is translated (user): now ZF with ZF-AC, `$AC` =
`--skip ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`, ZF kept so its 3,609 stay the baseline. Lint
before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `A ZF proposition defined with no arguments, …`, `` `combination` under a function of a function, read whole; … `` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17673` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, quoted name segments read |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all: NBG with Regularity and Choice (Gödel's E), and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 178, 135, 52 passed — none failing |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $AC --emit DIR --threads 16` (30:57, peak 18.9 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (28:05) | `lowered … 4086`; `refused, named: 7`, all `no owner`; `lemmas … unbuilt: 0`; 117 parts, every one `exit 0  stderr 0`; claims 59979 of 59979, schemas 7019 of 7019; `table: 179234579 nodes`; stages `expand 5.5 s, logic 329.6 s, registry 657.1 s, fol 593.9 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A ZF proposition defined with no arguments": the two decisions, Built, Measured.
- `DESIGN.md` "`combination` under a function of a function, read whole", Measured: every session's count, and the
  value copying that keeps ZF-Constructible out of memory.
- `Sources/Lowering/Reify.swift` — `namesConstant`, `atom`, `atDefinition`: a constant named by its class, a value at
  `i` only.
- `Sources/Lowering/Values.swift` — `fixing` and `Rebind`: closed values bound at a proof's top as indices.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms and nothing else | §0's `grep`; `check-base.sh` |
| an object-level defined constant of no arguments is a value at `i` and a predicate at `o`, its class the class of its 0-tuples | `aPropositionOfNoArgumentsIsItsClassOfTheEmptyTuple`; `aPropositionOfNoArgumentsIsProvedThroughItsDefinition`, kernel-checked |
| `combination` at a type with an argument taking a function or a proposition is Logic's, read whole | `eachPatternHasTheOwnerTheDivisionGivesIt`; `FunctionEqualityTests`' three, kernel-checked |
| a name reaches the text unchanged; a segment after the first that is no identifier or is a keyword is written quoted | `aSegmentAfterTheFirstWithAnInnerPrimeIsQuoted`, `theRealCheckerAcceptsWhatRenderEmits` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. Per session: a theory's prefix names its session (`ZF-AC.…`; `ZF.…` and `Pure`,
  `IFOL`, `FOL` the ZF session's).
- ⚠ **A LEMMA IS WRITTEN IN ITS FIRST CITER'S PART IN EMISSION'S ORDER**: with ZF-AC in the run, 295 of ZF's lemmas
  sit in ZF-AC's `AC_Equiv` and `AC18_AC19` parts. Compare a session's lemmas across runs by name, never by part.
- ⚠ **A CHAIN'S LINK CANNOT WAIT, LOWERED BELOW, FOR ITS CONSUMER** (`principalConnective`).
- ⚠ **A NODE IS 16 BYTES**; ⚠ **A WALK'S CONTEXT IS NEVER COPIED INTO A KEY**; ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**.
- ⚠ **`t[try f(…, &t)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13): bind the interned node first.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**, and so is `FunctionsError.noReading`.
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: find a run by `ps`, kill by PID; ⚠ **A BACKGROUND COMMAND
  IS STOPPED AT ITS TIME LIMIT, ITS CHILDREN WITH IT**: launch a long run with `setsid nohup` and wait on its status.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file); ⚠ **THE RELEASE BINARY IS NOT
  REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF with ZF-AC: 4,086 of 4,093 lowered, ZF-AC 477 of 477; every claim and schema name of the ZF run before present | §0's complete run; names diffed against the ZF run before |
| refused, named: ZF's 7, a type no class restricts, the ceiling | §0's complete run; FOUNDATION §3b |
| every session but ZF-Constructible, before this step: 6,921 of 7,299, all Proved | `DESIGN.md` "`combination` …", Measured |
| ZF-Constructible exceeds memory: `finished`'s closed values, bound at a proof's top as indices, copy every node holding one at each depth it is met | `MEM=16G … --through logic --theorem Datatype_absolute.Formula_Rec.MH_rel2`: 13.3 GB, 66M nodes; `DESIGN.md` Measured |
| comments 300/17673 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- A value fixed at a proof's top and referred to by its level — as the text names it — would be shared at every depth.
- ZF-Resid's 6 refused lower now: 4 held this step's pattern (`Confluence.strip`) by the seven-session run's counts,
  85 named at it of which ZF-AC's 81; the other 2 believed to cite them. Not run since.

## 6. Open decisions
- **ZF-AC is translated whole**: the next target is the user's. Agreed order before it: constants with no definition
  and their theory axioms (ZF-IMP's `loc`, ZF-Coind's `Const`…, ZF-ex's `flip`), then ZF-Constructible, memory first.

## 7. Next action
Get the user's choice of the next target. Done when the user has chosen.
