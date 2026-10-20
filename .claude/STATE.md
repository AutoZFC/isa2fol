# STATE — isa2fol
HEAD "A variable only the proof uses, constant in its arguments: one variable per result type, i or o" (parent "A
record's facts at fewer steps: …") · primitives · 2026-10-19.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `A variable only the proof uses, constant in its arguments: …`, `A record's facts at fewer steps: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `16777` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 121, 47 passed; Lowering 153 with 2 failing: `infinityReadsSuccByTheTheoremStatingItsMembers`, `anInstanceAtACompoundArgumentIsBetaAtItsValue` |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `metafun` 18 of 18 |
| `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --theorem ZF.iterates_triv` | refused, citing `BETA_0e23d963c3fd01a7_2`, unbuilt |
| `MEM=80G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` | killed, still lowering, at 83.7 GB (20:05) |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream. The checker is fol-zfc-comb `224d60e`, built only with
`bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A variable only the proof uses, constant in its arguments": decisions 1–2, Built, the three decisions
  made in the build, Measured — the complete run killed at `MEM=80G`.
- `Sources/Reader/Terms.swift` — `hide` (one binder per result type, a dropped argument not scanned) and `.hidden` (an
  application read as the variable at its result type, its arity checked).
- `Sources/Lowering/Fol.swift` — `isaHidden(i)`, `exists_elim` over `set_inhabited`; `Logic.swift` — `isaHidden(o)`.
- `Sources/Lowering/Meeting.swift` — `betaAtom`'s check that both forms name a shared argument first, `constrained`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most; `isaHidden` at `i` and `o` alone | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a variable only the proof uses is constant in its arguments | `aVariableOnlyTheProofUsesIsConstantInItsArguments`, `aWitnessAppliedToTheStatementsClassAndLetterIsTheProofsVariableAtI` |
| a shared argument a λ's body names below a connective is unbuilt, never a malformed step | `aSharedArgumentTheBodyNamesBelowAConnectiveIsUnbuilt` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **THE COMPLETE RUN DOES NOT FIT `MEM=80G`**: every node a walk builds stays for the run.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**: a shape the β walk cannot align is refused
  unbuilt before the walk, never left to throw in it.
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL.**
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**; ⚠ **A LINE THAT OPENS OR CLOSES A BLOCK IS NEVER SHARED**.
- ⚠ **`t[try instantiate(…)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13); ⚠ **`pre-commit run --all-files`
  LINTS TRACKED FILES ONLY**; ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S
  COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| the complete run is killed at `MEM=80G`, 83.7 GB, still lowering: nothing emitted, the named theorems the step adds not counted | §0's last row |
| `infinity` and `λx. x = x` refused unbuilt | the two failing tests of §0 |
| comments 264/16777 = 1.6% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The peak is the table: every node a walk interns stays for the run, though its results reach a fraction.

## 6. Open decisions
- **Memory**: the complete run no longer fits 80 GB.

## 7. Next action
Write the memory step's section in `DESIGN.md` and agree it decision by decision before any code.
