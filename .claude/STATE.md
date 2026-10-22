# STATE — isa2fol
HEAD "A theory's own parameter, a variable of what reaches it: ZF-IMP, ZF-Coind and ZF-ex whole" (parent "A ZF
proposition defined with no arguments, …") · primitives · 2026-10-22. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
Runs target one session at a time until it is translated (user): ZF, ZF-AC, then ZF-IMP with ZF-Coind and ZF-ex, all
done; the next target is the user's. `$T` = `--skip ZF-AC,ZF-Constructible,ZF-Induct,ZF-Resid`. Lint before every run:
`pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `A theory's own parameter, a variable of what reaches it: …`, `A ZF proposition defined with no arguments, …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `18047` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, quoted name segments read |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 152, 178, 135, 52 passed — none failing |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $T --emit DIR --threads 16` (49:42, peak 26.8 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (39:04) | `lowered … 4979`; `refused, named: 7`, all `no owner`; `@defs stated: 422, refused: 0`; `unbuilt: 0`; steps list `axiom AC.AC`; 136 parts, every one `exit 0  stderr 0`; claims 72408 of 72408, schemas 8262 of 8262; `table: 270012521 nodes` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A theory's own parameter, a variable of what reaches it": decisions 1–4, Built, Measured.
- `Sources/Reader/Parameters.swift` — `Reaches` (decision 4's closure), `isTheorysOwnAxiom`, `ParameterContext`.
- `Sources/Reader/Reader.swift` — `prove`, `stating`, `step`'s citation, `premise`, `premises(_:at:)`.
- `Sources/Reader/Terms.swift` — the closure: letters, parameters, other frees; `close(_:_:premising:_:in:)`.
- `docs/FOUNDATION.md` §2, "A theory's own parameter is a variable of what reaches it".

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms; a theory's own axiom is a premise | §0's `grep`; `aConstantATheoryNeverDefinesIsAVariableAndItsAxiomAPremise` |
| a parameter stands after a statement's letters, before its own variables, its premises between | `theParametersAndPremisesStandInFrontOfTheStatementsOwnVariables` |
| a citation takes the citer's parameters and hypotheses, then Isabelle's arguments, as many as it gives | `aCitationTakesTheCitersOwnParametersAndHypothesesThenIsabellesArguments`, `aCitationGivingFewerArgumentsThanItsTheoremsVariablesReadsAsIsabellesDoes` |
| the IR has no declared constant and no theory axiom | `Constant`, `Cited` (`Sources/IR/Constant.swift`) |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **`AC.AC` IS THE DIALECT'S AXIOM, STATED ABOVE THE FOUNDATION** (`ZF.AC`): never a theory's own axiom
  (`isTheorysOwnAxiom`); taken for one, every theorem resting on choice carried it as a premise and the unit held no
  `AC.AC_AXIOM`. A complete run's steps must list `axiom AC.AC`. Pinned by `anAxiomOfTheDialectAboveTheFoundationIsCitedNeverAPremise`.
- ⚠ **THE EXPORT'S READER TEST LOADS EVERY PROOF**: 571 s in a debug build; scale-gated, `ISA2FOL_SCALE=1`.
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems.
- ⚠ **A LEMMA IS WRITTEN IN ITS FIRST CITER'S PART IN EMISSION'S ORDER**: compare lemmas across runs by name, never by part.
- ⚠ **A CHAIN'S LINK CANNOT WAIT, LOWERED BELOW, FOR ITS CONSUMER** (`principalConnective`).
- ⚠ **A NODE IS 16 BYTES**; ⚠ **A WALK'S CONTEXT IS NEVER COPIED INTO A KEY**; ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**.
- ⚠ **`t[try f(…, &t)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13): bind the interned node first.
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: kill by PID; ⚠ **A BACKGROUND COMMAND IS STOPPED AT ITS
  TIME LIMIT, ITS CHILDREN WITH IT**: launch a long run with `setsid nohup` and wait on its status.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file); ⚠ **THE RELEASE BINARY IS NOT
  REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF-IMP 284 of 284, ZF-Coind 288 of 288, ZF-ex 798 of 798 lower and kernel-check; ZF 3,609 of 3,616 | §0's complete run, counted per session against each theory's `thms` |
| every claim and schema name of the ZF session's own run is in the target's unit | names diffed against that run's: 0 missing |
| the complete run peaks at 26.8 GB of the CI's 32, at emission | §0's complete run, `/usr/bin/time -v` |
| refused, named: ZF's 7, a type no class restricts, the ceiling | §0's complete run; FOUNDATION §3b |
| comments 302/18047 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- A value fixed at a proof's top and referred to by its level — as the text names it — would be shared at every depth
  (ZF-Constructible's memory).
- ZF-Resid's 6 and ZF-Induct's 2 refused in the seven sessions' run lower now; not run since the last two steps.
- `docs/SOURCE_SURFACE.md` and `docs/CLOSURE.md` are older than several reader steps (last generated 2026-10-16).

## 6. Open decisions
- **The next target is the user's.** Agreed order: ZF-Constructible, its memory first (the values a proof fixes at
  its top, copied at every depth).

## 7. Next action
Get the user's choice of the next target. Done when the user has chosen.
