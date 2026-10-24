# STATE — isa2fol
HEAD "ZF-Constructible's reflection: …" (parent "A value fixed at a proof's top, named by itself: …") · main ·
2026-10-24. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
The goal is the translated proofs (user, 2026-10-24): every session's from one build, each checked unit kept in
`~/isa2fol-units/`, its `README.md` a row per unit. Runs target one session at a time until it is translated (user):
ZF, ZF-AC, ZF-IMP with ZF-Coind and ZF-ex, ZF-Constructible, then the rest on the same build, all done but the
ceiling; what comes next is the user's. `$T` = `--skip ZF-AC,ZF-Coind,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`, `$O` = `--skip
ZF-Constructible`. Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `main` |
| `git log -2 --format=%s` | `ZF-Constructible's reflection: …`, `A value fixed at a proof's top, named by itself: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref main@{upstream}` | `origin/main` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `19563` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, quoted name segments read |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 153, 185, 138, 54 passed — none failing |
| `swift build -c release`, then `MEM=64G scripts/capped.sh .build/release/isa2fol lower data/zf_export $T --emit DIR --threads 16` (2:08:26, peak 57.2 GB; under `MEM=48G` killed in emission), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (3:52:32, peak 9.3 GB) | `lowered … 5723`; `refused, named: 14` — `no owner: 14`; `@defs stated: 549, refused: 0`; `unbuilt: 0`; `table: 410225522 nodes`; 544 parts, 29483070538 bytes, every one `exit 0  stderr 0`; claims 104949 of 104949, schemas 14283 of 14283 |
| the same with `$O` (59:14, peak 23.4 GB), then its check (35:48, peak 2.4 GB) | `lowered … 7290`; `refused, named: 9` — `no owner: 9`; `table: 291061745 nodes`; 146 parts, 5871412694 bytes, every one `exit 0  stderr 0`; claims 106690 of 106690, schemas 12120 of 12120 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `main`, upstream `origin/main` (`git@github.com:AutoZFC/isa2fol.git`), the
default branch; `backup/main-2026-03-27` (`d5dc4c8f`) is the March Rust and Bazel line, on no other branch.
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE. The checked units are in `~/isa2fol-units/` — the two of this build `2026-10-23_ZF-Constructible` and
`2026-10-24_all-but-ZF-Constructible`.

## 2. Read these first-hand
- `DESIGN.md` "ZF-Constructible's reflection": decisions 1–4, the citation at a λ, Built's decisions, Measured.
- `Sources/Lowering/Letters.swift` — `letterLift`, `letterDefinition`, `LetterInstantiation` (`BETA_<fp>_L`),
  `LetterFact` (`LIFT ⟨λ⟩`).
- `Sources/FolDialect/Emit.swift` — `concurrently`: every statement rendered before one is written, the cap's overrun.
- `~/isa2fol-units/README.md` — what each kept unit holds, and from which build.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms; a theory's own axiom is a premise | §0's `grep`; `aConstantATheoryNeverDefinesIsAVariableAndItsAxiomAPremise` |
| a variable taking a class is a letter, its lift a premise, discharged by `LIFT ⟨λ⟩` or the citer's own premise | `aVariableTakingAClassIsALetterItsLiftAPremise`, `aLetterCitedAtALambdaIsDischargedByTheLambdasLift`, `aLetterCitedAtTheCitersOwnLetterIsDischargedByItsPremise` |
| a citation at a λ holding the citer's letter is met by its `BETA_<fp>_L` | `aLetterCitedAtALambdaHoldingTheCitersLetterIsMetByItsBeta` |
| a closed value fixed at a statement's proof's top is one node at every depth, its binder naming it | `aClosedValueIsOneNodeAtEveryDepthItsBinderNamingIt`, `aValueFixedAtTheTopIsNamedByItsBinder` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A CHECKED UNIT IS KEPT IN `~/isa2fol-units/`, NEVER ONLY IN A SCRATCHPAD**: `/tmp` is emptied at every boot
  (`/usr/lib/tmpfiles.d/tmp.conf`); `check-unit.sh` rewrites a unit's `base/` and each `.fol.lib`.
- ⚠ **EMISSION HOLDS THE UNIT'S TEXT WHOLE**: 29.5 GB for the target, each box written in every proof citing it, so
  its complete run peaks at 57.2 GB, over the CI's `MEM=48G`.
- ⚠ **TWO UNITS OF ONE BUILD DIFFER BY PART, NEVER BY STATEMENT**: each holds the theorems outside the ZF sessions its
  sessions cite, a lemma in its first citer's part; compare by name, never by file.
- ⚠ **A VALUE'S TERM IS ITS IDENTITY, NEVER A TERM ITS PROOF HOLDS**: no scan reads it (`Node.forEachHeldChild`).
- ⚠ **A WALK HOLDS ITS PATH ON THE HEAP AND IS COMPILED PER RULE** (`visit`): recursive, it overflowed the main
  thread's 8 MB at 7,440 levels; not inlinable, Logic took 14% longer.
- ⚠ **`AC.AC` IS THE DIALECT'S AXIOM, STATED ABOVE THE FOUNDATION**: never a theory's own axiom
  (`isTheorysOwnAxiom`); a complete run's steps must list `axiom AC.AC`.
- ⚠ **THE EXPORT'S READER TEST LOADS EVERY PROOF**: 571 s in a debug build; scale-gated, `ISA2FOL_SCALE=1`.
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems.
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
| ZF-Constructible 2,114 of 2,121 lower and kernel-check, ZF 3,609 of 3,616, the missing exactly the ceiling | §0's `$T` run, counted by name against each theory's `thms` |
| every other session, same binary: ZF-AC, ZF-Coind, ZF-IMP, ZF-Resid, ZF-ex whole; ZF-Induct 1,494 of 1,496 | §0's `$O` run, by name |
| the ceiling is 16, each stated at a type no class restricts: ZF 7, ZF-Constructible 7, ZF-Induct's `Ntree.maptree_induct`, `maptree2_induct` | §0's logs, `no owner`; `--through expand --theorem`, patterns at `'a` |
| the two units are one translation: every statement (57,151) and proof (56,910) both hold is byte-identical | both units' parts hashed by name |
| per named theorem, our proof is at most 4.5× Isabelle's own with the boxes it reaches; ZF-Constructible's 26.45 GB is each box inlined in every citer | DESIGN Measured: `proof NAME:` spans against the export's proof files and their boxes |
| comments 366/19563 = 1.9% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Every box a statement of the unit would bring ZF-Constructible's 26.45 GB toward the export's scale and the target
  under 48 GB: not built, not measured.
- Emission writing each statement once those before it are written would hold at most `threads` texts: not built.
- All eight sessions as one unit would peak near 70 GB: never run.
- `docs/SOURCE_SURFACE.md` and `docs/CLOSURE.md` are older than several reader steps (last generated 2026-10-16).

## 6. Open decisions
- Emission over the CI's 48 GB (asked 2026-10-23, unanswered): every box a statement of the unit, at the cause, or
  emission bounded, decision 5's "Not built". The user then set the goal as the translated proofs (2026-10-24).
- What comes next: that, the ceiling (16), `CLASS ⟨λ⟩`'s growth as about the power 1.5, or ZF-UNITY, which the export
  lacks — the user's.

## 7. Next action
Ask the user which of §6 comes next. Done when they choose; any run of it keeps its checked unit in `~/isa2fol-units/`.
