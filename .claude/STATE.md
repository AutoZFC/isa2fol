# STATE — isa2fol
HEAD "A value fixed at a proof's top, named by itself: ZF-Constructible's memory" (parent "A theory's own parameter,
a variable of what reaches it: …") · primitives · 2026-10-22. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
Runs target one session at a time until it is translated (user): ZF, ZF-AC, then ZF-IMP with ZF-Coind and ZF-ex, all
done; ZF-Constructible now, its memory done; what comes next is the user's. `$T` = `--skip
ZF-AC,ZF-Coind,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`. Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `A value fixed at a proof's top, named by itself: …`, `A theory's own parameter, a variable of what reaches it: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `18237` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, quoted name segments read |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 152, 179, 138, 53 passed — none failing |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export $T --emit DIR --threads 16` (1:17:09, peak 42.6 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (2:12:20, peak 9.0 GB) | `lowered … 5291`; `refused, named: 446` — `no owner: 17`, `logic, unbuilt: 42`, `cites a refused statement: 387`; `@defs stated: 549, refused: 0`; `unbuilt: 0`; `table: 273459592 nodes`; 378 parts, 20262772295 bytes, every one `exit 0  stderr 0`; claims 87402 of 87402, schemas 12665 of 12665 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A value fixed at a proof's top, named by itself": decisions 1–5, Built, the build's decisions, Measured.
- `Sources/Lowering/Values.swift` — `naming` (the closed values fixed at the top by `valueElim`), `fixing` (the rest).
- `Sources/IR/Traversal.swift` — `visit`: explicit frames, `@inlinable`.
- `Sources/IR/Table.swift` — `valueElim`'s refusals (`witnessEscapes`); `Sources/IR/Node.swift` `forEachHeldChild`.
- `Sources/FolDialect/Emit.swift` — `concurrently`: every statement rendered before one is written (decision 5).

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms; a theory's own axiom is a premise | §0's `grep`; `aConstantATheoryNeverDefinesIsAVariableAndItsAxiomAPremise` |
| a closed value fixed at a statement's proof's top is one node at every depth, its binder naming it | `aClosedValueIsOneNodeAtEveryDepthItsBinderNamingIt`, `aValueFixedAtTheTopIsNamedByItsBinder` |
| a value's binder concludes its body's conclusion, never a formula holding the value | `aValuesBinderConcludesItsBodysConclusionAndRefusesItsEscape` |
| a walk goes as deep as its unit | `aWalkGoesAsDeepAsItsUnit` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A VALUE'S TERM IS ITS IDENTITY, NEVER A TERM ITS PROOF HOLDS**: no scan reads it (`Node.forEachHeldChild`);
  scanned, `Pow(0)`'s `isaConst` survived Logic. Pinned by `aValueItsHypothesisAndItsBinderAreFolZfcsTheValuesTermUnread`.
- ⚠ **A WALK HOLDS ITS PATH ON THE HEAP AND IS COMPILED PER RULE** (`visit`): recursive, it overflowed the main
  thread's 8 MB at 7,440 levels; not inlinable, Logic took 14% longer.
- ⚠ **EMISSION HOLDS THE UNIT'S TEXT WHOLE**: 19.71 GB for the target, so its complete run needs `MEM=48G`.
- ⚠ **`AC.AC` IS THE DIALECT'S AXIOM, STATED ABOVE THE FOUNDATION**: never a theory's own axiom
  (`isTheorysOwnAxiom`); a complete run's steps must list `axiom AC.AC`.
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
| ZF-Constructible 1,682 of 2,121 lower and kernel-check, 9 of its 18 theories whole; ZF 3,609 of 3,616 | §0's complete run, counted per theory against each theory's `thms` |
| every claim and schema name of the ZF session's own run is in the target's unit | names diffed against that run's: 0 missing |
| the complete run peaks at 42.6 GB, at emission | §0's complete run, `/usr/bin/time -v` |
| no owner, 17: ZF's 7, the ceiling; 7 stated at a type no class restricts (`MetaExists`' 3, …); 3 at Isabelle's `dummy` type | §0's log; `--through expand --theorem` on the refused, patterns `ifolAll(dummy, …)`, `use(theorem, [dummy], o)` |
| Logic, unbuilt, 42: a variable taking a class, `(i ⇒ o) ⇒ i ⇒ … ⇒ o`, and Pure's equality at `((i ⇒ o) ⇒ o) ⇒ o` | §0's log, `logic, unbuilt` patterns |
| comments 312/18237 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Most of the 387 refused citing a refused statement rest on the 42 at a variable taking a class: not traced.
- Emission writing each statement once those before it are written would hold at most `threads` texts, the target
  under 32 GB (DESIGN decision 5, "Not built").
- The locale theorems' size (116 statements of 50 MB or more, 10.72 GB of the 19.71) has a cause in their proofs, not
  measured.
- ZF-Resid's 6 and ZF-Induct's 2 refused in the seven sessions' run lower now; not run since three steps.
- `docs/SOURCE_SURFACE.md` and `docs/CLOSURE.md` are older than several reader steps (last generated 2026-10-16).

## 6. Open decisions
- None. Next (user, 2026-10-22: "a"): ZF-Constructible's 439 refused, its four decisions agreed one by one — 1 Pure's
  equality at a type with an argument taking a function or a proposition, its two sides one term, read as true; 2 a
  variable taking a class to a proposition a schema letter of its arity; 3 that letter's lift a premise of every
  statement closed over it; 4 the type only a proof uses, `dummy`, read at `i`. Emission's memory and the locale
  theorems' size wait.

## 7. Next action
Write FOUNDATION, then DESIGN for the four decisions; tests first; build. Done when the complete run lowers and
kernel-checks ZF-Constructible but its 7 stated at a type no class restricts, ZF's 3,609 kept, every part exit 0 with
empty stderr, every claim and schema Proved, under `MEM=48G`.
