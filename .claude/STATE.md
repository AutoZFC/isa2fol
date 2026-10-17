# STATE — isa2fol
HEAD "Letters first" (parent `f315a16d`) · primitives · 2026-10-17.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Letters first: a theorem closed over its propositions first, each citation instantiating them on its head` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `12176` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=24G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 138, 103, 113, 42 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `metafun` Proved 18 of 18 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (2:11, peak 6.7 GB) | `through logic: 2058 named theorems stand`; `no owner: 1301`; `logic, unbuilt: 257` |
| `MEM=56G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR` (11:38, peak 34.3 GB; the CI), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 14`; groups no owner, logic, cites a refused statement only; 17 parts; claims 6058 of 6058, schemas 104 of 104; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "The steps after class existence, in order" — steps 5–9, and the rule that the refusals order 5–8.
- `DESIGN.md` "Letters first", **Measured**, "What holds the 3,602 back" — each step's reach, followed to the roots.
- `DESIGN.md` §4.3b, "⚠ `Pure.dummy_pattern` IS NO CONSTANT" — step 7's piece, `isaFree(.hidden, T)`.
- `DESIGN.md` "OFCLASS — …", decision 3 — `FOL.meta_simps.1`, `(⋀x::'a. PROP P) ≡ PROP P`, stays `use(theorem, [i], o)`.
- `Sources/isa2fol/Lower.swift` — the report: `cites a refused statement` names ONE citation per theorem, the least.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a theorem's statement binds its propositions first; a citation instantiates them first | `aMetaLevelPropositionalVariableReadsAsAFormulaVariable`, `aCitationInstantiatesItsLettersFirst` |
| the letters-first form lowers kernel-checked; the off-spine form stays refused | `aLetterInstantiatedFirstLeavesTheInstanceNoLetterToWalk`, `aLetterTheCitedTheoremBindsAfterTheInstantiatedClassIsOffItsSpine` |
| Pure's equality between functions, its five rules, kernel-checked | `FunctionEqualityTests` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **THE REPORT'S `cites a refused statement` COUNTS ARE NOT WHAT A STEP FREES**: each theorem names its least refused
  citation only. Follow citations down to the statements refused at their own pieces before ordering steps.
- ⚠ **A DEFINIENS IS NEVER CLOSED LETTERS FIRST**: its λs are its constant's positional parameters. `Terms` takes the
  order explicitly; no default.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**: `git add` a new file first, or the commit hook reformats
  it and the commit fails.
- ⚠ **A FORMULA LOGIC REWRITES IS OWED A READING IN `Replacement`** (a stated `≡` at `i ⇒ i` stopped the ZF run).
- ⚠ **`s.variable(s.fix(.i))` AND `t[try s.hypothesis(…)]` READ A COPY TAKEN BEFORE THE MUTATION** (rule 13). Bind first.
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach.
- ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF**: one transform over every root passed 32 GB.
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Rules conclude `walked`, the walk's own rule.
- ⚠ **A BOX'S NAME MOVES WITH THE IR'S PRINTED PAYLOAD**: count boxes, never diff their names.
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**; a short Swift string is stored inline, so check a build by
  its timestamp, not `strings`.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 14 lowered; refused: no owner 1,301, logic 257, cites a refused statement 2,044; none at a letter off its spine | §0's complete run |
| the refused citations are led by `IFOL.exI` (374 citers) and `ZF_Base.Ball_def` (91) | the same report |
| no owner is led by `isaFree(i)` 731 (step 7), `use(theorem, [i], o)` 668, `isaDefinition(zf, object, [], args: [])` 210 (step 5) | §0's through-logic report |
| Logic's 257: `If` 245 (step 6), binders over a function of classes (step 9) | the same report |
| complete ZF run: read 44.9 s; expand 1.5, logic 80.7, registry 39.8, fol 356.4, link 26.5 s; emitted 144.2 s, 382 MB; 76.5M nodes | §0's complete run |
| comments 59/12176 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `DESIGN.md` "What holds the 3,602 back" — every figure from a throwaway dump, not kept; "alone" figures are upper bounds
  (a statement refused at its own pieces has its citations unread).
- `use(theorem, [i], o)` is `FOL.meta_simps.1` at `[i]` in all 675 statements holding it (the same dump).
- `SOURCE_SURFACE.md` and `CLOSURE.md` are unchanged by letters first (patterns are order-free); not regenerated.

## 6. Open decisions
- **The next step.** By the refusals: 7, the hidden variable (frees the most alone; its design is new), or 6, `If` and
  `bool_of_o` (needed by the most); 5, a ZF definition cited, is the plan's next number and third on both; beside 5–8,
  `FOL.meta_simps.1` at `[i]`, one theorem's instance, frees the most once 6 and 7 stand.
- For review: "Letters first"'s two build decisions; "Step 4"'s four; merging the checker branch.

## 7. Next action
Get the user's choice of the next step; then write its section in `DESIGN.md` — the problem in target text, its
decisions, the contracts, the tests first — and agree it decision by decision before any code. Done when the user has
agreed every decision of that section.
