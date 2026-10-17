# STATE — isa2fol
HEAD "Step 7 and an ∃-intro carrying its body" (parent `267988c2`) · primitives · 2026-10-17.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Step 7 and an ∃-intro carrying its body: the hidden variable bound at its proof's top, exI read as its step` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `12438` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 138, 107, 115, 42 tests |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `logic` Schemas proved 10 of 10; `metafun` Proved 19 of 19 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (3:07) | `through logic: 2347 named theorems stand`; `no owner: 950`; `logic, unbuilt: 319` |
| `MEM=64G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 48` (20:33, ≥ 55.5 GB; the CI), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (1:50) | `lowered … 14`; `cites a refused statement: 2333`, led by `ZF_Base.Ball_def` 363; 24 parts; claims 8710 of 8710, schemas 104 of 104; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "The steps after class existence, in order" — steps 5, 6, 8, 9 remain; the refusals order them.
- `DESIGN.md` "An ∃-intro carrying its body", **Measured** — where the statements `exI` held now fall, and why the unit
  doubled.
- `DESIGN.md` "Step 7" and "An ∃-intro carrying its body", **Decisions made in the build** — for the user's review.
- `Sources/Lowering/Scope.swift` `closing`, `introduced` — every isa ∃-intro reads its body off the formula it proves.
- `Sources/isa2fol/Lower.swift` — the report: `cites a refused statement` names ONE citation per theorem, the least.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| an isa ∃-intro concludes the body it is given, at a variable, a compound term, a value | `anExistentialIntroConcludesTheBodyItIsGiven`, `ExIntroTests` |
| a variable only the proof uses is bound at its proof's top, below its letters | `aVariableOnlyTheProofUsesIsBoundAtItsProofsTop`, `aHiddenVariableIsTheWitnessOfItsTypesInhabitation` |
| a theorem's statement binds its propositions first; a citation instantiates them first | `aMetaLevelPropositionalVariableReadsAsAFormulaVariable`, `aCitationInstantiatesItsLettersFirst` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **AN ∃-INTRO STATES ITS BODY, NEVER FINDS IT**: abstracting the witness binds every occurrence, wrong at a value
  (Lambda's `λy. x`, `equalities.Sigma_succ2`). Read the body off the formula proved: a statement, an iff's side, a
  naming.
- ⚠ **A CITATION FOL BUILDS AFTER ITS WALK MUST PARSE TO FOL-ZFC NODES**: base's parser reads `forall z. (set(z) -> …)`
  as `ifolAll(.i, …)`, which only Fol's walk lowers; `ex_intro` is bare for this.
- ⚠ **`t[try instantiate(…)]`, `t[try equation(…)]`, `t[try s.hypothesis(…)]` READ A COPY TAKEN BEFORE THE MUTATION**
  (rule 13): an index out of range the first time the node is new. Bind first.
- ⚠ **THE COMPLETE RUN NEEDS `MEM=64G`**: 55.5 GB sampled; 99% of the unit is lemmas nothing cites, requested before
  their statements fall.
- ⚠ **THE REPORT'S `cites a refused statement` COUNTS ARE NOT WHAT A STEP FREES**: each theorem names its least refused
  citation only. Follow citations down to the statements refused at their own pieces before ordering steps.
- ⚠ **A DEFINIENS IS NEVER CLOSED LETTERS FIRST**: its λs are its constant's positional parameters.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**: `git add` a new file first.
- ⚠ **A FORMULA LOGIC REWRITES IS OWED A READING IN `Replacement`**; a truth-set variable reads `holds(E)` in Reify's
  naming as in Logic's walk.
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach.
- ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF**: one transform over every root passed 32 GB.
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Rules conclude `walked`, the walk's own rule.
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**: `swift build -c release` before a run.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 14 lowered; refused: no owner 950, logic 319, cites a refused statement 2,333 | §0's complete run |
| the refused citations are led by `ZF_Base.Ball_def` 363, `Bex_def` 62, `QPair_def` 31 (step 5); `IFOL.exI` none | the same report |
| no owner is led by `use(theorem, [i], o)` 668 (`FOL.meta_simps.1` at `[i]`), `isaDefinition(zf, object, [], args: [])` 210 (step 5) | §0's through-logic report |
| Logic's 319: `If` 303 (step 6), binders over a function of classes (step 9) | the same report |
| complete run: read 44.5 s; expand 2.3, logic 136.1, registry 81.4, fol 716.8, link 50.0 s; emitted 195.8 s, 817 MB; 117.2M nodes | §0's complete run |
| comments 63/12438 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `SOURCE_SURFACE.md` predates step 7 and `exI`'s step: its `isaFree(.hidden)` rows and `exI` citations are stale;
  `surface` reads every session, and runs are the ZF session alone.
- `DESIGN.md` "What holds the 3,602 back" predates both steps; its figures came from a throwaway dump, not kept.

## 6. Open decisions
- **The next step.** By the refusals: 5, a ZF definition cited (`Ball_def` leads the refused citations; 258 at no
  owner); 6, `If` (303 at logic); `FOL.meta_simps.1` at `[i]` (668 at no owner). Beside them: 99% of the unit is lemmas
  nothing cites, now 817 MB — proving a request only once its statement stands is a design question.
- For review: "Step 7"'s eight build decisions, "An ∃-intro carrying its body"'s 2–4, "Letters first"'s two,
  "Step 4"'s four; merging the checker branch.

## 7. Next action
Get the user's choice of the next step; then write its section in `DESIGN.md` — the problem in target text, its
decisions, the contracts, the tests first — and agree it decision by decision before any code. Done when the user has
agreed every decision of that section.
