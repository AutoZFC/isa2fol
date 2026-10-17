# STATE — isa2fol
HEAD (see §0) · primitives · 2026-10-17.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user, 2026-10-17). Lint first: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Step 4: Pure's equality between functions, read pointwise; combination substitutes by the replacement walk` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `12101` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `MEM=24G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 137, 102, 113, 42 tests |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`, Proved n of n; `metafun` 18 of 18 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (2:09, peak 6.7 GB) | `through logic: 2058 named theorems stand`; `logic, unbuilt: 257` |
| `MEM=56G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR` (11:04, peak 34.3 GB; the CI), then `scripts/check-unit.sh DIR` | `lowered … 14`; 17 parts; claims 6057 of 6057, schemas 100 of 100; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, tree clean. The checker is fol-zfc-comb `224d60e`, branch
`libraries-and-streaming`, unmerged; build it only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE: consulted, never merged.

## 2. Read these first-hand
- `DESIGN.md` "Step 4 — Pure's equality between functions" — the two agreed decisions (pointwise; `combination` by the
  replacement walk), why not classes nor a lemma per function, the four decisions in the build, Measured.
- `Sources/Lowering/Functions.swift` — the pointwise formula, the five rules, `atSet` and `atClass` with `Substitution`
  (`Y` and `Z` fixed for the walk alone, dropped by `unshift`).
- `Sources/Lowering/Congruence.swift` — `Replacement`: the walk, now reading a stated function equation pointwise.
- `Sources/Lowering/Instance.swift` — `units`, `slotConverted(template:)`, `chained`: shared by Reify, Lambda, Functions.
- `Sources/Lowering/Lambda.swift` — the instance at a λ, which `combination` uses at a class argument.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms, NBG and `elem_first_subst` | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| `f ≡ g` and `⋀x. f x ≡ g x` are one formula, at a predicate, a function and a function of classes | `anEquationBetweenFunctionsIsItsPointwiseFormula` |
| Pure's five rules between functions, kernel-checked: `combination` at a set argument (variable, compound, value `i`) and a class argument (applied, in a slot) | `FunctionEqualityTests` |
| an instance at a λ concludes the walk's own rewrite of Isabelle's formula, kernel-checked | `LambdaTests` |
| a λ holding a proposition is a schema in it; the class prover refuses it, and its citers fall | `aLambdaHoldingALetterIsASchemaInIt` |
| a run through a stage stops there; an unknown stage stops the run | `PipelineTests` |
| emission writes the same bytes at any number of threads | `emissionWritesTheSameBytesAtAnyNumberOfThreads` |
| format and lint are the tools', run before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A FORMULA LOGIC REWRITES IS OWED A READING IN `Replacement`.** A stated `≡` at `i ⇒ i` inside a walked template
  stopped the ZF run (`noCongruence`, `Bin.bin.case_eqns.1`) until the walk read it pointwise.
- ⚠ **A FRAME'S VARIABLE READ BEFORE AN `open` OR A `fix` NAMES THE WRONG BINDER AFTER IT**; `s.variable(s.fix(.i))`
  reads the scope before the fix. Read `frame.variable(level)` where it is used.
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13): `t[try s.hypothesis(…)]` again in
  step 4. Bind first.
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach.
- ⚠ **`exists_intro` ABSTRACTS EVERY OCCURRENCE OF ITS WITNESS**: close a naming around a fresh `z = value`.
- ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF**: one transform over every root passed 32 GB.
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Rules conclude `walked`, the walk's own rule.
- ⚠ **A BOX'S NAME MOVES WITH THE IR'S PRINTED PAYLOAD**: count boxes, never diff their names.
- ⚠ **A LETTER IS THE READER'S, NEVER A POSITION AFTER EXPAND.** A serial never reaches output.
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**: `swift build -c release` before §0's runs.
- ⚠ **A SHORT SWIFT STRING IS STORED INLINE**: `strings` misses a ≤15-byte literal; check a build by its timestamp.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| ZF session (3,616 named): 14 lowered; refused: no owner 1,301, logic 257, letter off spine 797, cites refused 1,247 | §0's complete run |
| Logic's 257: `If` 245 (step 6), binders over a function of classes (step 9); no owner led by `isaFree(i)` 731, `use(theorem, [i], o)` 668, `isaDefinition(zf, object, [], args: [])` 210 | §0's through-logic report |
| complete ZF run: read 41.6 s, expand 1.4 s, logic 75.8 s, registry 38.0 s, fol 341.2 s, link 21.2 s, emission 140.8 s; 76.7M nodes; 382 MB | §0's complete run |
| 6,013 of the 6,057 claims are in the `_uncited` parts; `λ classExists` writes 4.3 of 5.7 million steps | the same report; `check-unit.sh` |
| 134 lemmas requested and refused, unbuilt | the same report |
| comments 59/12101 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 797 letters off their spine are step 3's gap — an instance walking under a `⋀` at `o` that the cited theorem
  binds after the instantiated variable (`allE`-like rules) — from their three patterns alone, no per-theorem trace.
- Few if any of the 14 are new: before step 4 no ZF theorem holding Pure's equality between functions passed Logic, and
  the ZF session alone was never run complete before.

## 6. Open decisions
- **The next step**, the user's to choose: the letter off its spine (797, the largest refusal after no owner); step 5,
  a ZF definition cited (270 need only it); the lemmas nothing cites, dropped at link (99% of the unit); the run's cost
  (11 min, 34 GB; Logic 10× slower than before step 4); step 6's `If` (245); step 7's hidden variable (731).
- For the user's review: "Step 4 — …"'s four decisions in the build; the earlier steps' listed in their sections;
  merging the checker branch.

## 7. Next action
Put the next step to the user — the letter off its spine against step 5. Done when the user has chosen.
