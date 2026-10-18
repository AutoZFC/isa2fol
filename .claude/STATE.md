# STATE — isa2fol
HEAD "Reify's formula naming by Logic's walk: a λ's class definition is its body walked" (parent `6c04a247`) · primitives · 2026-10-17.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Reify's formula naming by Logic's walk: a λ's class definition is its body walked` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `12864` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 139, 117, 119, 42 tests |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `logic` Schemas proved 10 of 10; `metafun` Proved 19 of 19 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (about 3 min) | `through logic: 2557 named theorems stand`; `no owner: 680`; `logic, unbuilt: 379` |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 48` (4:13, 13.3 GB; the CI), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` (21 s) | `lowered … 170`; `left out, no kept statement citing them: 7013 lemmas, 14 @defs`; `cites a refused statement: 2387`, led by `ZF_Base.Ball_def` 487; 31 parts, every one `exit 0  stderr 0`; claims 1942 of 1942, schemas 104 of 104 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Review after step 5 — the small fixes": what the review fixed, and **For the user's decision** —
  `combination`'s two constructions; `isaHidden` at `o`. The η-long variable named by itself, in a slot or at an
  instance, is DECIDED AGAINST (user, 2026-10-17): step 3's one rule stands. Reify's formula naming is BUILT: "Reify's
  formula naming by Logic's walk", its one build decision for the user's review.
- `DESIGN.md` "Step 5 — a ZF definition cited": the two agreed decisions, and **Decisions made in the build** 1–6 for
  the user's review — 5 and 6 fix earlier steps' code (step 4's `reflexive`, lazy proving's set-aside).
- `Sources/Lowering/Unfolding.swift` — `unfolded` (the rule), `UnfoldingProofs`, `readBack` (class parameters).
- `Sources/IR/Pass.swift` `Run.pruned`, `add`, `setAside`, `linked` — a request no remaining statement cites is set
  aside, and comes back when a proof the registry makes cites it.
- `Sources/Lowering/Lambda.swift` `LambdaProofs.classAtArguments`, `atTuple`, `LambdaInstance.equivalence` — shared
  with step 5's prover; `atArguments` (a free function) is the formula they prove.
- `DESIGN.md` "The steps after class existence, in order" — steps 6, 8, 9 remain; the refusals order them.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a ZF definition cited concludes its `c_UNFOLD` instantiated at its terms, by ID, at every kind of constant | `DefinitionTests` (seven), `aFunctionsUnfoldingIsProvedFromItsDef` |
| an isa ∃-intro concludes the body it is given | `anExistentialIntroConcludesTheBodyItIsGiven`, `ExIntroTests` |
| a lemma is proved only for a statement that stands, directly or through the proofs of lemmas so proved | `aLemmaRequestedByAStatementCitingARefusedOneIsNeverProved`, `aLemmaSetAsideAndCitedByAProofLaterIsProvedAndKept` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **AN INSTANCE OR A LEMMA REQUEST IS BUILT FROM `t[id]`, NEVER FROM `n`'S CHILDREN**: `n` holds the walk's naming,
  and a named λ in an EX request is one the class prover cannot read (`unread`) — step 4's `reflexive` did it.
- ⚠ **A TEST INTERNS EVERY NODE BEFORE ITS TABLE IS PASSED**: `lowered(l, [Statement(… try cited(…, &l) …)])` copies
  `l` first, and the citation is missing from the unit's table (`unproved … conclusion: nil`). Bind, then call.
- ⚠ **A BINDER AT `iⁿ ⇒ i` INSTANTIATED AT A CLASS LEAVES `function(K)` A PREMISE**: discharge it, as `LambdaInstance`
  and `readBack` do, or the next step mismatches (`premiseMismatch`).
- ⚠ **AN ∃-INTRO STATES ITS BODY, NEVER FINDS IT**: abstracting the witness binds every occurrence, wrong at a value.
- ⚠ **A CITATION FOL BUILDS AFTER ITS WALK MUST PARSE TO FOL-ZFC NODES**: `ex_intro` is bare for this.
- ⚠ **`t[try instantiate(…)]`, `t[try equation(…)]`, `t[try s.hypothesis(…)]` READ A COPY TAKEN BEFORE THE MUTATION**
  (rule 13). Bind first.
- ⚠ **A STEP'S REACH IS READ IN THE REFUSALS, NEVER IN THE UNIT'S SIZE**; the report's `cites a refused statement`
  counts name each theorem's least refused citation only — follow citations down before ordering steps.
- ⚠ **A STEP THAT LETS STATEMENTS STAND REACHES CODE NO RUN REACHED**: their lemmas are proved for the first time, and
  earlier steps' bugs surface in the complete run (step 5 met two). Run the complete run, not only through logic.
- ⚠ **A DEFINIENS IS NEVER CLOSED LETTERS FIRST**: its λs are its constant's positional parameters.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**: `git add` a new file first; SwiftFormat may reorder
  declarations a change makes internal — lint before the tests and the build.
- ⚠ **A FORMULA LOGIC REWRITES IS OWED A READING IN `Replacement`**; a truth-set variable reads `holds(E)`.
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach.
- ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF**: one transform over every root passed 32 GB.
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Rules conclude `walked`, the walk's own rule; a λ's
  class definition is `walked(formula:)`. ⚠ `walked(_:base:)` WALKS PROOFS TOO (Lambda's β at a compound term): made
  formula-only, three tests stopped at `predicateArgumentNotVariable`.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**: `swift build -c release` before a run.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 170 lowered; refused: no owner 680, logic 379, cites a refused statement 2,387 | §0's complete run |
| the refused citations are led by `ZF_Base.Ball_def` 487, `Bex_def` 107 (step 9's box binding a function of classes), `Bool.cond_DEF` 23 (step 6) | the same report |
| no owner is led by `use(theorem, [i], o)` 668 | §0's through-logic report |
| Logic's 379: `isaConst(defined zf object, o ⇒ i ⇒ i ⇒ i)` 325 — `If` (step 6); binders over a function of classes (step 9) | the same report |
| complete run: read 47.7 s; expand 2.3, logic 135.9, registry 22.3, fol 27.2, link 2.4 s; 194.8 MB; 36.7M nodes | §0's complete run |
| the unit holds 126 `c_UNFOLD` lemmas, 33,761 steps; 147 `@def`s stated, 69 refused; no lemma refused unbuilt | the same report, `steps by kind` |
| comments 61/12864 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `use(theorem, [i], o)` is `FOL.meta_simps.1` (`(⋀x::'a. PROP V) ≡ PROP V`) at `[i]` in the statements holding it: its
  statement is read from `FOL/theory/thms`; that the 668 hold it alone came from a throwaway dump, not kept.
- `SOURCE_SURFACE.md` predates step 7 and `exI`'s step: its `isaFree(.hidden)` rows and `exI` citations are stale.
- The definition command's `_def` theorems of the constants taking a class all go through the box binding a function of
  classes (`Ball_def`, `Bex_def` read; the other 36 of the 38 assumed alike).

## 6. Open decisions
- **The review's open items** (`DESIGN.md` "Review after step 5"): `combination`'s two constructions; `isaHidden` at
  `o`.
- **The next step.** By the refusals: 6, `If` (325 at logic; `Bool.cond_DEF` 23 among the refused citations); 9, a
  binder over a function of classes (`Ball_def` 487, `Bex_def` 107 — the definition command's box at the constant);
  `use(theorem, [i], o)`, believed `FOL.meta_simps.1` at `[i]` (668 at no owner).
- For review: step 5's six build decisions; "Lazy proving"'s three, "Step 7"'s eight, "An ∃-intro carrying its body"'s
  2–4, "Letters first"'s two, "Step 4"'s four; merging the checker branch.

## 7. Next action
Get the user's decision on the review's open items and the choice of the next step; then
write its section in `DESIGN.md` — the problem in target text, its
decisions, the contracts, the tests first — and agree it decision by decision before any code. Done when the user has
agreed every decision of that section.
