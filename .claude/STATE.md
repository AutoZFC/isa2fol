# STATE — isa2fol
HEAD (see §0) · primitives · 2026-10-16.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Functions of propositions and the bound ⋀P: Pure's ⋀ over a proposition is a truth set, read apart from a statement's own variables` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `8219` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 132, 107, 77, 41, 14 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`, Proved n of n; `truth` Schemas proved (2 of 2) |
| `MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export` | `proved: 9420` of 9420; cited: 200 named, 956 boxes binding a proposition, all proved |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`, then `scripts/check-unit.sh DIR` | 9 named lowered; 8 parts; claims 1433 of 1433, schemas 29 of 29; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, tree clean. The checker is fol-zfc-comb `224d60e`, branch
`libraries-and-streaming`, unmerged; build it only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE: consulted, never merged.

## 2. Read these first-hand
- `docs/FOUNDATION.md` S4 — a proposition an object as its truth set; a function of propositions applied to truth sets is
  its body at `∅ ∈ E` (a λ a wrapper), its equation pointwise, `combination` its instance then β.
- `DESIGN.md` "Functions of propositions and the bound `⋀P`" — decision 6 (the reader's kinds), the seven decisions in
  the build, Measured: where the logic's facts stop now.
- `Sources/Lowering/Truth.swift` — `Truths`: pointwise, the equality steps, `combination`, the truth instance, `fill`.
- `Sources/Reader/Terms.swift` — the `top` flag and `metaAll`: a statement's own `⋀` vs Pure's `⋀` over a proposition.
- `Sources/Lowering/Expand.swift` — `reflexivity(_:)`: a definition's citation inlined, its parameters letters (decision 3).

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms, NBG and `elem_first_subst` | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| Pure's `⋀` over a proposition below a statement's top is its own three kinds; a free proposition the letter | `pureAllOverAPropositionIsItsOwnNodeAndAFreeOneTheLetter`, `aMetaQuantifierOverAPropositionIsPuresBoundAll` |
| a truth set and a function of propositions lower and the kernel proves them, `TERM`'s `⋀C` at a top and in a premise alike | `pureAllOverAPropositionIsLoweredAndProved`, `aRewriteUnderTruepropIsLoweredAndProved` |
| a box binding a proposition is cited by `<theory>.BOX_<fingerprint>`, the same at any serial | `aBoxBindingAPropositionIsCitedByItsContentsName` |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A LETTER IS THE READER'S, NEVER A POSITION AFTER EXPAND.** Expand unfolds a definition's `⋀` (`&&&`, `TERM`) onto a
  statement's top; read by position there, one formula took two readings and the table refused the step.
- ⚠ **A REGEX ADDING NEW KINDS TO CATCH-ALL LISTS ALSO EXTENDS DEDICATED CASES**: `case .isaIffReflection:` swallowed the
  three new kinds into `iff_reflection`. Check every insertion site by hand.
- ⚠ **A SERIAL NEVER REACHES OUTPUT.** A box is named by its proof's content (§4.6 R2).
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13): `t[try shift(…)]` struck again. Bind first.
- ⚠ **BASE'S STATEMENTS ARE FOL-ZFC; THE WALK'S ARE ISA UNTIL FOL.** A truth set's binder is fol-zfc's own `∀`, its witness
  from `truth_EX` untyped: Fol never discharges `set` at it.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 9 of 9,420 named lowered; refused: no owner 6,722, logic 1,084, letter off spine 13, cites refused 1,592 | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| refused citations led by `Formula.satisfies_DEF` 63, `IFOL.TrueI` 51 | the same report |
| kernel: 8 parts, claims 1,433 of 1,433, schemas 29 of 29; `IFOL.True_def` among the claims | `scripts/check-unit.sh DIR`; `grep True_def DIR/IFOL.fol.def` |
| comments 40/8219 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `TrueI`, `FOL.ccontr` wait only on `protectD`/`protectI`, which instantiate `prop_def`'s letter inside a proof (Expand
  inlines a definition's citation); `notI`, `notE`, `iffI`, `iffD1` also on `not_def`/`iff_def`, whose boxes bind a
  variable of type `o ⇒ o` and use `≡` as a function of such. From the throwaway diagnostic of this session's builds.
- 358,349 citation sites apply all their frees, 94 partial ones leaving no proposition (a throwaway count).

## 6. Open decisions
- **The next step**, the user's to choose: a definition's citation stays a citation (its unfolded statement a schema,
  `schema_inst` at its letters — `protectD`, `protectI`, then `TrueI`, `FOL.ccontr`); a variable of type `o ⇒ o` and `≡`
  over functions of propositions (the derived definitions `not_def`, `iff_def`); `OFCLASS(i, term)` (5,601 named); `exI`.
- For the user's review: "Functions of propositions and the bound `⋀P`"'s seven decisions in the build; "Boxes binding a
  proposition"'s three and four; "The logic's rules read as steps"'s four; step 2's `Equalities.atI`; emission's seven;
  merging the checker branch.

## 7. Next action
Put the next step to the user, in the docs' own terms: which of §6's first item comes next. Done when the user has chosen.
