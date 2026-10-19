# STATE — isa2fol
HEAD "A theorem cited at a type, binding a proposition there: its instance a statement of the unit, as a box is" (parent `39a12ba5`) · primitives · 2026-10-18.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `A theorem cited at a type, binding a proposition there: its instance a statement of the unit, as a box is` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `13574` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 141, 127, 121, 43 tests |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `axioms` Proved 8 of 8; `logic` Schemas proved 10 of 10; `metafun` Proved 19 of 19; `zf` Proved 19 of 19 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (about 6 min) | `through logic: 2735 named theorems stand`; `no owner: 7`; `logic, unbuilt: 874` |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 48` (7:14, 24.9 GB peak; the CI), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 279`; `left out, no kept statement citing them: 8207 lemmas, 0 @defs`; `lemmas requested and refused, unbuilt: 8`; `cites a refused statement: 2456`, led by `ZF_Base.BOX_fe88880df9563825` 178; 33 parts, every one `exit 0  stderr 0`; claims 2331 of 2331, schemas 352 of 352 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "A theorem cited at a type, binding a proposition there": its agreed decision and the build's three;
  Measured — the 668 pass no owner and 548 of them stop at `If`.
- `DESIGN.md` "Step 9, widened — the definition command's local constant at a function of propositions": the reading
  decided over five others (option 2 for the stand-ins, option 3 for a hidden variable at `o ⇒ i`, step 6), its two
  agreed decisions, and **Decisions made in the build** 1–3 for review — 3 corrects emission.
- `Sources/FolDialect/Render.swift` — `Writer.binding`: a block's steps forgotten when it closes; the ⚠ on `step`.
- `Sources/Reader/Reader.swift` — `claim` and `isReadAtItsTerms`: one test names a box and substitutes it; `head`'s
  `.theorem` case: an instance binding a proposition named `<theory>.BOX_<fp>`, `Theorem.at` its types.
- `docs/FOUNDATION.md` S4 "At arity 0 …" and §3b "SO IS ONE WHOSE TYPE TAKES A PROPOSITION": a function of
  propositions has a proposition's two kinds, substituted where Isabelle substitutes, a class where bound.
- `DESIGN.md` "The steps after class existence, in order" — 6 is next by the refusals (§6).

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a box binding a variable whose type takes a function or a proposition is read at its citation, never a schema | `aBoxBindingAVariableTakingAFunctionIsReadAtItsCitation`, `…TakingAPropositionIsReadAtItsCitation` |
| a theorem cited at a type, binding a proposition there, is its instance, a statement named by its content | `aTheoremCitedAtATypeBindingAPropositionIsItsInstanceAStatement` |
| Pure's equality at a type with an argument taking a function or a proposition is `reflexive` or has no reading | `pureEqualityAtATypeTakingAFunctionIs…`, `…TakingAPropositionIsReflexivityWhenItsSidesAreOneTerm` |
| emission cites a step only inside the block that wrote it | `aStepWrittenInAClosedBlockIsDerivedAgain`; `theRealCheckerProvesWhatEmissionWrites` (`p_block`) |
| a ZF axiom cited is its lemma, proved from base's statement in NBG's words | `AxiomTests` (eight) |
| a statement is emitted no earlier than any statement it cites | `aStatementIsPlacedNoEarlierThanWhatItCites` |
| a lemma is proved only for a statement that stands, directly or through lemmas so proved | `aLemmaRequestedByAStatementCitingARefusedOneIsNeverProved` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA** and keeps the scopes of the derivation it met first
  (`derive_with_deps`): a step re-derived inside a block can die with a scope it never names. Never cite a step outside
  the block that wrote it; the kernel, not a test of the renderer's own, is what catches it.
- ⚠ **A STEP THAT LETS STATEMENTS STAND REACHES CODE NO RUN REACHED**: this step's reach failed emission, not its own
  code. Run the complete run and the kernel check, not only through logic — the through-logic count did not move.
- ⚠ **A FORMULA BUILT AT ONE FRAME IS LIFTED BEFORE A DEEPER FRAME READS IT** (`Scope.lift`).
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE PROVER'S WORDS, CHECKED ONLY BY THE KERNEL**: match `base/tiers/zf` to the walk.
- ⚠ **AN INSTANCE OR A LEMMA REQUEST IS BUILT FROM `t[id]`, NEVER FROM `n`'S CHILDREN**; ⚠ **A TEST INTERNS EVERY NODE
  BEFORE ITS TABLE IS PASSED**; ⚠ **`t[try instantiate(…)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13).
- ⚠ **A BINDER AT `iⁿ ⇒ i` INSTANTIATED AT A CLASS LEAVES `function(K)` A PREMISE**: discharge it.
- ⚠ **AN ∃-INTRO STATES ITS BODY, NEVER FINDS IT**; ⚠ **A DEFINIENS IS NEVER CLOSED LETTERS FIRST**.
- ⚠ **A STEP'S REACH IS READ IN THE REFUSALS, NEVER IN THE UNIT'S SIZE OR THE CLOSURES' BOUND.**
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY**; ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**;
  ⚠ **STATE GOES IN ITS STEP'S COMMIT**; ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 279 lowered; refused: no owner 7, logic 874, cites a refused statement 2,456 | §0's complete run |
| `FOL.meta_simps.1` at `[i]` is `schema FOL.BOX_c94ff9da85184c7d [A0(0)]: ((forall b1. (set(b1) -> A0)) <-> A0)`, kernel-checked | `grep 'BOX_c94ff9da85184c7d' DIR/FOL.fol.def`; §0's check |
| `IFOL.not_def`, `iff_def`, `notI`, `iffD1`, `iffD2`, `FOL.cases_simp` are in the unit, kernel-checked | `grep '^\(claim\|schema\) IFOL\.iffD1' DIR/IFOL.fol.def`; §0's check |
| refused citations led by `ZF_Base.BOX_fe88880df9563825` 178, `Replace_iff` 144, `FOL.IFOL_simps.32` 116, `RepFunI` 77, `Inter_iff` 76 | §0's complete run |
| `upair.succ_iff`, `UpairI1`, `ZF_Base.infinity` refused; the four cite `IFOL_simps.32`, `BOX_fe88…`, `infinity_AXIOM`, `UpairI2` | `lower … $ZF --theorem upair.succ_iff,ZF_Base.infinity,upair.UpairI1,ZF_Base.Replace_iff` |
| Logic's 874: `If` (873, `if_def` stopping at `If ≡ If`) and `AC.AC`; no owner 7, unrestricted type variables (`pair.split`, `Inductive.def_trans`) | §0's through-logic report |
| complete run: read 46.0 s; expand 4.1, logic 295.0, registry 35.6, fol 32.9, link 2.9 s; 264.2 MB, 2,884,207 steps written; 75.6M nodes, 24.9 GB peak | §0's complete run |
| comments 64/13574 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- From a throwaway trace of every refusal (not kept): `BOX_fe88…` falls through `ZF_Base.BOX_8405…` and
  `FOL.int_all_simps.3` with `FOL.BOX_1cd4667e985779e8`, a variable only the proof uses at `(i ⇒ o) ⇒ o ⇒ i` and
  `o ⇒ (i ⇒ o) ⇒ i`; `Replace_iff` through `IFOL_simps.32`, `quant_simps.1` with `IFOL.BOX_701952b5794ca2e9`, one at
  `o ⇒ i`; `succ_iff` through `UpairI2`, `Replace_iff`; the 8 unbuilt lemmas are `CLASS_<fp>`, `ZF_Base.bexE` behind
  `CLASS_02a8d0fe3431aadb`; FOL's `induct_conj_def`, `induct_implies_def` are not in the ZF session's unit.
- `is_bool_of_o`'s box (ZF-Constructible) is now read at its citation: outside the ZF session, never run.
- `SOURCE_SURFACE.md` predates step 7 (stale `isaFree(.hidden)`).

## 6. Open decisions
- **The next step.** By the refusals: step 6 — `If`, `bool_of_o` and a variable only the proof uses at `o ⇒ i`, a
  proposition as an argument its truth set (decided in outline, user 2026-10-18): `If` holds 873 at Logic, 548 of them
  freed from no owner by the last step, and `Replace_iff` 144, `IFOL_simps.32` 116 wait on the hidden `o ⇒ i`; then
  the one at a type taking a class (`BOX_fe88…` 178), with no reading as a variable — its own design; the class
  prover's λs it does not build (8 `CLASS_` lemmas); `AC.AC`. Memory: the CI peaked at 24.9 GB, under `MEM=32G`.
- **For review**: the instance step's three build decisions; step 9 widened's three (3: emission corrected, +3.3%
  steps, the checker's bookkeeping mirrored would win it back); step 8's five; step 9's three; step 5's six; and the earlier steps' (§6 of the last
  STATE in git history); merging the checker branch.

## 7. Next action
Get the user's choice of the next step; then write its section in `DESIGN.md` — the problem in target text, its
decisions, the contracts, the tests first — and agree it decision by decision before any code. Done when the user has
agreed every decision of that section.
