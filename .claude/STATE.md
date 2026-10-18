# STATE — isa2fol
HEAD "Step 8: ZF's axioms derived from NBG, read back into Isabelle's form; Regularity pinned" (parent `84f39eaa`) · primitives · 2026-10-18.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Step 8: ZF's axioms derived from NBG, read back into Isabelle's form; Regularity pinned` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `13572` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `18` — NBG with Regularity, and `elem_first_subst`; Choice unstated; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 140, 126, 121, 43 tests |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `axioms` Proved 8 of 8; `logic` Schemas proved 10 of 10; `metafun` Proved 19 of 19; `zf` Proved 19 of 19 |
| `swift build -c release`, then `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF` (about 3 min) | `through logic: 2617 named theorems stand`; `no owner: 673`; `logic, unbuilt: 326` |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 48` (4:37; the CI), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 215`; `left out, no kept statement citing them: 7058 lemmas, 0 @defs`; `cites a refused statement: 2402`, led by `IFOL.iffD2` 128; 32 parts, every one `exit 0  stderr 0`; claims 2189 of 2189, schemas 110 of 110 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, nothing uncommitted. The checker is fol-zfc-comb
`224d60e`, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Step 8 — ZF's axioms, derived from NBG": the three agreed decisions (base states each axiom in NBG's
  words and a lemma per axiom reads it back; Regularity, Mendelson's axiom D; `infinity`'s `succ` read by `upair.succ_iff`,
  emission placing a statement no earlier than what it cites), and **Decisions made in the build** 1–5 for review.
- `Sources/Lowering/Axioms.swift` — `AxiomProver.prove`, `AxiomReading.target` / `hole` (the three readings),
  `primitiveProof` (class at tuple, `AtTuple`), `functionProof` and `Members` (the members theorem, the term's UNIQ).
- `base/tiers/zf.fol.def` — the six `ZF_Base.a_NBG` statements, `cong_Union_l`, `cong_Pow_l`, `tup2_uniq`,
  `slot_p_q`, `slot_q_p`; `base/axioms.fol.def` — `regularity`, `no_self_member`.
- `DESIGN.md` "Step 9 — the definition command's local constant", "Review after step 5 — the small fixes": decisions
  still for the user's review.
- `DESIGN.md` "The steps after class existence, in order" — 6 remains, and 9's other pieces; the refusals order them.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 18 axioms, NBG's with Regularity | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a ZF axiom cited is its lemma, proved from base's statement in NBG's words | `AxiomTests` (eight) |
| the registry hands provers the named statements; a prover's `cites` refuses the lemma citing it | `theRegistryHandsItsProversTheNamedStatements`, `aLemmaCitingAStatementTheUnitLacksIsRefusedCitingIt` |
| a statement is emitted no earlier than any statement it cites | `aStatementIsPlacedNoEarlierThanWhatItCites` |
| a ZF definition cited concludes its `c_UNFOLD` instantiated at its terms, by ID | `DefinitionTests` (seven), `aFunctionsUnfoldingIsProvedFromItsDef` |
| a box binding a variable whose type takes a function is read at its citation | `aBoxBindingAVariableTakingAFunctionIsReadAtItsCitation` |
| a lemma is proved only for a statement that stands, directly or through lemmas so proved | `aLemmaRequestedByAStatementCitingARefusedOneIsNeverProved`, `aLemmaSetAsideAndCitedByAProofLaterIsProvedAndKept` |
| format and lint are the tools', before every run of the program | `pre-commit run --all-files`; the commit hook |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A FORMULA BUILT AT ONE FRAME IS LIFTED BEFORE A DEEPER FRAME READS IT** (`Scope.lift`): read under more binders it
  names other variables, and the table reports a premise mismatch far from the cause (`Members.members`).
- ⚠ **BASE'S `_NBG` STATEMENTS ARE THE PROVER'S WORDS, CHECKED ONLY BY THE KERNEL**: the citation's root is the words the
  prover computes; a change to the walk's rendering of an atom must be matched in `base/tiers/zf` (`AxiomTests` catch it).
- ⚠ **AN INSTANCE OR A LEMMA REQUEST IS BUILT FROM `t[id]`, NEVER FROM `n`'S CHILDREN**: `n` holds the walk's naming.
- ⚠ **A TEST INTERNS EVERY NODE BEFORE ITS TABLE IS PASSED**: bind, then call.
- ⚠ **A BINDER AT `iⁿ ⇒ i` INSTANTIATED AT A CLASS LEAVES `function(K)` A PREMISE**: discharge it, or the next step mismatches.
- ⚠ **AN ∃-INTRO STATES ITS BODY, NEVER FINDS IT**; a citation Fol builds after its walk must parse to fol-zfc nodes.
- ⚠ **`t[try instantiate(…)]`, `t[try graphs.definitionCited(…)]` READ A COPY TAKEN BEFORE THE MUTATION** (rule 13): an index
  out of range when the node is new. Bind first.
- ⚠ **A STEP'S REACH IS READ IN THE REFUSALS, NEVER IN THE UNIT'S SIZE OR THE CLOSURES' BOUND**: step 8's closures bounded
  1,571 more; the refusals moved to the logic's own theorems.
- ⚠ **A STEP THAT LETS STATEMENTS STAND REACHES CODE NO RUN REACHED**: run the complete run, not only through logic.
- ⚠ **A DEFINIENS IS NEVER CLOSED LETTERS FIRST**; ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add`
  first).
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT**: kernel-check every new reach. ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF.**
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY**: the axioms' prover reads a definition through `unfolding`,
  Reify's, and a class at its tuple through `AtTuple`, the unfolder's.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT.**

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 215 lowered; refused: no owner 673, logic 326, cites a refused statement 2,402 | §0's complete run |
| `ZF_Base.extension`, `Union_iff`, `Pow_iff`, `replacement`, `foundation` and their `_AXIOM` lemmas are in the unit, kernel-checked | `grep '^claim ZF_Base\.' DIR/ZF.ZF_Base.fol.def`; §0's check |
| `ZF_Base.infinity` falls citing `ZF_Base.infinity_AXIOM`, which falls with `upair.succ_iff` (it cites `IFOL.iffD1`, `upair.UpairI1`) | `lower … $ZF --theorem upair.succ_iff,ZF_Base.infinity` |
| the refused citations are led by `IFOL.iffD2` 128, `FOL.IFOL_simps.32` 111, `ZF_Base.Replace_iff` 108 (it cites `IFOL_simps.32`), `Inter_iff` 76, `RepFunI` 71, `IFOL.notI` 54, `IFOL.iffD1` 45, `Bool.cond_DEF` 25 | §0's complete run; `--theorem ZF_Base.Replace_iff` |
| no owner is led by `use(theorem, [i], o)` 668; Logic's 326: `If` (325) and `AC.AC` | §0's through-logic report |
| complete run: read 46.3 s; expand 2.2, logic 151.9, registry 24.4, fol 32.2, link 2.7 s; 249.9 MB; 42.4M nodes | §0's complete run |
| comments 64/13572 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `use(theorem, [i], o)` is `FOL.meta_simps.1` at `[i]`: from a throwaway dump, not kept.
- `IFOL.iffD1`, `iffD2`, `notI` and `FOL.IFOL_simps.32` are refused at `not_def` / `iff_def`, "a variable of type `o ⇒ o`"
  (CLAUDE.md): not traced this session.
- `SOURCE_SURFACE.md` predates step 7 and `exI`'s step: its `isaFree(.hidden)` rows and `exI` citations are stale.

## 6. Open decisions
- **The next step.** By the refusals: the logic's own theorems (`IFOL.iffD2` 128, `FOL.IFOL_simps.32` 111, `IFOL.notI` 54,
  `IFOL.iffD1` 45 — trace why each falls first); 6, `If` (325 at logic; `Bool.cond_DEF` 25); `use(theorem, [i], o)`
  (668 at no owner); `AC.AC` (Choice, Pi).
- **For review**: step 8's five build decisions; step 9's three; step 5's six; "Lazy proving"'s three, "Step 7"'s eight,
  "An ∃-intro carrying its body"'s 2–4, "Letters first"'s two, "Step 4"'s four; the review's open items (`combination`'s
  two constructions, `isaHidden` at `o`); merging the checker branch.

## 7. Next action
Get the user's choice of the next step; then write its section in `DESIGN.md` — the problem in target text, its
decisions, the contracts, the tests first — and agree it decision by decision before any code. Done when the user has
agreed every decision of that section.
