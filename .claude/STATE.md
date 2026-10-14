# STATE — isa2fol
The commit "STATE: handoff — Expand with ZF's meta level built (a54f0093); …" · primitives · 2026-10-14.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `STATE: handoff — Expand with ZF's meta level built (a54f0093); next, Logic's contract` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `git stash list \| head -1` | `stash@{0}: On kinds-proposal: S1 a λ is a wrapper: FOUNDATION + DESIGN Step (4) revised …` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `3437` |
| `ls Sources/Lowering \| tr '\n' ' '` | `Expand.swift Fol.swift Logic.swift Plan.swift Reify.swift Typing.swift` |
| `grep -m1 '^## Patterns' docs/SOURCE_SURFACE.md` | `## Patterns (2597)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed, in any order: 116, 85, 26, 14, 14 tests |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, branched from `caaa0e16` (2026-09-29). **`kinds-proposal` (`21ca100f`)
is the REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged — kept where it did well, improved where a
principle faults it. Its principles are this branch's: `CLAUDE.md` "Design rules".

## 2. Read these first-hand
- `DESIGN.md` §4a "Lowering's components" — Logic's business and its rows in the owner table; "Expand" — what Logic
  receives (its contract row; axioms' statements unfolded; `Pure.reflexive` cited at definitions' equation types);
  "The meta level, lowered" — what logic removes, and "Where Isabelle's computation becomes proof".
- `Sources/Lowering/Logic.swift` — the owner switch Logic's step makes exact; `Expand.swift` beside it, a built pass:
  ONE switch over `Pattern` (`piece`) for ownership and dispatch.
- `docs/FOUNDATION.md` §3b "The proof layer" — Pure's rules re-render, proved as schemas in
  `docs/phase2_probes/proof_layer.fol.def`; §2 S4 — the `⋀P::o` of the ND rules classified out.
- `Sources/IR/Pass.swift` — `Run`: `lower`, `prove`, `linked`.
- `Sources/Reader/Reader.swift` — `unit()`, `definition(of:at:)`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a pattern has at most one owner | `PipelineError.twoOwners`; `twoPassesOwningOnePatternStopTheRun` |
| a pattern no pass owns stops its statement before the first pass; one a pass owns unbuilt, at that pass | `aPatternNoPassOwnsIsRefusedBeforeTheFirstPassNamingEveryOne`, `aPatternItsPassHasNotBuiltIsRefusedAtThatPass` |
| no pattern survives its owner or comes back after it; each proof concludes its statement by ID after every pass | `PipelineError.survived`, `.unproved`; `aPatternThatSurvivesItsOwnPassStopsTheRun` |
| a citation of a theorem or a lemma names a statement, by ID; a statement citing a refused one falls, transitively | `linked`; `aStatementCitingARefusedOneIsRefusedTransitively`, `aCycleOfCitationsStopsTheRun` |
| a lemma is added once, in the registry's vocabulary, proved by the one prover owning its request or refused there | `aLemmaTwoStatementsCiteIsAddedOnceAndLoweredWithBothAsOneNode`, `TypingTests` |
| a definition is handed to the pass owning its constant, as it stands at that pass's input | `aPassReadsTheDefinitionsOfTheConstantsItOwnsAsTheyStandAtItsInput`, `aDefinitionOwnedByALaterPassReachesItUnfolded` |
| a logic constant unfolds by its definition at its type; a citation of its definition is `Pure.reflexive` under `⋀`-intros at its parameters | `ExpandTests` |
| a definition carries `axiomTypes`, `parameters`, and `Pure.reflexive` read at its equation's type | `aDefinitionCarriesItsAxiomsTypeArgumentsItsParametersAndPureReflexiveAtItsEquation` |
| a defined constant keeps its declared level; `unfolds(family, level)` is the one border Expand's and Reify's switches read | `aDefinedConstantKeepsItsDeclaredLevel`, `eachPatternHasTheOwnerTheDivisionGivesIt`, `aZFDefinitionAtTheMetaLevelUnfoldsAsTheLogicsDo` |
| what the pipeline keeps is fol-zfc | `legalize`; `aStatementWhoseOnlyIsaPieceIsALogicConstantIsLoweredWhole` |
| the reader emits only the isa and both dialects; a gap in the dialect STOPS the read | `theReaderEmitsOnlyTheIsaDialect`; `DialectGap` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests, `MEM=32G` read and lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **EACH COMPONENT MINDS ITS OWN BUSINESS** (user, 2026-10-13/14): Typing is no pass; Reify states and proves EX and
  UNIQ and nothing more; each lemma is proved by the component that states it.
- ⚠ **A PASS NEVER WRITES A PATTERN IT OWNS.** Fol writes `set(folBound(0))`; Expand writes unfolded definientia.
- ⚠ **A VARIABLE BECOMES `folBound` ONLY AT `i`, ONLY IN FOL.** A class variable relabelled early reads as a set.
- ⚠ **A DEFINITION IS WRITTEN IN TWO FORMS**: `c ≡ λx. b` (IFOL's, FOL's), and the applied `c(x) ≡ b` over the
  axiom's frees — ALL of Pure's (`prop_def`, `conjunction_def`, `term_def`) and `primrec`'s. `parameters` tells them apart.
- ⚠ **`Definition.reflexive` IS NEVER LOWERED**: the pipeline lowers `definiens` alone; only Expand, first, reads it.
- ⚠ **A ZF CONSTANT DECLARED AT THE META LEVEL IS NEVER NAMED** (FOUNDATION §2, "named only at the object level"):
  `split`, `qsplit`, `MetaExists.ex`, `L_Reflects`, `AC18` unfold in Expand. Reading `prop` as `o` and instantiating
  `'a` erase what marks them, so the level is kept on the constant (`Defined.level`), never inferred from a use's type.
- ⚠ **AN AXIOM'S STATEMENT ARRIVES UNFOLDED after Expand**: `iff_reflection`'s `↔`, `classical`'s `¬`, ZF's `↔`/`¬`.
- ⚠ **`Unit(table: t, statements: [try citing(…, &t)])` COPIES `t` BEFORE THE INTERN** (rule 13): build the statements first.
- ⚠ **A BUILT RULE NEVER REFUSES.** Only the pipeline refuses, before a pass, and the registry, for a lemma.
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.
- ⚠ **A λ IS A WRAPPER, NOT A CONSTANT `L` STATEMENTS NAME** (the reference's discarded amendment lost 52 ZF theorems).

## 4. State
| claim | verified by |
|---|---|
| `lower`: 0 of 9,420 lowered; refused at no owner 7,176, logic 1,078, reify 1,115; none at expand; 51 pass every pass and fall citing the refused `IFOL.TrueI` | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| the unit holds 133 theorems cited outside the ZF sessions and 1,004 definitions; 1,000 reach the pass owning their constant | the same run |
| top logic patterns: `ifolAll(o, body: o)` 1,036, `isaAllElim(o, o)` 971, `use(axiom Pure.equal_elim, [], o)` 505, `use(axiom Pure.symmetric, [o], o)` 463 | the same run |
| `Lowering.pipeline`: expand, logic, reify, fol; Typing's registry after reify, with no prover | `thePlanIsTheDesignsOrder` |
| comments are 9/3437 = 0.3% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Decision 4 is the first blocker of most of the 7,176: a generic theorem cited at `[i]` brings its `OFCLASS` premise.
- `IFOL.TrueI` stops at logic (a scratch print, not kept): `lower` reports only the named theorems' refusals.
- `exists_intro` at `isaBound(k, i)` concludes `ifolEx(i, …)` while Fol writes `folExists`: it matters at the step that
  builds the ∃ rules (DESIGN §4a, prerequisite 1).
- The 4 definitions not reaching their owner are at a type variable (no owner): not broken down.
- The rest of the reference's `docs/FOUNDATION.md`, and its `base/`, can be taken whole. The object-level border could
  not: it needed two adaptations to this branch (DESIGN §4a "Expand", point 6). Not checked.

## 6. Open decisions
- **Logic's step** — next in the plan's order (D2): its owner rows exactly, what it provides and assumes.
- **Decision 4** — no owner for 7,176, the largest group; design work.
- **The rest of the docs commit** — the reference's `docs/FOUNDATION.md` beyond the object-level border (in, adapted),
  with the stashed S1 revision (`git diff stash@{0}^1 stash@{0} -- docs/FOUNDATION.md`), and `base/` from
  `kinds-proposal`; taking it whole would bring the reference's arity-0 S4, which the border's `AC18` argument was
  adapted around. Awaiting the user's yes.

## 7. Next action
Write Logic's step in `DESIGN.md` §4a — its owner rows exactly, what it provides and assumes (Expand's row among its
assumptions) — and get it agreed; no code before. Done when the user agrees it.
