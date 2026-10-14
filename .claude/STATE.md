# STATE — isa2fol
The commit "Logic: a proposition at a statement's top a schema letter; …" · primitives · 2026-10-14.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Logic: a proposition at a statement's top a schema letter; the logic's propositional axioms the kernel's steps` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `git stash list \| head -1` | `stash@{0}: On kinds-proposal: S1 a λ is a wrapper: FOUNDATION + DESIGN Step (4) revised …` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `3623` |
| `ls Sources/Lowering \| tr '\n' ' '` | `Expand.swift Fol.swift Logic.swift Plan.swift Reify.swift Typing.swift` |
| `grep -m1 '^## Patterns' docs/SOURCE_SURFACE.md` | `## Patterns (2597)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed, in any order: 116, 91, 33, 15, 14 tests |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, branched from `caaa0e16` (2026-09-29). **`kinds-proposal` (`21ca100f`)
is the REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged — kept where it did well, improved where a
principle faults it. Its principles are this branch's: `CLAUDE.md` "Design rules".

## 2. Read these first-hand
- `DESIGN.md` §4a "Logic" — the rows exactly (point 5), the letter's grammar (2), and point 7: why Pure's `≡` and rules
  at a function type, and at `i`, wait, and what they need (a context's congruence per formula; base's `eq_*`).
- `Sources/Lowering/Logic.swift` — `piece`: the one switch, its unbuilt rows; `proof`: the kernel's 15 shapes.
- `Sources/IR/Legalize.swift` — `misplacedLetters`: where a letter may stand, checked once after the last pass.
- `docs/FOUNDATION.md` §2 S4 (a schematic `P :: o` is a schema letter) and §3b's mapping; `base/tiers/cong.fol.def`,
  the connectives' congruence schemas the next step would chain.

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
| a defined constant keeps its declared level; `unfolds(family, level)` is the one border Expand's and Reify's switches read | `aDefinedConstantKeepsItsDeclaredLevel`, `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a binder, its intro and its variable at `o` are fol-zfc's schema letter, no pass's | `eachPatternBelongsToTheIsaDialectTheFolDialectOrBoth`, `eachPatternHasTheOwnerTheDivisionGivesIt` |
| an elimination at `o` reduces on a ⋀-intro, else is `folSchemaInst`; each of the 16 propositional axioms is the kernel's proof of its statement, by ID | `LogicTests` |
| a letter stands only on its spine; a statement holding one elsewhere is refused `letterOffSpine` after the last pass | `LegalizeTests`; `aStatementHoldingALetterOffItsSpineIsRefusedAfterTheLastPass` |
| what the pipeline keeps is fol-zfc | `legalize`; `theLogicsOwnTheoremIsLoweredAsASchemaProvedByTheKernelsStep` |
| the reader emits only the isa and both dialects; a gap in the dialect STOPS the read | `theReaderEmitsOnlyTheIsaDialect`; `DialectGap` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests, `MEM=32G` read and lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **EACH COMPONENT MINDS ITS OWN BUSINESS** (user, 2026-10-13/14): Typing is no pass; Reify states and proves EX and
  UNIQ and nothing more; each lemma is proved by the component that states it.
- ⚠ **A PASS NEVER WRITES A PATTERN IT OWNS.** Fol writes `set(folBound(0))`; Logic writes a letter's ⋀-intro, no pass's.
- ⚠ **A VARIABLE BECOMES `folBound` ONLY AT `i`, ONLY IN FOL.** A class variable relabelled early reads as a set.
- ⚠ **A LETTER'S PLACE IS POSITIONAL; PATTERN OWNERSHIP CANNOT SEE IT.** It is fol-zfc's grammar, checked once by
  `misplacedLetters` after the last pass. Never refuse by position inside a pass.
- ⚠ **READING EVERY BOX AT ITS INSTANCE BLOWS UP**: a scratch reader passed 20 GB and 8 minutes against 4.3 GB and 88 s
  (DESIGN "Logic", point 3). β at `o` is Logic's, on a ⋀-intro only; a redex at `i` stays.
- ⚠ **A DEFINITION IS WRITTEN IN TWO FORMS**: `c ≡ λx. b` (IFOL's, FOL's), and the applied `c(x) ≡ b` over the
  axiom's frees — ALL of Pure's (`prop_def`, `conjunction_def`, `term_def`) and `primrec`'s. `parameters` tells them apart.
- ⚠ **`Definition.reflexive` IS NEVER LOWERED**: the pipeline lowers `definiens` alone; only Expand, first, reads it.
- ⚠ **A ZF CONSTANT DECLARED AT THE META LEVEL IS NEVER NAMED** (FOUNDATION §2): `split`, `qsplit`, `MetaExists.ex`,
  `L_Reflects`, `AC18` unfold in Expand; the level is kept on the constant (`Defined.level`), never inferred from a use.
- ⚠ **`Unit(table: t, statements: [try citing(…, &t)])` COPIES `t` BEFORE THE INTERN** (rule 13): build the statements first.
- ⚠ **A BUILT RULE NEVER REFUSES.** Only the pipeline refuses — before a pass, and after the last for a letter off its
  spine — and the registry, for a lemma.
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.
- ⚠ **A λ IS A WRAPPER, NOT A CONSTANT `L` STATEMENTS NAME** (the reference's discarded amendment lost 52 ZF theorems).

## 4. State
| claim | verified by |
|---|---|
| `lower`: 3 of 9,420 lowered (`ZF_Base.strip.1`, `func.basic_monos.2`, `.4`) and 23 theorems cited outside; refused at no owner 7,176, logic 558, reify 1,631; 52 cite a refused statement (`IFOL.TrueI` 51, `FOL.disj_mono` 1) | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| top logic patterns: `ifolAll((o => o), body: o)`, `isaAllElim(o, (o => o))`, `≡` at `o ⇒ o`, `use(axiom Pure.combination, [o, o], o)` 416 each; `Pure.reflexive` at `[o ⇒ o]` 412 | the same run |
| `Lowering.pipeline`: expand, logic, reify, fol; Typing's registry after reify, with no prover | `thePlanIsTheDesignsOrder` |
| comments are 9/3623 = 0.2% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- 68 of the 520 that pass Logic hold a letter off its spine (`&&&`, `TERM`, `ex` unfolded; a box behind a redex at
  `i`; a `⋀`-premise): a scratch survey, not kept. Today they stop at reify; `letterOffSpine` names them once Reify passes.
- The congruence at a propositional context is chainable from `base/tiers/cong.fol.def`'s schemas, per formula.
- Decision 4 is the first blocker of most of the 7,176: a generic theorem cited at `[i]` brings its `OFCLASS` premise.
- `exists_intro` at `isaBound(k, i)` concludes `ifolEx(i, …)` while Fol writes `folExists`: it matters at the step that
  builds the ∃ rules (DESIGN §4a, prerequisite 1).
- Why `FOL.disj_mono` is refused: not determined (`lower` reports only the named theorems' refusals).

## 6. Open decisions
- **Logic's next step or Reify's** — Logic's 558: Pure's `≡` and rules at a function type, and at `i` (DESIGN "Logic",
  point 7); Reify's 1,631: its step, against Logic's contract as built. The plan's order (D2) suggests Logic's first.
- **Decision 4** — no owner for 7,176, the largest group; design work.
- **Boxes behind a redex at `i`** — β through one is a shape (D1); reading boxes at their instance blows up.
- **The rest of the docs commit** — FOUNDATION's arity-0 S4 is taken (this step); the reference's later paragraphs
  (a proposition in a class position, a variable taking a class) and `base/` from `kinds-proposal` await the user's yes.

## 7. Next action
Draft Logic's next step in `DESIGN.md` §4a — Pure's `≡` and rules at a function type and at `i` — its rows, what it
provides and assumes; no code before. Done when the user agrees it.
