# STATE — isa2fol
The commit "STATE: handoff — the unit and its citations built (52a35e4e); …" · primitives · 2026-10-14.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `STATE: handoff — the unit and its citations built (52a35e4e); next, Expand's contract` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `git stash list \| head -1` | `stash@{0}: On kinds-proposal: S1 a λ is a wrapper: FOUNDATION + DESIGN Step (4) revised …` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `3336` |
| `ls Sources/Lowering \| tr '\n' ' '` | `Expand.swift Fol.swift Logic.swift Plan.swift Reify.swift Typing.swift` |
| `grep -m1 '^## Patterns' docs/SOURCE_SURFACE.md` | `## Patterns (2592)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 114, 16, 84, 14 tests |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, branched from `caaa0e16` (2026-09-29). **`kinds-proposal` (`21ca100f`)
is the REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged — kept where it did well, improved where a
principle faults it. Its principles are this branch's: `CLAUDE.md` "Design rules".

## 2. Read these first-hand
- `DESIGN.md` §4a "Lowering's components" and "The unit and its citations" — the division (Typing a registry, no pass),
  the pass-sets interface, the owner of each pattern, what the reader provides, how a lemma is cited, added, proved and
  linked; point 4 (EX and UNIQ by one walk over a term) is agreed and Reify's own step.
- `Sources/IR/Pass.swift` — `Run`: `lower` (unbuilt refusals, definitions handed to their owner, lemmas added), `prove`
  (the registry after its pass), `linked` (citations, cycles, refusals carried to citers).
- `Sources/Lowering/Typing.swift`, `Fol.swift`, `Plan.swift` — the registry routing to provers; Fol's ONE switch over
  `Pattern` (binders, instances, variables and guards of variables at `i`); the plan and `pipeline`.
- `Sources/Reader/Reader.swift` — `unit()`, `definition(of:at:)`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a pattern has at most one owner | `PipelineError.twoOwners`; `twoPassesOwningOnePatternStopTheRun` |
| a pattern no pass owns stops its statement before the first pass; one a pass owns unbuilt, at that pass | `aPatternNoPassOwnsIsRefusedBeforeTheFirstPassNamingEveryOne`, `aPatternItsPassHasNotBuiltIsRefusedAtThatPass` |
| no pattern survives its owner or comes back after it | `PipelineError.survived`; `aPatternThatSurvivesItsOwnPassStopsTheRun`, `…WrittenBackStopsTheRun` |
| a citation of a theorem or a lemma names a statement, by ID; a statement citing a refused one falls, transitively | `linked`; `aStatementCitingARefusedOneIsRefusedTransitively`, `aCitationOfNoStatementStopsTheRun`, `aCycleOfCitationsStopsTheRun` |
| a lemma is added once, after the pass citing it, in the registry's vocabulary, and lowered with its citers as one node | `aLemmaTwoStatementsCiteIsAddedOnceAndLoweredWithBothAsOneNode`, `aLemmaHoldingAPatternAPassBeforeTheRegistryOwnsStopsTheRun` |
| a lemma is proved by the one prover owning its request, or refused there | `TypingTests`; `aLemmaItsProverHasNotBuiltIsRefusedThereAndItsCitersFall` |
| a definition is handed to the pass owning its constant, as it stands at that pass's input | `aPassReadsTheDefinitionsOfTheConstantsItOwnsAsTheyStandAtItsInput` |
| what the pipeline keeps is fol-zfc | `legalize` after the last pass; `aPatternNoPassOwnsWrittenByAPassFailsAtTheEnd` |
| the reader emits only the isa and both dialects; a gap in the dialect STOPS the read | `theReaderEmitsOnlyTheIsaDialect`; `DialectGap` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests, `MEM=32G` read and lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **EACH COMPONENT MINDS ITS OWN BUSINESS** (user, 2026-10-13/14): Typing is no pass — the registry, the guards, the
  typing lemmas, discharges and helpers; Reify states and proves EX and UNIQ and nothing more; each lemma is proved by
  the component that states it.
- ⚠ **A PASS NEVER WRITES A PATTERN IT OWNS.** Fol writes `set(folBound(0))`, never `set(isaBound(0, i))`.
- ⚠ **A VARIABLE BECOMES `folBound` ONLY AT `i`, ONLY IN FOL.** A class variable relabelled early reads as a set.
- ⚠ **A DEFINITION IS WRITTEN IN TWO FORMS**: `c ≡ λx. b`, and `primrec`'s applied `c(x) ≡ b` over the axiom's frees.
- ⚠ **`Unit(table: t, statements: [try citing(…, &t)])` COPIES `t` BEFORE THE INTERN** (rule 13): build the statements first.
- ⚠ **A BUILT RULE NEVER REFUSES.** Only the pipeline refuses, before a pass, and the registry, for a lemma.
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.
- ⚠ **A λ IS A WRAPPER, NOT A CONSTANT `L` STATEMENTS NAME** (the reference's discarded amendment lost 52 ZF theorems).

## 4. State
| claim | verified by |
|---|---|
| `lower`: 0 of 9,420 lowered; refused at no owner 7,178, expand 1,048, logic 133, reify 1,061; none reaches Fol; read 61.9 s, lowered 17.0 s | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| the unit holds 133 theorems cited outside the ZF sessions at no type arguments and 1,004 definitions; 892 reach the pass owning their constant | the same run |
| top no-owner patterns: `use(theorem, [i], o)` 6,040, `isaOfClass(i)` 6,039, `use(definition zf, [], o)` 1,544, `isaFree(i)` 1,489 | the same run |
| `Lowering.pipeline`: expand, logic, reify, fol; Typing's registry after reify, with no prover | `thePlanIsTheDesignsOrder` |
| comments are 9/3336 = 0.3% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Decision 4 is the first blocker of most of the 7,178: a generic theorem cited at `[i]` brings its `OFCLASS` premise.
- `exists_intro` at `isaBound(k, i)` concludes `ifolEx(i, …)` while Fol writes `folExists`: it matters at the step that
  builds the ∃ rules (DESIGN §4a, prerequisite 1).
- Of the 112 definitions not reaching their owner, most are at a type variable (no owner) or hold Expand's or Logic's
  unbuilt patterns: not broken down.
- `base/` and `docs/FOUNDATION.md` from the reference can be taken whole; not checked against the new lowering.
- Expand can cite `Pure.reflexive` at a definition's type without the reader: the cited equation's own head is `≡` at
  that type, and the η-long bound variable is the table's (the reader's `etaLong`, moved to IR). Not checked against
  the export's 892 definitions that reach their owner.

## 6. Open decisions
- **Expand's contract**: its owner rows exactly, what it provides and assumes (DESIGN "The unit and its citations",
  "Then Expand"). Not discussed with the user yet.
- **Decision 4** — no owner for 7,178, the largest group; design work.
- **The rest of the docs commit** — `docs/FOUNDATION.md` with the stashed S1 revision
  (`git diff stash@{0}^1 stash@{0} -- docs/FOUNDATION.md`), `base/` from `kinds-proposal`. Awaiting the user's yes.

## 7. Next action
Write Expand's step in `DESIGN.md` §4a — its owner rows exactly, what it provides and assumes — and get it agreed;
no code before. Done when the user agrees it.
