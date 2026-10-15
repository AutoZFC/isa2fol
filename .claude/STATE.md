# STATE — isa2fol
The commit "Logic: Pure's equality as the kernel's steps; Reify: S1 at the site — …" · primitives · 2026-10-14.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Logic: Pure's equality as the kernel's steps; Reify: S1 at the site — a term named where it stands, a constant's @def, an instance at a compound term` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `git stash list \| head -1` | `stash@{0}: On kinds-proposal: S1 a λ is a wrapper: FOUNDATION + DESIGN Step (4) revised …` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `5034` |
| `ls Sources/Lowering \| tr '\n' ' '` | `Base.swift Chain.swift Expand.swift Fol.swift Instance.swift Logic.swift Plan.swift Provers.swift Reify.swift Scope.swift Tuple.swift` |
| `grep -m1 '^## Patterns' docs/SOURCE_SURFACE.md` | `## Patterns (1518)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed, in any order: 121, 103, 55, 24, 14 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 13 tiers, each `exit 0  stderr 0` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, branched from `caaa0e16` (2026-09-29). **`kinds-proposal` (`21ca100f`)
is the REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged — kept where it did well, improved where a
principle faults it. Its principles are this branch's: `CLAUDE.md` "Design rules".

## 2. Read these first-hand
- `DESIGN.md` §4a "Reify — S1 at the site" — the agreed design, then **Built** (the refinements made in the build, for
  the user's review) and **Measured**.
- `Sources/Lowering/Reify.swift` — `owns`, `Naming` (one `Chain` per atom, a `designated` path recording a unit's
  binders), `classDefinition`, `ReifyProver.define`.
- `Sources/Lowering/Instance.swift` — `TermInstance.proof`; `Conversion.step`: each side opened, the other closed at its
  witnesses; `returning` (UNIQ, `eq_trans`, `eq_symm`).
- `Sources/Lowering/Scope.swift` and `Logic.swift`'s `Replacement` — a proof built by levels; the one replacement walk.
- `Sources/Lowering/Fol.swift` — `Entry` and `discharge`: the output's binders, a guard found between its fix and the next.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a pattern has at most one owner | `PipelineError.twoOwners`; `eachPatternHasTheOwnerTheDivisionGivesIt` |
| Reify's pieces are the logic pass's, as Reify's switch answers them; Reify's switch claims none of Logic's | `reifysPiecesAreTheLogicPasss` |
| each piece is named where it stands, one variable per occurrence, by ID; naming commutes with an instance at a variable | `ReifyTests` |
| an instance at a compound term concludes Isabelle's formula named, by ID, through Logic and Fol, citing EX and UNIQ of the term | `anInstanceAtACompoundTermConcludesIsabellesFormulaNamed`, `anInstanceAtAnAppliedFunctionVariableDischargesItsGuard`, `anInstanceInsideALambdaKeepsItsClass` |
| a `@def` is stated from the definition as Expand left it, its class parameters outside the tuple; a definition holding a pattern no pass owns or one a pass leaves unbuilt refuses its `@def` before the registry, read under its parameters | `aConstantsDefinitionIsItsClassFromItsDefinition`, `aDefinitionHoldingAnUnbuiltPatternIsRefusedBeforeTheRegistry`, `aDefinitionsClassParameterIsItsDefinitionsVariable` |
| Fol guards every object binder by its type (`set`, `function`, none) and `∃` at `i`; a variable beyond objects is Fol's, unbuilt | `FolTests`, `eachPatternHasTheOwnerTheDivisionGivesIt` |
| an `∃` at an isa binder is `isaExIntro`/`isaExElim`; fol-zfc's `∃` steps take fol-zfc's binder only | `existentialStepsAtAnIsaBinderAreTheIsaSteps` |
| a pattern no pass owns stops its statement before the first pass; one a pass owns unbuilt, at that pass | `PipelineTests` |
| no pattern survives its owner; each proof concludes its statement by ID after every pass | `PipelineError.survived`, `.unproved` |
| a citation, or a constant's class predicate, links to a statement or a `@def`; a statement citing a refused one falls | `linked`; `PipelineTests` |
| base is cited by its parsed text; every base tier is kernel-checked | `ParseTests`; `scripts/check-base.sh` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests and `check-base.sh`, `MEM=32G` read and lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13), for a `Table` and a `Chain` alike:
  `chain.predicate(…, [try tupled(…)])` and `ys.chain.formula(try ys.atom(…))` both read binders not yet bound. Bind first.
- ⚠ **A DEFINITION'S PARAMETERS ARE ITS `@def`'S VARIABLES, NO PIECE OF ITS BODY**: read with its leading λs, a class
  parameter is "a λ beyond objects", Logic's unbuilt, and every `@def` with a class argument falls
  (`aDefinitionsClassParameterIsItsDefinitionsVariable`).
- ⚠ **A VARIABLE BEYOND OBJECTS IS FOL'S, UNBUILT — NEVER NO OWNER**: unowned, a meta definition holding one is dropped,
  and Expand then meets its constant in another definition and stops the run (`MetaExists.ex`).
- ⚠ **A RULE'S PREMISES ARE THE RULE'S, NEVER ITS INSTANCE'S**: `equal_elim` at `B := C ⟹ D` takes two premises.
- ⚠ **AN EQUATION BETWEEN FUNCTIONS IS OWNED, NEVER NO-OWNER**: only Expand, after the no-owner check, removes one.
- ⚠ **A COMPONENT IS HOW THE CODE IS ORGANIZED, NEVER A FRAMEWORK NOTION** (user, 2026-10-14).
- ⚠ **NO RULE WRITES A PATTERN ITS PASS OWNS**; never an unnamed term after logic.
- ⚠ **A λ IS NAMED WHERE IT IS CONSUMED, NEVER AT ITS OWN NODE**: one bottom-up walk reaches the λ first.
- ⚠ **A BUILT RULE NEVER REFUSES.** Only the pipeline refuses, and the registry for a lemma.
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 59 of 9,420 lowered; 451 `@def`s stated, 107 refused; 400 EX/UNIQ refused, unbuilt; refused named: no owner 7,176, logic 924, letter off spine 94, cites a refused statement 1,167 | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| the most frequent stop at logic is Lambda's instance at a class type, `isaAllElim(o, (i => i))` 458 | the same run |
| `read` proves all 9,420 named theorems | `MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export` |
| comments are 18/5034 = 0.4% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The instance's conversion throws `LogicError.context` on a `⋀` at a class type inside `φ`; the corpus run met none,
  but nothing rules one out.
- Most of the 1,167 citing a refused statement fall on EX/UNIQ alone, so EX's and UNIQ's prover lowers many at once.
- Decision 4 is the first blocker of most of the 7,176: a generic theorem cited at `[i]` brings its `OFCLASS` premise.

## 6. Open decisions
- **The build's refinements await review** (`DESIGN.md` "Reify — S1 at the site", Built): EX and UNIQ per term with
  fingerprint names; UNIQ in chain form; lemma variables as fol-zfc's `∀`; `isaExIntro`/`isaExElim`; a `@def`'s
  definition read under its parameters.
- **Next step** — EX's and UNIQ's prover (class existence per formula, R5; the λ's class lemma), or Lambda's instance at
  a class type (458 at logic), or Logic's equality at objects.
- **Decision 4** — no owner for 7,176, the largest group; design work.

## 7. Next action
The user reviews the build's refinements and chooses the next step. Done when one is agreed in `DESIGN.md`.
