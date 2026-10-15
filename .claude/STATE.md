# STATE — isa2fol
HEAD "Class existence's prover: a formula's class of records from base's rows, read back exact; one lift per class-taking
constant" · primitives · 2026-10-15.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Class existence's prover: a formula's class of records from base's rows, read back exact; one lift per class-taking constant` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `7511` |
| `ls Sources/Lowering \| tr '\n' ' '` | `Base.swift Chain.swift Classes.swift Comprehension.swift Congruence.swift Expand.swift Facts.swift Fol.swift Graph.swift Instance.swift Logic.swift Plan.swift Provers.swift Reify.swift Scope.swift Terms.swift Tuple.swift` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed, in any order: 121, 105, 75, 28, 14 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 13 tiers, each `exit 0  stderr 0`; `tuples` Proved (26), `classes` Proved (65), `metafun` Proved (17), `zf` Proved (6) |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream. Class existence is built and committed: every lemma the
corpus requests is proved; the named theorems stop at other pieces (§4). **`kinds-proposal` (`21ca100f`) is the
REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged.

## 2. Read these first-hand
- `DESIGN.md` "Class existence — its prover" — the plan, then **Built**, **Decisions made in the build** (ten, reviewed)
  and **Measured**.
- `DESIGN.md` "Lowering's components", the owner table — which pieces have no owner yet, and whose question each is.
- `Sources/Lowering/Comprehension.swift` — `Comprehension` builds a formula's classes of records in the top frame;
  `Reading` reads each back exact in a frame fixing a `Record`.
- `Sources/Lowering/Classes.swift` — `ClassProver`: `CLASS ⟨λ⟩`, `c_CLASS` (a set constant's a singleton), `c_LIFT`,
  `REKEY_m`.
- `Tests/LoweringTests/ClassTests.swift` — each lemma kind proved and kernel-checked.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a lemma's proof concludes its statement by ID, before Fol and after | `ClassError.misproved`, `ReifyError.misproved`, `TupleError.misproved`; `PipelineError.unproved`; `proveAll` in `Proving.swift` |
| every node the generator reads concludes `elem(a, A) ↔ φ` at the formula given | `ComprehensionError.misread`, checked at each node in `Reading.read` |
| every hypothesis is its binder's | `misscoped` in `proveAll` (the table does not check it) |
| every generated lemma kind is Proved by the real checker from base | `kernelChecks` in `ClassTests`, `ProverTests`, `TupleTests` |
| a pattern has at most one owner; a lemma at most one prover | `PipelineError.twoOwners`, `ProversError.owners` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests and base, `MEM=32G` lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13), for a `Table`, a `Chain`, a `Frame`
  AND an argument list: `lowered(t, try f(&t))` passes `t` before `f` writes it. Bind first.
- ⚠ **A PROOF BUILT OUTSIDE AN ASSUMPTION IS NEVER REUSED INSIDE IT** — nor at a scope a walk goes under: an equation
  captured by a hole closure is rebuilt at the hole's scope (`ClassProofs.carried`). Rebuild from levels, or `have` it.
- ⚠ **`Reading.record` OPENS ITS PREFIXES, FIXING A VARIABLE PER ENTRY**: a formula taken in the frame before it is
  that many levels shallow. `extend` only `have`s.
- ⚠ **A SET CONSTANT'S CLASS BINDS A SET, `∃ᵢS`**: `exists_intro` keeps an isa witness `isaBound` under a fol binder.
- ⚠ **A NAMING IS NEVER CLOSED AROUND ITS OWN VALUE**: `exists_intro` abstracts every occurrence of its witness.
- ⚠ **A FOL-ZFC VARIABLE IS UNTYPED** in an instance (`Sources/IR/Index.swift`).
- ⚠ **A PATTERN `case let .x(a, b) = p2` REBINDS, IT DOES NOT COMPARE**: write `case .x(let a, b)` to match `b`.
- ⚠ **A RESERVED WORD IN ANY SEGMENT OF A NAME BREAKS THE CHECKER'S LEXER** (`T.use`); `checkName` refuses it.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a second "STATE: handoff" commit (user, 2026-10-03).
- ⚠ **A COMPONENT IS HOW THE CODE IS ORGANIZED, NEVER A FRAMEWORK NOTION** (user, 2026-10-14).
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 59 of 9,420 lowered; 1,866 other statements reach fol-zfc; 451 `@def`s stated, 107 refused; 0 lemmas refused unbuilt; named refused: no owner 7,176, logic 924, letter off spine 94, cites a refused statement 1,167 (940 statements, `Formula.satisfies_DEF` first, no EX) | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` (2 min 11 s, peak 13.0 GB by `/usr/bin/time -v`) |
| patterns held by the refused, a statement counted under each it holds: no owner — `use(theorem, [i], o)` 6,040, `isaOfClass(i)` 6,039, `use(definition zf object, [], o)` 1,542, `isaFree(i)` 1,489; logic, unbuilt — `isaAllElim(o, (i => i))` 458, `isaAllElim(o, (i => o))` 351 | the same run's per-pattern lists |
| the 1,866: 165 `_CLASS`, 99 `CLASS_`, 27 `_LIFT`, 2 `REKEY_`, 278 `EX_`, 338 `UNIQ_`, 451 `_DEF`, 147 `_AGREE`, 106 `_FUNC`, 100 `_TOTAL`, 73 `FUNC_`, 19 `_EX`, 19 `_UNIQ`, 15 `TUPLE_`, 27 other | a throwaway count of `unit.statements` names, not kept; re-derive the same way |
| comments are 27/7511 = 0.4% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- How many named theorems lower once any one blocker is built is unknown: the counts overlap, and a statement holding
  several needs all of them.
- The corpus's class-existence proofs are as valid as the tests' — only the tests' are kernel-checked; emission, and so a
  corpus-wide check and the proofs' rendered size, is unbuilt.
- No lemma the corpus requests reaches a class quantifier in a definition body (the run would have thrown
  `ComprehensionError.unread`); one that does needs a refusal design, not a fallback.

## 6. Open decisions
The step after class existence (`DESIGN.md` "Lowering's components", the owner table):
- **A theorem cited at a type instance** (`use(theorem, [i], o)` with `isaOfClass(i)`; §4a decision 4, deferred): held
  by the most refused statements.
- **A ZF definition cited at the object level** (`use(definition zf object, [], o)`): no owner yet.
- **An instance at a class type** (Lambda's, owned and unbuilt): logic's largest refusals.
- **Emission**: lowers nothing new, but kernel-checks every built proof on the corpus and measures its size.
The first three extend what lowers, by overlapping counts; emission verifies what is built.

## 7. Next action
Ask the user which §6 step comes next; done when one is chosen — its design is then agreed decision by decision before
any code.
