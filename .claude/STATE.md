# STATE — isa2fol
b93a030a (+ this file) · primitives · 2026-10-13.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log --oneline -2 \| tail -1` | `b93a030a Input layer: axioms and constants as typed values, a pattern a primitive at its type` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `git stash list \| head -1` | `stash@{0}: On kinds-proposal: S1 a λ is a wrapper: FOUNDATION + DESIGN Step (4) revised …` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `2817` |
| `ls Sources/Lowering` | `Guard.swift` |
| `grep -m1 '^## Patterns' docs/SOURCE_SURFACE.md` | `## Patterns (2592)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 112, 7, 67, 14 tests |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, branched from `caaa0e16` (2026-09-29). **`kinds-proposal` (`21ca100f`)
is the REFERENCE**: consulted (`git show kinds-proposal:PATH`), never merged — what it did well is kept, what a principle
faults is improved (the ledger in `DESIGN.md` §4.3b). Its principles are this branch's: `CLAUDE.md` "Design rules".

## 2. Read these first-hand
- `CLAUDE.md` "Design rules" — D1–D3, I1–I3: what every change must satisfy; I3 is the next step's subject.
- `DESIGN.md` §4.3b — the input layer as built: the ledger (kept / improved, and why), the contracts, the ONE reading
  function, the pattern rule, the census, and where the build departs from the agreed text (`isaFree(.hidden, T)`).
- `Sources/IR/Constant.swift`, `Sources/IR/Pattern.swift` — the vocabulary every pass will switch over.
- `Sources/Reader/Constants.swift` (`reading`, `define`), `Sources/Reader/Census.swift` (the closure).
- `docs/SOURCE_SURFACE.md` — the 2,592 patterns the reader emits: the pieces D1 owes a rule each.

## 3. Invariants
| invariant | enforced by |
|---|---|
| the reader emits only the isa and both dialects; every constant and citation is a typed value | `theReaderEmitsOnlyTheIsaDialect`; the types |
| a leaf FOL has reads as its node; a defined constant as defined (`↔ ¬ PROP` included) | `theCoveredLeavesReadAsFolNodesAndADefinedConnectiveAsDefined`, `truepropIsErasedAndPropIsADefinedConstant` |
| a gap in the dialect (an unlisted leaf or axiom of the foundation) STOPS the read, never refuses | `DialectGap`; `anUnlistedLeafOfTheFoundationStopsTheRead`, `anUnlistedAxiomOfTheFoundationStopsTheRead` |
| the census counts the reader's own output, never a separate walk of the export | `Reader.census()`; `CensusTests.swift` |
| a unit is valid only when the checker exits 0 AND stderr is empty; `Conditional` is never `Proved` | `CLAUDE.md` "Verification" |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests and census, `MEM=32G` read and lower) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** An input layer copied from it (name lists, `Pattern` printed as a report)
  was rejected (reflog `2f26918a`). Derive each piece from a principle; record what was kept and why.
- ⚠ **`t[try t.intern(…)]` READS `t` BEFORE THE INTERN** (rule 13): an index out of range when the node is new. Bind first.
- ⚠ **A λ IS A WRAPPER, NOT A CONSTANT `L` STATEMENTS NAME** (kinds-proposal's discarded amendment: 52 ZF theorems lost
  at compound parameters, ~400 steps per instance).
- ⚠ **NO PROVIDER FOR A CONSUMER THE CORPUS HAS NOT CHECKED** — kinds-proposal's Steps 2–3 (~300 lines) gained no theorem.

## 4. State
| claim | verified by |
|---|---|
| `read` proves all 9,420 named and the 200 they cite outside the ZF sessions, 0 refused, ~63 s, 3.5 GB peak | `MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export` |
| the guard lowers 2,685 and refuses 6,735, all `compoundInstantiation` | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| the census: 2,592 patterns, `Pure.combination` at 281 instances; ~76 s | `isa2fol surface data/zf_export`; `grep -c combination docs/SOURCE_SURFACE.md` |
| 4 `declared` patterns occur; the 5 theory axioms reach 4–9 theorems each | `grep -c 'isaConst(declared' docs/SOURCE_SURFACE.md`; `docs/CLOSURE.md` "not ZF's" table |
| 23 named theorems state a type variable; a citation at an unbound one stops the read | `docs/CLOSURE.md` "Type variables"; `aCitationAtATypeVariableTheProofDoesNotBindStopsTheRead` |
| comments are 8/2817 = 0.3% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- `isaFree(.hidden, _)` never occurs in a statement of the export: reasoned from `standard_hidden_terms` (the proposition
  is left untouched), pinned only on a fixture (`aVariableOnlyTheProofUsesIsTheHiddenVariable`).
- A theorem resting on a theory's own axioms becomes, in lowering, one conditional on them, its parameters universally
  quantified; not designed.
- `base/` and `docs/FOUNDATION.md` from the reference can be taken whole (kernel-checked, or mathematics). Not checked:
  whether a `base/` tier assumes an encoding the new lowering will not use.
- The reference's jobs (`dc3b8bc1`) and compress (`2c49fbb9`) were measured sound there; they come back re-derived when a
  step needs them, not copied.
- #10, β at a compound argument the λ drops or copies, is S1's naming of the argument; unresolved.

## 6. Open decisions
- **Go-ahead for the pass-sets interface** (asked, unanswered): how a pass states the `Pattern` sets it takes and gives,
  dispatches by one exhaustive switch over them, and where the sets are checked (I3; `DESIGN.md` §4.3b 4, last paragraph).
- **The rest of the docs commit** — `docs/FOUNDATION.md` with the stashed S1 revision
  (`git diff stash@{0}^1 stash@{0} -- docs/FOUNDATION.md`; `git stash show -p … -- PATH` errors), `base/` from
  `kinds-proposal`. Awaiting the user's yes.

## 7. Next action
On the user's go, write the pass-sets interface into `DESIGN.md` — D2: the contract before code — and agree it with the
user. Done when the user has agreed it; no code before.
