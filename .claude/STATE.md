# STATE — isa2fol
HEAD "Emission: the unit as parts, each kernel-checked against the libraries of what it cites; a walk carries a binder
by its schema" · primitives · 2026-10-15.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `Emission: the unit as parts, each kernel-checked against the libraries of what it cites; a walk carries a binder by its schema` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `7895` |
| `ls Sources/FolDialect \| tr '\n' ' '` | `Declaration.swift Emit.swift Parse.swift Render.swift` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed, in any order: 121, 105, 76, 41, 14 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 13 tiers, each `exit 0  stderr 0`, Proved n of n; `cong` Schemas proved (10 of 10), `classes` Proved (65 of 65) |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`, then `MEM=32G scripts/capped.sh bash scripts/check-unit.sh DIR` | 39 parts; summed, claims 1445 of 1445, schemas 29 of 29; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream. Emission is built and the corpus's unit is
kernel-checked. The checker, `~/repos/fol-zfc-comb`, is on branch `libraries-and-streaming` at `224d60e` (`--lib`, streamed
proof files, the library writer's fix, quoted name segments), not merged into `comb-verifier`, not pushed; its
`bazel-bin/src/tools/proof_checker` is that commit's `-c opt` build. **`kinds-proposal` (`21ca100f`) is the REFERENCE**:
consulted (`git show kinds-proposal:PATH`), never merged.

## 2. Read these first-hand
- `DESIGN.md` "The steps after class existence, in order" — the agreed order; step 1 is next.
- `DESIGN.md` "Emission — the unit as text, checked by the kernel" — decisions 1–3, **Built**, **Decisions made in the
  build** (seven, for the user's review) and **Measured**.
- `Sources/FolDialect/Emit.swift` — parts, a statement's placement, each part's loads, the report.
- `Sources/FolDialect/Render.swift` — `step` (what is written once, and until when), `schemaInstance`, `spelled`.
- `Sources/Lowering/Logic.swift` — `Replacement.quantified`: a binder's equivalence proved once.
- `scripts/check-base.sh` (`checked`, the validity rule) and `scripts/check-unit.sh`.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, and Proved and Schemas proved list every claim and schema it declares; a part citing an invalid one is not checked | `checked` in `scripts/check-base.sh`; `scripts/check-unit.sh` |
| `Conditional` is never `Proved` | `checked` compares counts; `CLAUDE.md` "Verification" |
| a walk is linear in its binders | `aQuantifierCongruenceIsLinearInItsBinders` (`WalkTests`) |
| a step is written once while citable; a node is not a fact | `EmissionTests` (four sharing tests, kernel-checked) |
| a lemma's proof concludes its statement by ID, before Fol and after | `ClassError.misproved`, `ReifyError.misproved`, `TupleError.misproved`; `PipelineError.unproved` |
| every hypothesis is its binder's | `misscoped` in `proveAll` (the table does not check it) |
| a name base declares stops emission | `EmitError.declaredByBase`; `aNameBaseDeclaresStopsEmission` |
| every build, test, checker, read and lowering run is capped | `scripts/capped.sh` (`MEM=16G` tests and base, `MEM=32G` lower and check-unit) |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **BUILD THE CHECKER ONLY WITH `bazel build -c opt`**: a plain build repoints `bazel-bin` to fastbuild, where there is
  no `proof_checker`. An unreviewed checker change builds in a separate output base (`--output_base=… --symlink_prefix=/`).
- ⚠ **A WALK PROVES A BINDER'S EQUIVALENCE ONCE**: in both directions, under each direction's witness, the checker derives
  it twice per binder — 10¹² steps written for 1,238 distinct (`WF_absolute.rtrancl_alt_FUNC`).
- ⚠ **A NODE IS NOT A FACT**: the renderer keys a step by its node and the names its loose indices resolve to.
- ⚠ **A RESERVED SEGMENT AFTER THE FIRST IS WRITTEN QUOTED** (`Com.bexp."false"`), a first one refused: the checker's
  keyword tokens carry no spelling. The export's names were counted whole (`theory/consts`, `thms`): seven.
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13), for a `Table`, a `Chain`, a `Frame`
  AND an argument list. Bind first.
- ⚠ **A PROOF BUILT OUTSIDE AN ASSUMPTION IS NEVER REUSED INSIDE IT**: rebuild from levels, or `have` it.
- ⚠ **A FOL-ZFC VARIABLE IS UNTYPED** in an instance (`Sources/IR/Index.swift`).
- ⚠ **A PATTERN `case let .x(a, b) = p2` REBINDS, IT DOES NOT COMPARE**: write `case .x(let a, b)` to match `b`.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a second "STATE: handoff" commit (user, 2026-10-03).
- ⚠ **A COMPONENT IS HOW THE CODE IS ORGANIZED, NEVER A FRAMEWORK NOTION** (user, 2026-10-14).
- ⚠ **COPYING THE REFERENCE IS NOT DESIGNING.** Derive each piece from a principle; record what was kept and why.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 59 of 9,420 named theorems lowered, 1,866 other statements; refused: no owner 7,176, logic 924, letter off spine 94, cites a refused statement 1,167 | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| emitted: 39 parts, 1,445 claims, 29 schemas, 451 `@def`s, 71,966,989 bytes; steps written 1,033,187, as trees 1,107,750, distinct 879,656; 303 s, peak 13.4 GB, the emission 169 s | the same run with `--emit DIR` (its report) |
| kernel: every part valid — claims 1,445 of 1,445, schemas 29 of 29; 9.9 s, peak 551 MB | `scripts/check-unit.sh DIR`, summed |
| the 59 by session: ZF 9, ZF-Induct 21, ZF-Resid 12, ZF-IMP 6, ZF-Coind 5, ZF-AC 3, ZF-Constructible 2, ZF-ex 1; none cites a generated lemma — all 1,388 lemmas are in `_uncited` | the theory parts' `claim`/`schema` lines (a throwaway count, not kept); `check-unit.sh`'s `_uncited` rows |
| comments are 34/7895 = 0.4% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- A check holds one part's arena; how it grows with a theory part far larger than today's is unmeasured.
- How many named theorems lower once step 1 is built is unknown: the 6,040 theorems step 1 frees meet logic's gate.

## 6. Open decisions
- The user's review of the emission build's seven decisions (`DESIGN.md` "Emission", "Decisions made in the build").
- Step 1 of the agreed order, decision 4: its rule is decided (a `term`-restricted theorem read at `i`, `OFCLASS(i,
  term)` dropped); its owner is not — the reader (the reference's, which §4.3b's "no translation decision" forbids) or a
  lowering component.
- Merging and pushing the checker's `libraries-and-streaming` (the user's).

## 7. Next action
Open step 1's design, decision by decision, starting with its owner; done when the user agrees each decision — no
code before.
