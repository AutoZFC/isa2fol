# STATE — isa2fol
`HEAD` · `feature/exists-descent` · 2026-09-24.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is NOT on a non-login shell's PATH — it is at `~/.local/bin`.
⚠ **BENCHMARK WITH `-c release` OR THE NUMBER IS MEANINGLESS.** There is no benchmark now.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`7`** |
| `ls Sources` | `FolDialect IR isa2fol YXML` |
| `ls docs` | `FOUNDATION.md phase2_probes SOURCE_SURFACE.md` |
| `find Sources Tests -name '*.swift' \| wc -l` | `10` (285 lines) |
| comment density of `Sources` (CLAUDE.md rule 9 has the script) | `6/160 = 3.75%` — **UNDER the 5% cap** |
| `scripts/source-surface.py \| head -1` | `population: 3616 named ZF theorems, 37 ZF.* theories` |
| `grep -cE '^axiom' base/axioms.fol.def` · `ls base/tiers/*.fol.def \| wc -l` | `17` · `10` |
| `ls docs/phase2_probes/*.fol.def \| wc -l` · `ls data/zf_export \| wc -l` | `17` · `40` |
| `test -x ~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker` | exit 0 |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

Worktree `/home/arthur/repos/isa2fol`, tree CLEAN, **ahead of
`origin/feature/exists-descent`, NOT pushed** — count: `git rev-list --count origin/feature/exists-descent..HEAD`.
⚠ **THE BRANCH NAME DESCRIBES WORK THAT NO LONGER EXISTS** — see §6.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `DESIGN.md` **§2, §4** | the ZF-surface dialect; the interned table, node identity, de Bruijn + D2 shifting, D5 determinism, the proof layer — DECIDED, NOT BUILT |
| `Sources/IR/IRType.swift` | the only IR code: `i`, `o`, Pure's `prop`, `fn` |
| `~/repos/fol-zfc-comb/src/proof/nd/stack.cpp`, `src/core/formula.cpp` | the checker the design mirrors: derived-formula marking, scopes, `instantiate_gen`/`shift`/`abstract` |
| `docs/SOURCE_SURFACE.md` | the MEASURED source surface; regenerates |
| `docs/FOUNDATION.md` **§2** | S1–S6, the specification everything must satisfy |
| `CLAUDE.md` rules 1, 9, 10, 11 | no fallbacks · comment cap · never run uncapped · no `default:` |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 **AND** stderr is empty | `theRealCheckerAcceptsWhatRenderEmits` |
| No isa node and no `prop`/`fn` type survives lowering | `legalize` — NOT BUILT (`DESIGN.md` §4.5) |
| Emitted text is a function of input content | NOT BUILT — the cross-table test, `DESIGN.md` §4.6 |
| `docs/FOUNDATION.md` is mathematics, with no code reference | nothing checks it; discipline |
| Comments ≤ 5% of `Sources/**/*.swift` | the §0 row; **delete prose, never raise the cap** |

**Standing warnings — silent if repeated:**

- **⚠ `Conditional` IS NOT `Proved` AND THEY ARE NEVER SUMMED.**
- **⚠ A CLAIM WITH NO PROOF BLOCK IS NOT CITABLE.** `use X` on a declared-only
  claim fails `unknown axiom/theorem in ctx`, *not* `Conditional`, which needs
  `proof X: UNPROVED`. So the artifact must carry stubs — §6.3.
- **⚠ A REWRITE IS PARTIAL, SO ADDING A NODE KIND BREAKS NOTHING.** Rule 11's
  guarantee lives in `legalize`, and in D2's one traversal for binder kinds.
- **⚠ DO NOT RESTORE THE REGION GRAPH** (`Sources/IR` before this state) — formulas
  are interned and immutable now (`DESIGN.md` §4).
- **⚠ NEVER ITERATE A `Dictionary`/`Set` ON A PATH TO OUTPUT** — Swift seeds
  `Hasher` per process (`DESIGN.md` §4.6 R3).
- **⚠ `IRType.i` DOES NOT DISTINGUISH A SET FROM A CLASS, DELIBERATELY.** NBG is
  one-sorted. Only G5's two-sided rule can catch a guard error.
- **⚠ NOTHING CLOSES POLYMORPHISM AT THE TYPE LEVEL.** `IRType` has no `'a`; the
  reader must refuse by name, and `groundnessIsStructural` needs re-pinning.
- **⚠ A `ZVar` CARRIES NO TYPE.** A free variable's sort is in the `frees` table
  at the head of the proof file — `pair tfrees (pair frees (pair prop proof))`.
- **⚠ THE RUST-ERA DESIGN DOCS WERE DELETED — DO NOT RESTORE ONE.** They planned
  `IR1`–`IR4`, `H → S → E → LOWER`, `PassContext`, `src/replay/`, and read as
  current. `git log` finds them; `DESIGN.md` supersedes them.
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED** — its §5 says so.
- **⚠ SERIALS COLLIDE ACROSS THEORIES.** Index on `(theory, serial)`.
- **⚠ `isa2fol-build` (§1) IS A LIVE WORKTREE ON THE DELETED RUST TREE.**

## 4. State

| claim | verified by |
|---|---|
| YXML parses real export output; `render` emits what the REAL checker accepts | `aRealExportFileParses`, `theRealCheckerAcceptsWhatRenderEmits` |
| `base/axioms.fol.def` checks clean | `proof_checker base/axioms.fol.{def,proof}` → `OK: 7 claim(s)`, empty stderr |

**No IR is built beyond `IRType`**, and there is no reader.

## 5. Beliefs — NOT verified

- **197** term constants in **27** levels — `~/isabelle-object-constants.md`, which
  says of itself "no standing test handle". Live and close but not the same
  population: `source-surface.py` measures **190** `i`-valued, **55** `o`-valued.
- **794** of 868 declared proofs reach PASS S, **74** carry a βη-redex. From
  deleted Rust code; nothing reproduces it.

## 6. Open decisions

1. **The branch.** `feature/exists-descent` names deleted work; nothing pushed (§1).
   Rename, branch fresh, or merge to `main`? `isa2fol-build` still holds `rs/`.
2. **Flatten at read time, or keep the curried `ZApp` spine?** `isaAtom(String,
   [OpID])` already presumes head+args, and S1 materialises per *application* —
   against which, flattening is where the reader stops being a transcription.
3. **`UNPROVED` as `extern`.** Separate compilation needs it (§3's citability
   warning); R2 says "no debt". Ban at the final link, or per unit?
4. **What monomorphise instantiates at** — use-site type argument (faithful) or
   always `'a := i` (resolves `eq`/`All`/`Ex`/`split`, but a generic IFOL theorem
   then means only its `i`-instance, WEAKER than Isabelle's).
5. **Is the linkable interface the `.fol.def` text or the lowered graph?** Text
   needs `parse` (already required, `DESIGN.md` §3) and buys separate
   compilation; the graph needs no parser but forces one process.

## 7. Next action

**Framework design, one piece at a time, each discussed with the user BEFORE any
code.** This is not feature work. Minimal first; add slowly. Passes are
experiments — review the framework, not their bugs.

**The IR is designed on paper, `DESIGN.md` §2 and §4, and only `IRType` is built.**
Build order, each step discussed in its concrete Swift shape first, tests first:
1. the formula table — interning, immutable nodes, `looseBound`; the §4.3 node kinds
2. D2 — the five laws, then `mapVars` and shift/instantiate/abstract
3. decide whether `FolDialect.Formula` survives; then D5's level-named renderer,
   accepted by the real checker

D2 (shifting) and D5 (determinism) are decided, `DESIGN.md` §4.4, §4.6. Next to
discuss: the rest of §4.8 — S1 placement, the unit, the proof layer.

**In flight elsewhere:** the application-shape census,
`.claude/tasks/ISA_SHAPE_CENSUS.md` → `docs/ISA_SHAPES.md` on branch
`census/isa-shapes`. It TESTS the ZF-surface shape (`DESIGN.md` §2): which export
terms read into it, and which refuse.

**The reader comes after step 1**: its node kinds are §4.3's; it also needs a
positional ztyp decoder (tag 0 is both `ZConst` and `Type`). First target:
`QPair_iff` (`ZF.QPair`, serial 6958).
