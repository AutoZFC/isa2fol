# STATE — isa2fol
`HEAD` · `feature/exists-descent` · 2026-09-23.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is NOT on a non-login shell's PATH — it is at `~/.local/bin`.
⚠ **BENCHMARK WITH `-c release` OR THE NUMBER IS MEANINGLESS.** There is no benchmark now.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`14`** |
| `ls Sources` | `FolDialect IR isa2fol Lowering YXML` |
| `ls docs` | `FOUNDATION.md phase2_probes SOURCE_SURFACE.md` |
| `find Sources Tests -name '*.swift' \| wc -l` | `22` (743 lines) |
| comment density of `Sources` (CLAUDE.md rule 9 has the script) | `21/470 = 4.47%` — **UNDER the 5% cap** |
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
| `DESIGN.md` **§4, §4a** | the pass engine and the statement lowering — the two live parts |
| `Sources/IR/Op.swift` | the op enum carries its own operands; 4 switches here + `legalize` = the extension cost |
| `Sources/Lowering/Statement.swift` | the three passes, and why their order is forced |
| `docs/SOURCE_SURFACE.md` | the MEASURED source surface; regenerates |
| `docs/FOUNDATION.md` **§2** | S1–S6, the specification everything must satisfy |
| `CLAUDE.md` rules 1, 9, 10, 11 | no fallbacks · comment cap · never run uncapped · no `default:` |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 **AND** stderr is empty | `theRealCheckerAcceptsWhatRenderEmits` |
| No `isa.*` op and no `prop`/`fn` type survives lowering | `legalize` — one exhaustive switch |
| Lowering is a deterministic function of the statement | `loweringIsDeterministic` |
| `docs/FOUNDATION.md` is mathematics, with no code reference | nothing checks it; discipline |
| Comments ≤ 5% of `Sources/**/*.swift` | the §0 row; **delete prose, never raise the cap** |

**Standing warnings — silent if repeated:**

- **⚠ `Conditional` IS NOT `Proved` AND THEY ARE NEVER SUMMED.**
- **⚠ A CLAIM WITH NO PROOF BLOCK IS NOT CITABLE.** `use X` on a declared-only
  claim fails `unknown axiom/theorem in ctx`, *not* `Conditional`, which needs
  `proof X: UNPROVED`. So the artifact must carry stubs — §6.3.
- **⚠ A REGION'S VALUE IS `result`, NEVER "THE LAST OP"** — a pass that appends
  would rebind the binder, and `replaceAllUses` must maintain `result` too. Its
  SCOPE, though, is represented and not enforced: an op outside a region may
  reference that region's `blockArg` and no verifier objects.
- **⚠ A REWRITE PATTERN IS PARTIAL, SO ADDING AN `Op` CASE BREAKS NOTHING.**
  Rule 11's guarantee lives in `legalize` alone.
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
| A mixed isa/fol graph lowers to fol-zfc-only | `theStatementLoweringAddsTheGuard` |
| `⋀x. φ` becomes `∀x. (set(x) → φ)` — the statement's SHAPE changes | `theGuardIsTheAntecedentOfTheRegionResult` |
| A binder at a non-`i` sort refuses rather than guessing a guard | `aBinderAtANonSetSortRefusesRatherThanGuessing` |
| A region holds a binder body; the bound variable is an ordinary op | `aRegionHoldsABinderBody` |
| A fixpoint is a walk that changes nothing; no round cap exists — a pass with 1,000 rewrites converges | `aConvergentPassNeedsNoCap` |
| `replaceAllUses` scans every op (no use-list), so a pass is O(rewrites × ops) | `Sources/IR/Builder.swift` `replaceAllUses` |
| Adding one `Op` case costs **5** exhaustive switches | `grep -c 'switch self' Sources/IR/Op.swift` + `legalize` |
| YXML parses real export output; `render` emits what the REAL checker accepts | `aRealExportFileParses`, `theRealCheckerAcceptsWhatRenderEmits` |
| `base/axioms.fol.def` checks clean | `proof_checker base/axioms.fol.{def,proof}` → `OK: 7 claim(s)`, empty stderr |

**There is no reader.** Nothing turns `YXML.Node` into a `Graph`; every test builds
its graph by hand.

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

Next to discuss: **the mutation API.** `insert(before:)` silently appends when
the anchor is not in the region's `ops` (`?? count`, a rule-1 fallback);
`erase` tombstones without checking for remaining uses; `DESIGN.md` §4 claims
lowering "relabels edges, nodes persist" while every pattern inserts a new op +
`replaceAllUses` + `erase`. `Trueprop`'s coercion needs forwarding, not relabel.

Queued for discussion, not decided:
- how a proof is typed — a proof of φ must be distinguishable from φ
- substitution into a region (∀-elim at a term, β, schema instantiation)
- formula equality — interning pure ops vs α-equivalence over regions
- citations: a symbol table of lowered signatures (ties to §6.3, §6.5)
- provenance on created ops, instead of phase 2 re-running lowering
- a structural verifier: operand live/typed/in scope, region result set, one owner
- duplicated facts: `Binder` in `IR` and `FolDialect`; `isaAll`'s sort vs its region arg
- `FolDialect.Formula` beside the `fol.*` ops — two representations of one thing

**Deferred until the framework settles: the reader.** Decoding `QPair_iff`
(`ZF.QPair`, serial 6958) needs an `i`-valued constant application, IFOL's
`iff`/`conj`, and a positional ztyp decoder (tag 0 is both `ZConst` and `Type`).
