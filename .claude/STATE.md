# STATE — isa2fol
`HEAD` · `feature/exists-descent` · 2026-09-24.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is NOT on a non-login shell's PATH — it is at `~/.local/bin`.
⚠ **BENCHMARK WITH `-c release` OR THE NUMBER IS MEANINGLESS.** There is no benchmark now.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`59`** |
| `ls Sources` | `FolDialect IR isa2fol YXML` |
| `ls docs` | `FOUNDATION.md phase2_probes SOURCE_SURFACE.md` |
| `find Sources Tests -name '*.swift' \| wc -l` | `19` (1805 lines) |
| comment density of `Sources` (CLAUDE.md rule 9 has the script) | `4/773 = 0.52%` — **UNDER the 5% cap** |
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
| `Sources/IR/Node.swift` | the flat Node; `mapChildren` — the ONE place binders are named — and `boundVariable` |
| `Sources/IR/Table.swift`, `Traversal.swift`, `Index.swift` | interning + validation at `intern`; the one `transform`; shift/instantiate/abstract as rules |
| `~/repos/fol-zfc-comb/src/proof/nd/stack.cpp`, `src/core/formula.cpp` | the checker the design mirrors: derived-formula marking, scopes, `instantiate_gen`/`shift`/`abstract` |
| `docs/SOURCE_SURFACE.md` | the MEASURED source surface; regenerates |
| `docs/FOUNDATION.md` **§2** | S1–S6, the specification everything must satisfy |
| `CLAUDE.md` rules 1, 9, 10, 11 | no fallbacks · comment cap · never run uncapped · no `default:` |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 **AND** stderr is empty | `theRealCheckerAcceptsWhatRenderEmits` |
| No source kind survives a lowered root | `legalize`, pinned by `legalizeRefusesAReachableSourceKindByName` |
| Equal content is one node; a node is well-formed or it does not exist | `Table.intern`, pinned by `TableTests` |
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
- **⚠ BUILDING fol-zfc-comb IN ITS DEFAULT CONFIG REPOINTS `bazel-bin`** from `k8-opt`
  (where `proof_checker` lives) to `k8-fastbuild`, and isa2fol's real-checker test then
  fails to find the checker. Restore: `ln -sfn <execroot>/bazel-out/k8-opt/bin bazel-bin`.
- **⚠ fol-zfc-comb's `//src/library` DOES NOT BUILD HERE AS CONFIGURED** — GCC 11 `-O3`
  `stringop-overflow` in `library.cpp` under `.bazelrc`'s `-Werror`; pre-existing. Its
  tests run with `--cxxopt=-Wno-error=stringop-overflow`.

## 4. State

| claim | verified by |
|---|---|
| A proof step constrains only its principal connective; conclusions are computed at `intern` | `ProofTests` |
| The real checker PROVES an emitted proof for every rule family (forall, exists, classical, not, or, iff, and, use) | `theRealCheckerProvesWhatEmissionWrites` |
| `Rule.after` rewrites a step once its premises are rewritten, conclusion unchanged | `afterRewritesAStepOnceItsPremisesAreRewritten` |
| The index engine satisfies D2's five laws over 300 seeded random formulas each, and its worked cases | `IndexTests` |
| The tests have teeth: `instantiate` without the `k − 1` fails 4 tests; `isaAbs` not marked binding fails 2 | a mutation, by hand — re-run it after touching `Index.swift`/`Node.swift` |
| YXML parses real export output | `aRealExportFileParses` |
| `render` emits what the REAL checker accepts and proves — every construct, and `false` as ⊥ (rendering `False` fails it: a mutation, by hand) | `theRealCheckerAcceptsWhatRenderEmits` |
| Qualified names in claim/predicate positions: the grammar change is DRAFTED on fol-zfc-comb branch `qualified-names` (`487c68c`), NOT merged; the checker isa2fol runs is still the old one, so the real-checker test uses only plain names | `git -C ~/repos/fol-zfc-comb log -1 qualified-names`; its `//test:qualified_names_test` |
| `base/axioms.fol.def` checks clean | `proof_checker base/axioms.fol.{def,proof}` → `OK: 7 claim(s)`, empty stderr |

**The framework is built — formulas, proof steps, rendering, emission. No concrete pass,
no reader.** Pre-existing rule-1 violation found, not fixed: `Sources/YXML/Node.swift:18`
reads a missing attribute as `""`.

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
1. ~~the formula table~~ — built
2. ~~D2's index engine, the traversal, passes, legalize~~ — built
3. ~~`FolDialect` as the text boundary~~ — `render` built; `parse` waits for imports
4. ~~the proof layer's framework~~ — built: 22 step kinds, conclusions at `intern`,
   two binder namespaces, `Rule.before`/`after`, emission. Census Q6 now only bears on
   the READER (how Isabelle's indices map to ours), not the framework

Every framework question is decided except proof-level depth (`DESIGN.md` §4.8), which
waits on census question 6. Pass-level questions (S1 placement, meta functions as function
classes) are in §4a and are NOT framework.

**In flight elsewhere:** the application-shape census,
`.claude/tasks/ISA_SHAPE_CENSUS.md` → `docs/ISA_SHAPES.md` on branch
`census/isa-shapes`. It TESTS the ZF-surface shape (`DESIGN.md` §2): which export
terms read into it, and which refuse.

**The reader comes after step 1**: its node kinds are §4.3's; it also needs a
positional ztyp decoder (tag 0 is both `ZConst` and `Type`). First target:
`QPair_iff` (`ZF.QPair`, serial 6958).
