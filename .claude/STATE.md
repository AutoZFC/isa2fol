# STATE — isa2fol
`cf2c1972` · `feature/exists-descent` · 2026-09-23.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

**⚠ THE RUST TREE IS GONE.** Deleted at `f2ce5bbf`. Any `rs/…` path in any
document is dead; it is in git history and nothing depends on it.
`swift` is NOT on a non-login shell's PATH — it is at `~/.local/bin`.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `swift build` | `Build complete!` |
| `swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`17`** |
| comment density of `Sources/**/*.swift` (CLAUDE.md rule 9 has the script) | `24/504 = 4.8%` — **UNDER the cap**; it must stay there |
| `find Sources Tests -name '*.swift' \| wc -l` | `22` (852 lines) |
| `ls Sources` | `FolDialect Framework IR isa2fol YXML` |
| `grep -cE '^axiom' base/axioms.fol.def` | `17` |
| `ls base/tiers/*.fol.def \| wc -l` | `10` |
| `ls docs/phase2_probes/*.fol.def \| wc -l` | `17` |
| `scripts/source-surface.py \| head -1` | `population: 3616 named ZF theorems, 37 ZF.* theories` |
| `ls data/zf_export \| wc -l` | `40` |
| `test -x ~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker` | exit 0 |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

Worktree `/home/arthur/repos/isa2fol`, tree CLEAN, **72 ahead of
`origin/feature/exists-descent`, NOT pushed**.
⚠ **THE BRANCH NAME DESCRIBES WORK THAT NO LONGER EXISTS** — see §6.
⚠ **TWO DEAD WORKTREES REST ON THE DELETED RUST LAYER**, and `git worktree list`
is the only place either shows up:
- `.claude/worktrees/contig` (`fix/contiguous-slots`) — gitignored, never
  `git add -A` it.
- `/home/arthur/repos/isa2fol-build` (`feature/build-integration`, `6f7703f0`) —
  outside this worktree, still carrying `rs/`, `BUILD.bazel`, its own `CLAUDE.md`.

`git worktree remove` clears either.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `DESIGN.md` | the package design. **§5 lists what was deliberately NOT decided** |
| `CLAUDE.md` rules 9, 11, 12 | the comment cap and the two Swift rules the guarantees rest on |
| `Sources/FolDialect/Term.swift` | S1 as a type — one field, and why that kills `iota` |
| `docs/FOUNDATION.md` **§2** | S1–S6, the specification everything must satisfy |
| `docs/SOURCE_SURFACE.md` | the MEASURED source surface — what the reader must cover, and why FOL is proof-only |
| `DESIGN.md` **§4** | the pass engine — why `legalize` replaces rule 11, and why derivations are append-only |
| `Sources/IR/Legalize.swift` | the ONE exhaustive switch naming both vocabularies |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 **AND** stderr is empty | `theRealCheckerAcceptsWhatRenderEmits` |
| No `default:` in a switch over an IR enum | CLAUDE.md rule 11 — **nothing checks this; it is discipline** |
| IR enums stay `internal` or `@frozen` | CLAUDE.md rule 12 — same |
| Only `base/` may carry a bare `axiom` | not yet enforced in code |
| Comments ≤ 5% of `Sources/**/*.swift` | the §0 row; **delete prose, never raise the cap** |
| `docs/FOUNDATION.md` is mathematics, with no code reference | nothing checks it; discipline |

**Standing warnings — silent if repeated:**

- **⚠ `Conditional` IS NOT `Proved` AND THEY ARE NEVER SUMMED.** The checker
  reports three states. A corpus conditional on one missing lemma reads as a
  triumph if they are added.
- **⚠ A CLAIM WITH NO PROOF BLOCK IS NOT CITABLE.** `use X` on a declared-only
  claim fails `unknown axiom/theorem in ctx` — *not* `Conditional`. `Conditional`
  needs `proof X: UNPROVED`. An `include` carries declarations, never proofs.
- **⚠ GUARDING A CLASS MAKES THE CLAIM FALSE, NOT REDUNDANT.** Hence
  `Binder.setVar`/`.classVar`; pinned by `aClassBinderCarriesNoGuard`.
- **⚠ NOTHING CLOSES POLYMORPHISM AT THE TYPE LEVEL ANY MORE.** `Statement<Poly>`/
  `<Ground>` went with the tree IR on 2026-09-23, and `IRType` has no case for
  `'a`. The reader must refuse a type variable BY NAME, and
  `groundnessIsStructural` — the only test that pinned it — went with the module.
  Re-pin it. Measured, the cost is small: **12 of 3,616 named ZF theorems**
  carry a type variable (0.3%), half `split`/`qsplit`; IFOL/FOL/Pure are 37-48%
  but that layer is cited, never translated.
- **⚠ `producesEvidence` GUARDS AN OP'S RESULT, NOT ITS OPERANDS.** Rewriting a
  formula that a proof step cites silently changes what is proved. Nothing
  catches that; what covers it is ORDER — lower every formula, then build the
  proof layer — and no code enforces the order yet.
- **⚠ `Op.operands` ALLOCATES, EVEN AT FIXED ARITY** — `return [a, b]` is a heap
  array. In any loop over the whole graph use `Op.references(_:)`, which does
  not. Rebuilding every op in `replaceAllUses` cost 1.5× before the guard.
- **⚠ `IRType.i` DOES NOT DISTINGUISH A SET FROM A CLASS, AND THAT IS DELIBERATE.**
  NBG is one-sorted; `set(·)` is a predicate, not a sort. So the type system CANNOT
  catch a guard error — only G5's two-sided rule can, and it must run after every
  pass, not once at the end.
- **⚠ `IRType.prop` IS PURE'S `prop`; A FORMULA IS `.o`.** So `folZfcOnly` bans
  `.prop` — "no meta level survives" — which is correct and reads backwards.
  The four cases are the surface's own names: `.i`, `.o`, `.prop`, `.fn`.
- **⚠ A REWRITE PATTERN IS PARTIAL, SO ADDING AN `Op` CASE BREAKS NOTHING.** Rule 11's
  guarantee moved to `legalize`, which is exhaustive. A new op that nothing lowers is
  caught there and nowhere else.
- **⚠ SERIALS COLLIDE ACROSS THEORIES** — 760 of them. Any index over the export
  must key on `(theory, serial)`.
- **⚠ `IsaDialect.Term` HAS FIVE CASES BECAUSE THE EXPORT HAS NO TAG 2.** That is
  a fact about the export's *preprocessing*, not about Isabelle. Reading must fail
  loudly if one arrives, never absorb it.
- **⚠ THE RUST-ERA DESIGN DOCS WERE DELETED 2026-09-23 — DO NOT RESTORE ONE TO
  ANSWER A DESIGN QUESTION.** `FOUNDATION_TO_FOLZFC.md`, `DECLARE.md`,
  `REPLAY.md`, `KERNEL_ABI.md`, `fol_abi.h`, `DESIGN_rs.md`. They planned the
  Rust implementation — `IR1`–`IR4`, `H → S → E → LOWER`, `PassContext`,
  `Vec<Step>` dialect-partitioned passes, `src/replay/`'s two-phase driver — and
  none of it survives the language change. They read as current and they are not;
  that is exactly how a session re-imports a dead architecture. **Structure comes
  from `DESIGN.md` and the code. `docs/FOUNDATION.md` supplies the mathematics
  and nothing else.**
- **⚠ `docs/FOUNDATION.md` CARRIES NO CODE REFERENCE AND MUST NOT GAIN ONE.**
  Module paths, function names and test names were stripped 2026-09-23: each
  named deleted code while reading as live evidence. Cite a `base/` tier or a
  probe — the kernel checks those — or state the claim with no handle.
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED**, and its §5 now
  says so outright. The measuring code went with the encoder. Belief, not state.
- **⚠ THE CHECKER PATH IN OLDER DOCS IS WRONG.** It is
  `~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`, never
  `/home/arthur/Documents/repo/fol-zfc/`.

## 4. State

| claim | verified by |
|---|---|
| The YXML reader reads real Isabelle output — 11 Pure axioms, `file=theory.ML` | `aRealExportFileParses` |
| `render` emits syntax the REAL checker accepts: exit 0, empty stderr, `+ probe` | `theRealCheckerAcceptsWhatRenderEmits` |
| A class binder renders unguarded; a set binder renders as an implication | `aClassBinderCarriesNoGuard`, `aGuardedForallRendersAsAnImplication` |
| An unbalanced close is an error, not absorbed | `anUnbalancedCloseIsAnError` |
| `base/axioms.fol.def` still checks clean after the move | `proof_checker base/axioms.fol.def base/axioms.fol.proof` → `OK: 7 claim(s)` |
| Swift installs no-sudo, GPG-verified, idempotent | `scripts/02-install-swift.sh` |
| Mutation is in place — COW is NOT firing; graph build is linear in ops | `bench()` |
| ⚠ **DEBUG IS 38× SLOWER THAN RELEASE** (k=800: 161.9ms vs 4.3ms). Benchmark with `-c release` or the number is meaningless | `bench()` |
| `PatternPass` is **O(k²)** — release 0.3/1.2/4.7ms at k=200/400/800. Fine per theorem; ~70 min on one corpus-wide graph | `bench()`, **`-c release`** |
| The pass engine lowers a mixed Isa/Fol graph to fol-zfc-only | `loweringMakesItFolZfcOnly` |
| A pass that leaves an `isa.*` op behind is rejected AT THAT PASS | `aPassThatLeavesItsEliminatedShapeBehindIsRejected` |
| A value from a **fol** evidence op cannot be rewritten or erased; `isaAxiom` is source and MUST stay lowerable | `aDerivationCannotBeRewritten`, `aDerivationCannotBeErased`, `anIsaAxiomCanBeLoweredToAFolUse` |
| A non-converging pattern fixpoint throws rather than capping | `aFixpointThatDoesNotConvergeThrows` |
| The ZF source surface is 16 logical constants + 4 sorts + 249 ZF constants; proofs cite a frontier of 7 Pure axioms + 132 IFOL/FOL rules + 7 ZF axioms | `scripts/source-surface.py` |

**Nothing above the YXML reader is implemented.** `Framework` has types only;
there is no corpus driver, no conversion, no reader from `Node` to `Statement`.

## 5. Beliefs — NOT verified

**⚠ EVERY CORPUS MEASUREMENT BELOW WAS TAKEN WITH RUST CODE THAT NO LONGER
EXISTS.** None has a live handle. Re-derive before acting on any of it.

- **868** statements declare; **15,243** wait on a constant; **687** genuinely
  refuse — of which **463** are `sort 'a` (polymorphism).
- Of 868 declared proofs, **794** reach PASS S and **74** carry a βη-redex, so
  most proofs are already normal and PASS S is the wall.
- **197** term constants in **27** definitional levels, plus 54 predicates.
  *This one is partly independent*: `~/isabelle-object-constants.md` has the table
  and the `.thy` pointers, and the split was pinned by a test that is now deleted.
- The Pure metalogic is 7 rules, 5 of them 99.2% of citations —
  `~/isabelle-pure-metalogic.md`, likewise from deleted code.
- The theorem citation graph is acyclic (16,798 nodes, 0 unordered).

## 6. Open decisions

1. **The branch.** `feature/exists-descent` names deleted work; 72 commits
   unpushed. Rename, branch fresh, or merge to `main`?
2. **What monomorphise instantiates at** — the use-site type argument (faithful;
   leaves a statement's own free `'a` undecided) or always `'a := i` (resolves
   `eq`/`All`/`Ex`/`split` at once, but a generic IFOL theorem then means only its
   `i`-instance, which is WEAKER than Isabelle's).
3. **The ZF primitive surface** — a third dialect, or a stage inside IsaDialect?
   Parked by the user; constants are explicitly *not* primitives.
4. **What `base/` becomes** — `.fol.def` text today. Does `FolDialect` read it,
   or is it opaque input handed to the checker?
5. **`UNPROVED` as `extern`.** Separate compilation needs it; the old L gate
   refused it outright ("R2 admits no debt"). The rule arguably belongs at the
   final link, not per unit. Nowhere written down since the companion docs went.
6. **Circular reasoning in §18's fixpoint.** The user flagged it as suspect —
   fol-zfc does not support circular reasoning, and §18's "it is a DAG at artifact
   granularity" is the only thing holding it up, from a design since deleted.

## 7. Next action

**Read the export into the IR graph: `YXML.Node` → `Graph` of `isa.*` ops.**

The pass engine is built and proved on a 5-op graph (`DESIGN.md` §4); the tree IR
that used to stand between them is deleted, so the reader now builds a `Graph`
directly. `DESIGN.md` §2 lists the refusals it owes;
`docs/SOURCE_SURFACE.md` lists the surface it must cover.

**Done when** every one of the 16,798 export statements either builds a `Graph`
or fails with a named `IRRefusal` — no absorbed cases — and the polymorphism
refusal is re-pinned by a test.
