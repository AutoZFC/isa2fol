# STATE — isa2fol
`f2ce5bbf` · `feature/exists-descent` · 2026-09-23.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

**⚠ THE RUST TREE IS GONE.** Deleted at `f2ce5bbf`. Any `rs/…` path in any
document is dead; it is in git history and nothing depends on it.
`swift` is NOT on a non-login shell's PATH — it is at `~/.local/bin`.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `swift build` | `Build complete!` |
| `swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`8`** |
| comment density of `Sources/**/*.swift` (CLAUDE.md rule 9 has the script) | `40/268 = 14.9%` — **OVER the 5% cap, deliberately recorded** |
| `find Sources Tests -name '*.swift' \| wc -l` | `16` (411 lines) |
| `ls Sources` | `FolDialect Framework isa2fol IsaDialect YXML` |
| `grep -cE '^axiom' base/axioms.fol.def` | `17` |
| `ls base/tiers/*.fol.def \| wc -l` | `10` |
| `ls docs/phase2_probes/*.fol.def \| wc -l` | `17` |
| `ls data/zf_export \| wc -l` | `40` |
| `test -x ~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker` | exit 0 |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

Worktree `/home/arthur/repos/isa2fol`, tree CLEAN, **71 ahead of
`origin/feature/exists-descent`, NOT pushed**.
⚠ **THE BRANCH NAME DESCRIBES WORK THAT NO LONGER EXISTS** — see §6.
⚠ **`.claude/worktrees/contig` is a dead worktree** resting on the deleted layer;
gitignored, never `git add -A` it. `git worktree remove` clears it.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `DESIGN.md` | the package design. **§5 lists what was deliberately NOT decided** |
| `CLAUDE.md` rules 9, 11, 12 | the comment cap and the two Swift rules the guarantees rest on |
| `Sources/FolDialect/Term.swift` | S1 as a type — one field, and why that kills `iota` |
| `Sources/IsaDialect/Statement.swift` | `Poly`/`Ground` phantom stages |
| `docs/FOUNDATION.md` **§2** | S1–S6, the specification everything must satisfy |
| `docs/FOUNDATION_TO_FOLZFC.md` **§14** | the source interface — the frozen IR1 calculus |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 **AND** stderr is empty | `theRealCheckerAcceptsWhatRenderEmits` |
| No `default:` in a switch over an IR enum | CLAUDE.md rule 11 — **nothing checks this; it is discipline** |
| IR enums stay `internal` or `@frozen` | CLAUDE.md rule 12 — same |
| Only `base/` may carry a bare `axiom` | not yet enforced in code |
| Comments ≤ 5% of `Sources/**/*.swift` | the §0 row; **delete prose, never raise the cap** |

**Standing warnings — silent if repeated:**

- **⚠ `Conditional` IS NOT `Proved` AND THEY ARE NEVER SUMMED.** The checker
  reports three states. A corpus conditional on one missing lemma reads as a
  triumph if they are added.
- **⚠ A CLAIM WITH NO PROOF BLOCK IS NOT CITABLE.** `use X` on a declared-only
  claim fails `unknown axiom/theorem in ctx` — *not* `Conditional`. `Conditional`
  needs `proof X: UNPROVED`. An `include` carries declarations, never proofs.
- **⚠ GUARDING A CLASS MAKES THE CLAIM FALSE, NOT REDUNDANT.** Hence
  `Binder.setVar`/`.classVar`; pinned by `aClassBinderCarriesNoGuard`.
- **⚠ SERIALS COLLIDE ACROSS THEORIES** — 760 of them. Any index over the export
  must key on `(theory, serial)`.
- **⚠ `IsaDialect.Term` HAS FIVE CASES BECAUSE THE EXPORT HAS NO TAG 2.** That is
  a fact about the export's *preprocessing*, not about Isabelle. Reading must fail
  loudly if one arrives, never absorb it.
- **⚠ `docs/FOUNDATION_TO_FOLZFC.md` §10 AND §18 HAVE STATUS ROWS CITING DELETED
  CODE.** §10's phase table (3 of 8 rows), §18's "LANDED" rows (`walk_cenv`,
  `no_graph`, `w.graphs` — zero occurrences anywhere). Trust the code over the row.
- **⚠ THE CHECKER PATH IN OLDER DOCS IS WRONG.** It is
  `~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`, never
  `/home/arthur/Documents/repo/fol-zfc/`.

## 4. State

| claim | verified by |
|---|---|
| The YXML reader reads real Isabelle output — 11 Pure axioms, `file=theory.ML` | `aRealExportFileParses` |
| `render` emits syntax the REAL checker accepts: exit 0, empty stderr, `+ probe` | `theRealCheckerAcceptsWhatRenderEmits` |
| A class binder renders unguarded; a set binder renders as an implication | `aClassBinderCarriesNoGuard`, `aGuardedForallRendersAsAnImplication` |
| A type variable anywhere makes a whole sort non-ground | `groundnessIsStructural` |
| An unbalanced close is an error, not absorbed | `anUnbalancedCloseIsAnError` |
| `base/axioms.fol.def` still checks clean after the move | `proof_checker base/axioms.fol.def base/axioms.fol.proof` → `OK: 7 claim(s)` |
| Swift installs no-sudo, GPG-verified, idempotent | `scripts/02-install-swift.sh` |

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

1. **The branch.** `feature/exists-descent` names deleted work; 71 commits
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
   final link, not per unit. Not yet written into FOUNDATION_TO_FOLZFC.
6. **Circular reasoning in §18's fixpoint.** The user flagged it as suspect —
   fol-zfc does not support circular reasoning, and §18's "it is a DAG at artifact
   granularity" is the only thing holding it up, from a design since deleted.

## 7. Next action

**Build the IsaDialect reader: `YXML.Node` → `Statement<Poly>`.**

**Done when** every one of the 16,798 export statements either reads into a
`Statement<Poly>` or fails with a named `Refusal` — no absorbed cases — and the
tag-2 bet (§3) is tested against real data rather than assumed.
