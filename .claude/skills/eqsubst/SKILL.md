---
name: eqsubst
description: Eliminate ONE ledger entry of the kernel `eq_subst` op from the isa2fol corpus, on the rail, without raising coverage instead. Use whenever working on eq_subst retirement / removing eq_subst from the checker kernel, routing IFOL_2esubst or a foundation body off eq_subst, or when tempted to "un-stub proofs / raise the Proved count" (that is NOT this goal). Enforces the no-eq_subst rail.
argument-hint: [ledger-entry-name]
allowed-tools: Read Grep Glob Bash Edit Write
---

# /eqsubst — drive the ledger to empty, then delete the kernel op

The goal is **remove `eq_subst` from the checker kernel.** Success = the emitted
corpus verifies against a kernel with NO `eq_subst`, no regression. The ONLY thing
standing in the way is `ci/eq_subst_ledger.txt` — every proof still emitting
`eq_subst`. Drive it to EMPTY, then delete the op. Nothing else is this goal.

## The #1 drift (we did it this session — do not repeat)

**Confusing "raise the Proved count" with "eliminate eq_subst."** The 727
`ShapeMismatch:ImpliesElim` / 1526 forced-UNPROVED proofs are **already
`eq_subst`-free** (they are stubs). Un-stubbing them (tracker fixes,
`instantiate_schema` higher-arity, NonFunctionIota, `_resp`/`_exists` claims)
raises coverage but **removes ZERO eq_subst** and clears **ZERO ledger entries**.
That is a different project (faithfulness/coverage), not this one. If the work you
are about to do does not strike a name off `ci/eq_subst_ledger.txt`, you are off the
rail — stop.

**Litmus test before any edit:** "Which ledger entry does this remove, and will
`ci/no_eq_subst_gate.sh` show the ledger strictly shorter?" No answer ⇒ not this skill.

## Hard rules (do not rationalize around these)

1. **Every `eq_subst` use has a CONCRETE `P` — so it is derivable structurally.**
   `eq_subst` is opaque Leibniz (`eq(a,b) → P(a) → P(b)`, arbitrary P); it is a
   kernel primitive ONLY because P is opaque. In every real use P = `λx.φ(x)` is
   known, and `φ(a)→φ(b)` follows by induction over φ from atom-congruence
   (`elem_first_subst`, `eq_first/second_subst`) + native connective ND. That
   induction is `rewrite/congruence.rs::congruence()` — already built. Use it.
2. **Keep `elem_first_subst`; remove `eq_subst`.** The end foundation keeps exactly
   ONE irreducible atomic-equality axiom (`elem_first_subst`) plus derived
   structural congruence. Never re-introduce opaque Leibniz under another name
   (a fresh `P`-schema, a "congruence axiom", a trusted `_resp` you did not prove).
3. **Do NOT add to the ledger to pass.** The gate forbids growth; the skill forbids
   even thinking of it. Entries leave the ledger only by being eliminated.
4. **One ledger entry per commit.** Pick a single entry; drive it `eq_subst`-free;
   gate; commit. No jumping ahead while a chosen entry is unfinished.
5. **The gate is law.** After wiring, `ci/no_eq_subst_gate.sh <fresh.proof>` must show
   the ledger strictly shorter (or the PROGRESS line naming your entry as now-clean,
   which you then prune), `ci/no_admit_gate.sh` stays `OK: no hacks`, and the corpus
   4-tuple does not regress on the affected proofs (or you honestly report the
   regression and its cause — never hide it).

## The two categories (the ledger is the frontier table)

`ci/eq_subst_ledger.txt` groups the remaining entries:

- **Category A — hardcoded foundation bodies** (`rs/src/bridge/lambda_foundation/*.body`):
  `collect_clean_bwd_clean`, `Image_mem_def`, `Pair_arg1_subst`, `range_relmem`,
  `range_unique`. Each rewrites ONE concrete predicate with a direct kernel
  `eq_subst`. **Clear by:** re-deriving the body with `congruence`/`ext_rewrite` over
  that concrete position. Self-contained, finite — the tractable proving ground.
- **Category B — opaque-P subst schemas** (`rs/src/schema_proof/fo_lemmas.rs`):
  `IFOL_2esubst`, `IFOL_2essubst`, `IFOL_2eback_subst`, `IFOL_2eforw_subst`. Each is
  general Leibniz over opaque P, proved WITH `eq_subst` — unprovable otherwise.
  **Clear by INLINING every downstream `schema_inst` use** (each carries a concrete
  `P = λx.φ` already in the IR as a `SchemaBinding`) through `congruence(motive=φ, eq)`
  — `congruence()` returns the `φ(b)` result directly — until the schema has zero
  uses, THEN delete its claim+proof. This is Phase 3 / Population A.

## The loop

1. **Orient.** Read `ci/eq_subst_ledger.txt`. Generate fresh + run the rail (the gate
   `cd`s to repo root, so pass a REPO-ROOT-relative proof path, from repo root):
   ```
   cd rs && ./target/release/isa2fol --bridge ../data/zf_export --output ../data/zf_export/bridge.fol.def && cd ..
   bash ci/no_eq_subst_gate.sh data/zf_export/bridge.fol.proof
   ```
   Note the current 4-tuple (stock checker) as the no-regression baseline. Pick the
   target entry (the skill argument, or the next tractable one — start Category A).
2. **Locate the eq_subst.** Find the body/schema and the exact `eq_subst` step
   (`--trace <name>` / read the `.body` / read `fo_lemmas.rs`). Know WHICH concrete
   predicate + position it rewrites and WHAT the structural replacement is.
3. **Derive structurally.** Replace the `eq_subst` with a `congruence`/`ext_rewrite`
   derivation over the concrete positions (Category A = in the body; Category B =
   route the uses, then delete the schema). If it is iota-heavy you will hit the
   **materialized-handle vs raw-iota `implies_elim` wall** (memory: emit the
   eliminated / exists-descent form the stock checker accepts) — that wall IS the
   real work here, not a detour.
4. **Gate.** Regenerate; `ci/no_eq_subst_gate.sh <fresh.proof>` (ledger strictly
   shorter for your entry); `ci/no_admit_gate.sh` (no hacks); `cargo test --release
   --lib` (green); stock-checker 4-tuple (no regression on affected proofs, or an
   honest, explained one). If you cannot eliminate it without admitting/regressing —
   STOP and report; do not admit, do not park it back on the ledger silently.
5. **Commit one entry.** Prune the cleared name from `ci/eq_subst_ledger.txt`. Commit
   message names the entry + ledger delta (N→N-1) + 4-tuple delta. When the ledger
   hits ZERO, the final step is deleting the kernel op (fol-zfc `lowering.cpp` /
   `stack.cpp` + decls; `translate_term` STAYS) and re-verifying the whole corpus.

## Anti-sprawl

- `ci/eq_subst_ledger.txt` is the frontier; `rs/docs/EXT_SUBST_SPEC.md §0.9` is the
  design (structural congruence). Do NOT spin up new plan docs or measurement passes
  in place of eliminating an entry — that is the drift. If you are writing analysis
  instead of removing an `eq_subst`, stop and remove one.
- `congruence()` is already built (`116f47d7`); reuse it, don't re-derive congruence.

## Checker / build facts
- Checker: `/home/arthur/Documents/repo/fol-zfc/bazel-bin/src/tools/proof_checker`
  (stock; NEVER modify it to accept our output — self-certification is forbidden).
  Release builds only. Command:
  `PROOF_CHECKER_MAX_WARNINGS=100000 <checker> <def> <proof> | grep -E '^Proved|^Conditional|^Unproved|^Failed'`.
- `forall_elim` tolerates iota↔materialized-handle; `implies_elim` demands EXACT term
  identity (the wall). `eq_sym` is native (no `use`). `rs/bridge.fol.*` golden is
  PRE-EXISTINGLY STALE — always gate on a FRESH `--bridge` output, never the golden.
- Clean up generated `../data/zf_export/bridge.fol.*` / `bridge.serial_map` after
  measuring (artifacts, do not commit).
