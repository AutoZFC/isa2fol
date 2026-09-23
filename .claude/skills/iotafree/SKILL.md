---
name: iotafree
description: Drive isa2fol toward FULLY iota-free emitted proofs by mirroring fol-zfc's description-elimination, one plan node at a time, on the rail. Use whenever working on iota/description elimination, the epsilon-wall (implies_elim "antecedent doesn't match" / "unknown term"), materialize_term / iota_elim emission, or the IOTA_FREE_PLAN. Enforces the iota-free rail + the never-promote rule.
argument-hint: [phase-node, e.g. P3.1 or "next"]
allowed-tools: Read Grep Glob Bash Edit Write
---

# /iotafree — mirror fol-zfc's eliminate_descriptions; drive iota to 0

**Goal:** isa2fol emits proofs the stock ND checker accepts WITHOUT needing the
description handling it lacks. No raw `(iota …)` term may reach a checker rule
that compares by exact identity (`implies_elim`, `not_elim`, `exists_intro`).
Success = the epsilon-wall class is gone and the corpus is iota-free, with no
regression and NO new axioms. Full roadmap: `rs/docs/IOTA_FREE_PLAN.md`.

## The #1 drift (do not repeat)
**Citing an axiom / promoting a theorem to make a proof pass.** That is the
FORBIDDEN admission path (it grew thm-debt +12 and cascaded last time). Never
turn a theorem into an axiom; never add an axiom or a trusted `_resp`/`_unique`
you did not derive. Accept a 4-tuple regression when it strictly trades for a
removed iota — but admission is not a trade, it is a hack.

**Second drift:** invent our own exists-descent shape instead of matching the
checker. The checker's `eliminate_descriptions` (fol-zfc `formula.cpp:790-927`)
is the ground truth for how formulas compare — our `∃`-form must equal ITS
output (differential oracle). Porting the CODE (uniform positive Russell,
`Not(Exists…)` NOT `∀`, no α-dedup) beats re-deriving the docs (which are stale).

## The loop (one plan node per invocation)
1. **Validate baseline first.** From repo root:
   - `cd rs && cargo build --release && cargo test --release --lib` (clean).
   - `cd rs && ./target/release/isa2fol --bridge ../data/zf_export` (regen).
   - `bash ci/no_admit_gate.sh` → `OK: no hacks`, **thm-debt unchanged** (never promote).
   - `bash ci/no_eq_subst_gate.sh rs/bridge.fol.proof` → ledger unchanged.
   - `bash ci/iota_free_gate.sh rs/bridge.fol.proof` → within MAX.
   - 4-tuple via the stock checker (record Proved/Conditional/Unproved + the
     `ERROR: N proof(s) failed` line = Failed) AND the **wall-count** (ERRORs
     matching the iota-mismatch pattern). This is the PRIMARY progress signal.
2. **Pick the node.** Read `rs/docs/IOTA_FREE_PLAN.md` §4; take the argument
   node (or the first unfinished one). Do EXACTLY that node — no scope creep.
3. **Do one increment.** Per the phase. P1 = port `eliminate_descriptions`
   (differential-oracle-tested, INERT). P3 = generalize
   `pass_eliminate_descriptions` (`pass/elim_desc.rs`, slot `bridge/mod.rs:1168`)
   for ONE step-kind (implies_elim antecedent first). Mirror `emit_eq_sym_desc`
   + `rewrite_exists` + fol-zfc's `EliminateIotaInProof`.
4. **Gate.** Re-run all of step 1. Required: no_admit thm-debt unchanged;
   no_eq_subst unchanged; iota gate not increased (lower MAX_* in
   `ci/iota_ledger.txt` if it dropped); wall-count not up; Proved not down
   unless a hack was genuinely removed and the user accepts it; ZERO new fails
   from ordering/cascade (all-`unknown-in-ctx` newly-failed = you perturbed the
   emission topo-order — fix, don't ship).
5. **Record.** Update the `IOTA_FREE_PLAN.md` §7 status log + the ledger MAX.

## Litmus test before any edit
"Which plan node is this, and after it will `ci/iota_free_gate.sh` show a lower
count (or the differential oracle green) with thm-debt unchanged and no new
fails?" No answer ⇒ off the rail; stop.

## Hard rules
1. **Never promote / never add an axiom.** thm-debt monotone. (`no_admit`.)
2. **No new `eq_subst`.** (`no_eq_subst` ledger unchanged.)
3. **iota-ledger monotone non-increasing;** drive to 0, never raise MAX to pass.
4. **Differential-anchored:** emitted `∃`-form must equal the checker's
   `eliminate_descriptions` output — validated, not assumed.
5. **Prefer honest UNPROVED over a wrong emit.** Soundness = Leisenring
   (Hilbert–Bernays 2nd ε-theorem); the pass adds ZERO axioms.

## Key coordinates (from the 2026-07-27 investigation)
- Formula rewrite to port: fol-zfc `src/core/formula.cpp:790-927`.
- Proof-level reference impl: fol-zfc `src/proof/translate/iota_elim/proof_rewriter.cpp`
  (`EliminateIotaInProof`, wired only in the comb checker).
- Wall sites (exact-identity): `stack.cpp:339` implies_elim, `:393` not_elim,
  `:553` exists_intro; `forall_elim :519` tolerates raw iota (the leak in).
- Our emit sites: `materialize_term rewrite/mod.rs:288` (hub) + equiv.rs:766,832
  + expand.rs:78 + beta_norm.rs:209 + prop_bridge.rs:389; TEXT: flat_rel/arity.rs:185,196.
- Nucleus to generalize: `pass/elim_desc.rs` + `emit_eq_sym_desc rewrite/mod.rs:327`
  + `rewrite_exists quant.rs:87`. Pass slot: `bridge/mod.rs:1168-1171`.
