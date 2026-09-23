---
name: chain
description: Derive one node of the isa2fol math-faithfulness chain WITHOUT admitting any new axiom. Use whenever working on the ZF→FOL faithfulness/lambda derivation, removing a convenience hack, or when tempted to admit a schema/axiom. Enforces the no-admit rail.
argument-hint: [node-or-hack-name]
allowed-tools: Read Grep Glob Bash Edit Write
---

# /chain — derive on the rail, never admit

You are advancing the isa2fol faithfulness derivation. The #1 failure mode (history:
we did it many times) is **admitting a convenience axiom/schema as a shortcut and
calling the result proved**. This skill exists to make that impossible. Math
faithfulness is P0.

## Hard rules (do not rationalize around these)

1. **No new admitted axioms or schemas. Ever.** The only legitimate admissions are
   the legit base in `rs/docs/CHAIN.md` (ZFC axioms in relmem/exists form,
   `elem_first_subst`, canonical op iff-definitions, first-order logic rules). If a
   step needs anything else, you DERIVE it — you do not admit it.
2. **No "tracked / flip-bounded / conservative / interim" admissions.** Those phrases
   are the rationalizations that caused the drift. There is no allowlist escape hatch.
3. **One node per commit.** Pick a single frontier node; do not jump ahead to
   downstream work while a dependency is still a hack.
4. **Probe-first.** Prove the node as a standalone `rs/docs/phase2_probes/<node>.fol.{def,proof}`
   that the checker accepts, using ONLY the legit base + already-derived nodes, BEFORE
   wiring it into the corpus.
5. **The gate is law.** `ci/no_admit_gate.sh` must not gain hacks; a node is only
   "done" when the hack count strictly drops (or stays 0) and `cargo test` is green.

## The loop

1. **Orient.** Read `rs/docs/CHAIN.md` (the rail + frontier table). Run
   `ci/no_admit_gate.sh` to see the live hack count. Pick the target node (the skill
   argument, or the next frontier node whose deps are all derived).
2. **Probe.** Write `rs/docs/phase2_probes/<node>.fol.{def,proof}`. Declare ONLY
   legit-base axioms + already-derived lemmas; prove `<node>`. Check it:
   `PROOF_CHECKER_MAX_WARNINGS=100000 /home/arthur/Documents/repo/fol-zfc/bazel-bin/src/tools/proof_checker <def> <proof>`
   It must be Proved, or Conditional only on legit-base schemas (Separation/Replacement).
   If you cannot derive it without admitting something — STOP and report; do not admit.
3. **Wire.** Replace the corpus admission with the derived proof (emit the lemma + its
   proof; remove the `axiom`/`schema` declaration). Re-generate:
   `cd rs && cargo run --release -- --bridge ../data/zf_export`.
4. **Gate.** `ci/no_admit_gate.sh` (hack count dropped, no new hacks), `cargo test
   --release` (green; the 3 `def_eq_fix_*` integration fails are pre-existing), and
   record the corpus 4-tuple from the checker (no Proved balloon = soundness).
5. **Commit one node.** Update the `rs/docs/CHAIN.md` frontier table (tick the node).
   Commit message names the node + the 4-tuple delta + the hack-count delta.

## Anti-sprawl

- `rs/docs/CHAIN.md` is the ONLY operational source of truth. Update it; don't create
  new plan docs. `FOUNDATION.md` is the math reference. Superseded plans live in
  `docs/archive/`.
- One probe file per node, named after the node. Delete superseded probes.
- If you find yourself writing a new plan/measurement instead of deriving a node, you
  are drifting — stop and derive the node.

## Checker / build facts
- Checker: `/home/arthur/Documents/repo/fol-zfc` branch `comb-verifier`,
  `bazel-bin/src/tools/proof_checker`. Release builds only.
- `forall_elim` at an iota term FAILS (parser quirk) — use eigenvars (`exists_elim`)
  instead. `IFOL_2erefl/sym/trans` are emitted late; derive `eq` facts from
  `Subset_def`+`extension__ax` if needed early. No `#` comments in `.body` files.
