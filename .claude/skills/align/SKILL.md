---
name: align
description: Keep the isa2fol implementation aligned with the proved mathematics — classify before coding, probe before wiring, peel one obstruction at a time. Use whenever emitting/unblocking a constant, changing a generator or recognizer, chasing a refusal or kernel rejection, or when a doc explains why something "cannot" be done. Enforces the verdict rail.
argument-hint: [constant-or-refusal]
allowed-tools: Read Grep Glob Bash Edit Write
---

# /align — the math is proved; a blocker is yours until shown otherwise

The mathematics is settled (`docs/FOUNDATION.md`). Of the whole corpus **four**
constants are refused by the specification — R6's `split`/`setclass` (S5) and
`cond`/`update` (S4). **Everything else that does not emit is an implementation
problem.** This skill exists because the project has repeatedly recorded an
implementation gap as if it were a mathematical one, and then sent the next
session to the wrong file.

## Hard rules (do not rationalize around these)

1. **Never diagnose from a document.** A doc's account of a blocker is a
   *hypothesis*. Reproduce it, read the **actual** refusal string, and locate the
   literal that produced it (`grep -rn '<exact text>' src/`). Cite `file:line`.
   Precedent: `STATE §7` named `generate::alias` for a message that only ever came
   from `concrete_uniq_proof` — and the *recorded* refusal was a third thing.
2. **Classify before coding.** Run `gate::align`. `Refused` → it is mathematics;
   stop and say so. `Omitted` → `licensed_by` names what proves it derivable, and
   that is the obligation you are discharging.
3. **No new admitted axiom or schema, ever.** `base/` is the only place a bare
   `axiom` may appear. A schema is a macro and is legitimate only when *proved*
   parametrically. If a step seems to need an admission, you have the wrong design.
4. **Probe before wiring.** Build the smallest `.fol.def`/`.fol.proof` the checker
   accepts — exit 0 **and empty stderr** — showing the target IS derivable, before
   touching the pipeline. Cheapest form: call the generator in a throwaway test and
   run `unit::check`.
5. **Peel one obstruction at a time**, re-running after each. Read `w.failed`, not
   just `w.refused`: **a refusal that becomes a kernel rejection is worse than the
   refusal was**, and it means you removed a guard without building its content.
6. **A guard is guilty until proven the true obstruction.** Delete it and observe.
   Guards naming the wrong condition are this codebase's most common bug — the one
   blocking `fst` claimed a graph-hypothesis/transport collision that provably
   cannot occur.
7. **Artifact beats doc.** When they disagree the code is right; fix the doc in the
   same session and say what was stale. (`FOUNDATION` said 19 axioms; `base/` has
   17. It said a class left of `∈` is "outside the theorem"; it is eliminable, and
   the elimination is kernel-proved.)
8. **Never hand over a non-green tree.** `git stash` with a descriptive message
   beats a half-refactor. Say plainly what is unfinished.

## The loop

1. **Orient.** Run `.claude/STATE.md` §0. Then `gate::align` — it prints the
   corpus partition and pins the counts.
2. **Target.** Pick one constant or one refusal kind. Read its ledger verdict and
   its `licensed_by`. If the refusal shape is not in `LEDGER`, the gate fails —
   classify it first; that *is* the first unit of work.
3. **Reproduce.** Dump the rendered body and the real refusal. Never read a chain
   shape off a definition — print the `Formula`.
4. **Probe** (rule 4), then **implement**, peeling (rule 5).
5. **Gate.** All of: `MEM=16G scripts/capped.sh swift test` green · `legalize`
   passes on every graph a test builds · comment density falling toward 5%
   (rule 9) · no new `axiom` outside `base/`.
6. **Record.** Update `STATE.md` §7 with the *measured* result and any correction
   owed to `FOUNDATION.md`. Corrections go in as standing warnings, not as history.

## Design bias, when there is a choice

- **Codegen over hardcoding.** A per-arity table passes every test written at the
  arities it covers. If a mechanism is width-parameterised, it owes a test at a
  width `base/` does not ship.
- **Proved schemas are free to use; unproved ones are hacks.** Instantiating a
  proved kernel is preferred to open-coding a derivation.
- **Watch proof size.** It is measured, not assumed, and **this bullet has been
  stale THREE times, on all four numbers each time.** Do not quote it — run
  `every_refusal_carries_a_verdict`, which prints the pair and asserts the
  ratchets. A change that inflates them needs to say so.
- **Fix the design, not the symptom.** Trace upstream; the bug is almost never
  where the value is wrong.

## Anti-sprawl

`FOUNDATION.md` is the mathematics and the only design doc — its companions were
deleted 2026-09-23 as Rust-era. `DESIGN.md` is the package structure.
`.claude/STATE.md` is the handoff. Update those; do not create new plan docs.
One node per commit.

**Absorbs `/chain`**, deleted 2026-09-23 with the Rust tree it drove. Its
no-admit rule survives as rule 3 above.

## Facts worth not re-deriving

- Checker: `~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`, passed via
  `PROOF_CHECKER=`. It MOVED out of `~/Documents/repo/`; `find_checker` still looks
  for the old path and simply fails every kernel test when it is absent.
  A base tier is a CHAINED unit: `$CK <def> <proof> <deps…> -- <dep_proofs…>`; run
  bare it reports `Failed`, which reads exactly like staleness and is not.
- Release builds only, and everything through `scripts/capped.sh` (rule 10).
- `exists_intro` at **two** arguments generalises *every* occurrence of the
  witness; a target the witness still occurs in needs the three-argument
  `let` form. `exists_elim`'s eigenvariable is discharged by a no-witness
  `exists_intro` before `implies_intro`.
- `set(C)` is **false** for a class, not redundant: class binders are bare, set
  binders guarded and interleaved (R3).
