# Task: census of the application shapes in the Isabelle export

**For:** a separate Claude session, working in parallel.
**Deliverable:** facts with a regenerating handle. **Not** a design, and **not** Swift code.

## Why this exists

isa2fol is redesigning its IR (the design session owns `Sources/`). Two decisions are made:

- Formula/term nodes will be **interned**: equal node ⇒ same ID, bound variables as
  de Bruijn indices, mirroring fol-zfc's registry.
- The Isabelle dialect will **not** transcribe raw `ZApp`. The reader recognises Isabelle's
  application spines (`ZApp(ZApp(ZConst "Pure.imp", a), b)`) as dialect nodes (`imp(a, b)`).

To choose the node kinds, the design session needs to know **every shape in which
application actually occurs in the export**, and which shapes a recogniser would NOT cover.
Nobody has measured that. That is this task.

## Read first (primary sources, not summaries)

1. `CLAUDE.md` in the repo: the rules apply to you. Especially: no fallbacks, a count is
   evidence never a premise, `(theory, serial)` keys (serials collide across theories),
   run everything capped.
2. `Isabelle2025-2/src/Pure/zterm.ML` under `~/repos/isabelle-study/`:
   lines 11-27 (`ztyp`, `zterm`), 249-258 (`zproof`), 1460-1506 (the XML encoder, the
   ground truth for tags and child order).
3. `isa2fol surface` (`Sources/Reader/Surface.swift`) and `docs/SOURCE_SURFACE.md`: how an existing census is
   built and documented. It loads `~/repos/isabelle-study/bin/isa-deps` (the YXML decoder and
   `ZPROOF` tag map); reuse that loading pattern.
4. `~/isabelle-pure-metalogic.md` §0 and §A: reading notes. Treat their numbers as claims to
   reproduce, not facts.

## The export (verified facts)

⚠ **Every figure in this file was measured on the pre-2026-09-25 export, which merged two
Isabelle builds.** `data/zf_export` is now a local cache built by `scripts/03-export-zf.sh`
from ONE build: 15,946 proof files, every citation resolves, and serials differ from build to
build — re-measure every anchor below, and never record a serial as an example (name the
theorem instead).

- `data/zf_export/<theory>/proofs/<serial>`: 16,798 files, 40 theories.
  Envelope: `pair tfrees (pair frees (pair prop proof))` (`proofterm.ML:2062`, `export_proof`).
- `data/zf_export/<theory>/theory/consts`: constant declarations with types. Use them to get
  each constant's declared type, and hence its arity.
- **Tag 0 is `ZConst` in a zterm and a type in a ztyp.** Decode by position (encoder
  order), never by tag alone.
- A free `ZVar`'s type may be absent (the `typed_vars` flag, `zterm.ML:1475`). The type is
  then in the `frees` header.
- A theorem citation (`ZConstp` / `ZThm`) exports attributes `[serial, theory, name, index]`
  and its type arguments as children. **It carries no statement and no term instantiation**:
  term instantiation is the surrounding `ZAppt`s.

## Questions to answer

Split every count by **statements** vs **terms inside proofs** (`ZAppt` arguments,
`ZAbsp` hypotheses, `ZHyp`). Give two populations, as in the notes: **P1** = all 16,798
files, **P2** = the 3,616 named ZF theorems (`isa2fol surface` counts it per session).
For every non-standard shape, give **≤ 3 examples as `(theory, serial)`**.

1. **Spine heads.** For every maximal `ZApp` spine, what kind is the head: constant, free
   `ZVar`, schematic `ZVar`, `ZBound`, or `ZAbs` (a β-redex)? For constant heads, record
   (name, number of arguments applied) against the arity of the **instantiated** type.
   Report it both ways, because a polymorphic constant at a function type gains arrows.
   Classify each as fully applied, partially applied, or over-applied.
2. **Binder arguments.** For every constant argument position whose type is a function
   (`Pure.all`, `IFOL.All`/`Ex`/`Ex1`, and every ZF binder: `Collect`, `Replace`, `RepFun`,
   `Lambda`, `Sigma`, `Pi`, `The`, …, found from the types, not from a list): is the
   argument a `ZAbs` or something else (η-short: a variable, a constant, a partial
   application)?
3. **Bare `ZAbs`.** A `ZAbs` that is not the argument of a constant: where, and how many.
4. **Type arguments.** For each polymorphic constant, the multiset of instantiations.
   Which contain a type variable, and where? Reproduce or refute the claim
   "12 of 3,616 named ZF theorems carry a type variable" (`CLAUDE.md`).
5. **Pure-internal constants.** `Pure.prop`, `Pure.conjunction`, `Pure.term`, `Pure.type`,
   `Pure.sort_constraint`, and `OFCLASS`, in statements and in proofs.
6. **Bound variables in proofs.** A `ZBound` inside a term inside a proof may refer to a
   proof-level `ZAbst` binder, not a term `ZAbs`. Establish the de Bruijn convention from
   `zterm.ML` and confirm it on the data: do term indices count `ZAbst` binders? Is every
   `ZBound` resolvable to a binder whose type is known?
7. **Citations.** Resolve every citation to a file by `(theory, serial)`. The design
   session found **838 unresolved citations** with its own quick decode. Reproduce that
   number, then list and explain the unresolved ones.

**Anchors that validate your decoder:** 16,798 files · 797,924 `ZAppt` (it also appears in
`~/isabelle-pure-metalogic.md` §A) · 1,780,478 proof nodes (from the design session's
decode; reproduce it or explain the difference).

## Method: constraints

- **Output:** `scripts/isa-shapes.py`, stdlib only, which prints markdown tables.
  `docs/ISA_SHAPES.md` is its output plus a short reading of it. **Every number in the doc
  must come from the script.** State the regenerate command at the top.
- **Unknown tag, unexpected child count, or an unresolvable type: exit non-zero naming
  `(theory, serial)`.** Never skip a file or bucket it as "other" (CLAUDE.md rule 1).
- Run it through `MEM=16G scripts/capped.sh python3 scripts/isa-shapes.py`.
- **Touch only** `scripts/isa-shapes.py` and `docs/ISA_SHAPES.md`. Do not edit `Sources/`,
  `Tests/`, `DESIGN.md`, `docs/FOUNDATION.md`, `CLAUDE.md` or `.claude/`. The design
  session is changing them.
- **Facts, not design.** Do not choose node kinds. If the data suggests something, you may
  add a last section headed **"Implications — proposal, not decided"**.

## Where, and how to communicate

- **Work in your own worktree and branch:**
  `git -C /home/arthur/repos/isa2fol worktree add ../isa2fol-census -b census/isa-shapes feature/exists-descent`.
  This task file is at `/home/arthur/repos/isa2fol/.claude/tasks/ISA_SHAPE_CENSUS.md`.
  Read it from there.
- **Commit** to `census/isa-shapes` in small steps. Never push, and never touch other branches.
- **The interface is the doc.** The design session will read `docs/ISA_SHAPES.md` and the
  script on your branch, not your conversation, so the doc must stand on its own.
- **Stop and ask the user (who relays to the design session)** when:
  - a finding contradicts something stated in this file;
  - the export has a shape the encoder in `zterm.ML` does not explain;
  - answering needs a design decision.

  Do not work around any of these; record them under **"Open questions"** in the doc as well.
- **Final message to the user,** at most 15 lines: branch and commit sha; the regenerate
  command; whether each anchor was reproduced; the three most consequential findings with
  their counts; the open questions.

## Done when

The script runs clean over all 16,798 files. Every anchor is reproduced or its difference
explained. Questions 1-7 each have counts for P1 and P2, split by statement vs proof, with
examples for every non-standard shape. The unresolved-citation list is complete.
