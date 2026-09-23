# REPLAY — the translation framework

**STATUS: DESIGN + SKELETON.** `src/replay/` runs; the proof phase refuses
everywhere. That is the designed state — §5 explains why the refusals are the
product.

`docs/DECLARE.md` is the declaration pipeline this framework drives. Read it for
what happens *inside* PHASE 1; read this for the driver around it.

---

## 0. The defect this fixes

Two ends built to meet, empty middle:

| | |
|---|---|
| **front** | `export/lower.rs` — YXML → IR1 (`meta::Proof`). Built |
| **middle** | §14's H → S → E → LOWER over proofs. *Nothing consumes `meta::Proof`* |
| **back** | `proof_builder::Script` → `emit` → `unit::check` → kernel. Built |

`Script`'s 26 methods are exactly `nd::Rule`'s variants, so the ends were built to
fit. Nothing drives one from the other. `replay/` is that middle's shape.

---

## 0a. The shape

**There is no function that does both phases.** Each is an entry point; the
artifact between them is a file.

```
 ╔═ PHASE 1 ═ declare::phase(&corpus, found, select) ════════════════════════╗
 ║                                                                           ║
 ║   per theorem, order-free:                                                ║
 ║     D1 KIND → D2 TERM → D3 ATOM → D4 GUARD → D5 DECL   (docs/DECLARE.md)  ║
 ║              ▲ Foundation::entry — the vocabulary, and its §18 level      ║
 ║     ⇒ Declared | Waiting{on: C} | Refused                                 ║
 ║                                                                           ║
 ║   loop: found.advance();  promoted == 0 ⇒ STOP, the waiting set is final  ║
 ╚═══════════════════════════════════════════════════════════════════════════╝
        │
        ▼  (Declarations, Ledger<Declaration>, rounds)
        │
   Declarations::write(dir)  ─────►  decls.fol.def   ←── THE ARTIFACT
                                          │
   Declarations::load(path)  ◄────────────┘   a process that never ran PHASE 1
        │
        ▼
 ╔═ PHASE 2 ═ prove::phase(&corpus, found, &decls, select) ══════════════════╗
 ║                                                                           ║
 ║   per theorem the ARTIFACT names — looked up BY NAME, as a `use` resolves ║
 ║     Lower → H → S → E → LOWER → emit → check                              ║
 ║            ▲ Foundation::{ex,uniq,cong,class}     ◄── decls.fol.def is    ║
 ║     ⇒ Proved | Conditional{on} | Refused              the ONE dep         ║
 ╚═══════════════════════════════════════════════════════════════════════════╝
        │
        ▼  Ledger<Proving>
```

**Two ledgers, one per phase.** A joint view is a join at report time, never a
shared row both phases write.

---

## 1. The three corrections this design encodes

Each was a real mistake, each is silent if repeated.

### ⚠ 1a. THERE IS NO PROOF ORDER. The kernel checks modularly.

Measured, with `thm_a` citing an unproved `lemma_b`:

```
Conditional (1):
  ~ thm_a (depends on: lemma_b)
OK: 2 claim(s) checked (0 proved, 1 conditional, 1 unproved)      EXIT=0
```

The checker verifies A's derivation **is valid from B**, records the dependency by
name, and refuses to call it Proved. `unit.rs:129-131` already parses all three
buckets. So "A is blocked because B is not proved" is not a constraint the target
imposes — **it was invented.** The previous framework gated on it and left 16,451
theorems unattempted on round 1, discarding the measurement instead of taking it.

**A proof needs its citations DECLARED, never PROVED.** Closure is the checker's
own arithmetic (`Proved` vs `Conditional`), computed, not scheduled.

### ⚠ 1b. THE TWO PHASES HAVE DIFFERENT INPUTS, NOT DIFFERENT HALVES OF ONE PASS.

DECLARE reads a statement and the Foundation. PROVE reads a proof term and the
declaration artifact. Gating DECLARE on anything PROVE needs reported **18**
declared where the truth was 868.

### ⚠ 1c. WAITING IS NOT REFUSED.

A constant below §18's L1 is `Waiting` — a later round may clear it. Merging the
two reported "15,930 statement refusals" where the truth is 15,243 waiting and
**705 refused**. A 20× misstatement of the work.

---

## 2. Why this is buildable now — the boundaries are frozen

| boundary | frozen by |
|---|---|
| `meta::Proof` — what the export lowers into | **mechanically**: `ir/meta_tests.rs`'s exhaustive `frozen_*` matches do not compile if a variant is added |
| `Provider` — what the foundation answers | **by specification**: "an obligation outside {EX, UNIQ, CONG, class-existence} is a specification change, not a refusal" (§14) |

FOUNDATION §3's open atom question lives entirely behind `Provider::class`. The
framework never sees it; when §3 resolves, one impl changes.

---

## 3. Two phases, and the artifact between them

**The phases communicate through `decls.fol.def`, not through memory.**

That is not a convenience. It is what makes the design work:

| it gives | because |
|---|---|
| **resumability** | DECLARE today, PROVE next week; the def is the state |
| **a constant-size dep list** | PROVE's check passes exactly ONE dep — the declaration artifact. `use B` resolves against B's *declaration*; B's proof is irrelevant |
| **parallelism** | 16,798 independent checks, no shared mutable context |
| **an inspectable intermediate** | the declaration layer is a thing you can read, diff, and hand to the kernel on its own |

The one-dep property retires the scaling problem the previous design left open —
transitive dep lists per theorem do not scale, and under this design they never
arise.

---

## 4. Order

**None between theorems, in either phase.** A statement renders from its own term
plus the Foundation; a proof needs its citations declared, which PHASE 1 already
guaranteed for every theorem it declared.

The only ordering anywhere is the **constant layer** — FOUNDATION_TO_FOLZFC §18's
L0 → L1 → L2 — and it enters through `Foundation` alone:

```
   CONSTANT LAYER (NBG)                    THEOREM LAYER (Isabelle)

   L0 DECLARED   signature, C_def
        │
   L1 DENOTING   C_EX C_UNIQ C_CONG ─────►  a STATEMENT mentioning C renders
        │                                            │
        │                                            ▼
        │                                     a THEOREM about C is translated
        │◄───────────────────────────────────────────┘
        ▼   §18's "characterised" route
   L2 GRAPHED    C_GRAPH ──────────────────►  a CLASS over C compiles
```

**A theorem declares when every constant in its statement is at L1. L2 of none.**
The arrow back lands at L2, and nothing the theorem layer consumes comes from L2 —
that is the whole soundness argument, and G6 is its gate.

The citation graph is kept as **analysis** — blame and cone over the ledger — never
as a schedule. Measured: 16,798 nodes, **acyclic**.

---

## 5. The ledger — two columns, never summed

```rust
pub enum Declaration { Declared, Waiting { on: String }, Refused(Refused) }

pub enum Proving {
    NotAttempted,                      // the declaration did not succeed
    Proved,
    Conditional { on: Vec<String> },   // the kernel's own word
    Refused(Refused),
}
```

One row per theorem, two independent verdicts. **Proved and Conditional are never
added.** Conditional-on-one-missing-lemma across 15,000 theorems would read as
triumph; §1c is the same lesson and it only has to be learned once.

`Ledger::blockers()` groups refusals by cause and ranks them. That ranking *is* the
work-list, measured rather than argued.

---

## 6. Three seams, and nothing else is generic

| seam | varies because |
|---|---|
| `Foundation` | the mathematics is unfinished. It is the **vocabulary** (what an Isabelle constant becomes, and at which §18 level) AND the **obligations** (`Provider`'s frozen four). `foundation::Bare` is the day-one impl: everything at L0, every obligation refused |
| `Sink` | tests need memory, runs need disk |
| `Select` | one theorem, one theory, or the corpus — the same driver for a unit test and a full run |

`Foundation::entry` and `Foundation::advance` add **no obligation** — they report
where the constant layer has got to and ask it to take a step. §14's freeze holds.

**⚠ `Entry` CARRIES ITS SOURCE.** `Source::Base` is our `.fol` foundation;
`Source::Translated` is Isabelle's own constant recast under NBG. FOUNDATION §3:
Isabelle's pairs stay Kuratowski, "a VALUE inside an assignment, never an
assignment". Serving one where the other belongs is §4's failure mode at a new
site, and `Source` is what keeps it visible.

---

## 7. The rails

| never | enforced by |
|---|---|
| emit `UNPROVED` | `gate/linker.rs:50` — "R2 admits no debt" |
| emit a bare `axiom` outside `base/` | `gate::admission` |
| count `Conditional` as `Proved` | separate columns; `Ledger::proved()` counts one |
| fall back when a stage cannot proceed | every stage returns `Result<_, Refused>` |
| promote a constant from inside `replay/` | promotion is `Foundation`'s, always |
| hold the corpus in memory | §8 |

**Nothing mathematical belongs in `replay/`.** If a change here needs to know what
a class is, it is in the wrong file.

---

## 8. Scale

16,798 statements; ~798k `AppT` nodes. §14 lists "three intermediate trees over the
whole proof-term corpus: memory and time unmeasured" as unverified. The one OOM
ever traced was exponential `Unit::deps` nesting in `constant::walk` — **not
parallelism** (CLAUDE.md rule 10).

Streaming per theorem, the ledger holds verdicts (small), Units go to the `Sink`.
§3's one-dep property is what keeps `Unit::deps` from nesting at all.

---

## 9. Open decisions

1. **`unit::check` rejects `Conditional`** — `Buckets::bad()` is
   `conditional > 0 || unproved > 0 || …`. PHASE 2 must *observe* Conditional while
   `Proved` stays the only thing counted. That is a deliberate change to a stated
   invariant and belongs in FOUNDATION_TO_FOLZFC before it is made.
2. **`Formula::Quant` has no binder sort**, so G5 cannot tell an object binder from
   a class binder and reports a correct class quantifier as an R3 violation
   (DECLARE.md §1, measured). One field fixes it; DECLARE's D4 depends on it.
3. **`main.rs` has no replay mode** — 57 lines, `--scan` only. Until it has one,
   the framework runs only from a test.
4. **Two statement paths.** The framework uses IR1 (`lower::prop` →
   `from_meta::prop`, §14's route); the censuses use `linearize::convert_term`.
   Measured: **868** vs **1,372**. ⚠ ~504 statements render on the legacy path and
   not through IR1. Unexplained; do not assume either is the real number.

---

## 10. Layout

```
replay/
  mod.rs          Corpus, Select -- NO run(); the phases are the API
  verdict.rs      Stage, Refused, trait Verdict, Declaration, Proving, Ledger<V>
  foundation.rs   Level, Levels, Source, Entry, trait Foundation; Bare
  declare.rs      PHASE 1 + Declarations (the artifact, loadable from a file)
  prove.rs        PHASE 2 -- refuses today
  sink.rs         trait Sink (PHASE 2's units); MemSink, DirSink, decls_path
```

**Two entry points: `declare::phase` and `prove::phase`.** Pinned by
`phase_2_can_start_from_a_file_phase_1_never_handed_it`.

⚠ **A `run()` THAT CHAINS THEM IS THE MISTAKE THIS LAYOUT EXISTS TO PREVENT.**
The first attempt had one; `prove` then took an in-memory `Declarations` with a
`BTreeMap<ThmId, String>`, never read the def, and neither phase could run alone.
The file handoff was fiction while the design doc claimed it.

---

## 11. What the corpus says

`replay::tests::the_corpus_ledger` (ignored — a measurement, not a gate), whole
export, ~4s, with `Bare` in place. **Both phases run; PHASE 2 attempts every
declared theorem.**

| PHASE 1 DECLARE | |
|---|---|
| indexed | 16,798 — every one gets a row |
| **declared** | **868** · artifact = 868 decls, 79,314 bytes |
| **waiting** on a constant below L1 | **15,243** |
| refused | 687 |

| PHASE 2 PROVE | |
|---|---|
| attempted | **868** — exactly what the ARTIFACT names, no closure gate |
| proved / conditional | 0 / 0 — the passes refuse, as designed |

Waiting on: `Nat_2enat` 907, `Ordinal_2eOrd` 789, `Ordinal_2elt` 763,
`List_2elist` 501, `Int_2ezless` 435, `ZF_Base_2eSubset` 366.

Refused, by cause — **the whole work-list, both phases, one table**:

| n | stage | why |
|---|---|---|
| **794** | eliminate | PASS S is not built |
| **463** | kind | sort `'a` is outside I \| O \| Prop \| Arrow |
| 74 | normalise | PASS H is not built: a beta/eta redex |
| 49 | kind | meta conjunction |
| 26 | kind | `` `W` at 0 argument(s) heads no Pure form`` |
| 24 | kind | sort `'a @ Pure.eq` outside the grammar |
| 20 | atom | no rendering rule for `==` at sort prop |

### Two findings the old design could not see

**⚠ 794 OF THE 868 DECLARED PROOFS ARE ALREADY βη-NORMAL.** `794 + 74 = 868`:
every declared theorem reaches either PASS S or PASS H, and only **74** carry a
redex at all. PASS H is a small job; **PASS S is the wall**, and it is the largest
single entry in the entire ledger.

The previous design reported **18** at eliminate, because its invented proof-order
closure stopped the other 850 from being attempted (§1a). That is a 44× difference
in the measurement, from removing a constraint the kernel never imposed.

**Polymorphism is the whole declaration story** — 463 of 687, `'a` outside §14's
sort grammar. It is §11.0's `split` finding reaching far past `split`, and a
DECLARE **D1** problem.

So the work-list, ranked and measured:

1. **PASS S** — 794 proofs
2. **D1 polymorphism** — 463 statements
3. **the Vocabulary** — 15,243 waiting, §18's constant layer
4. **PASS H** — 74 proofs
