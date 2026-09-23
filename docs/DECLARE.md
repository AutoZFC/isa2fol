# DECLARE — the declaration framework

**STATUS: DESIGN ONLY.** No code. `src/replay/` as written is superseded by this —
see §9.

**Scope: one Isabelle theorem statement → one `decl::Decl` in the target.** Proofs
are out of scope, deliberately and completely. Declarations have no order among
themselves (§7), so this is the part that can be got right on its own.

---

## 1. The rule this exists to enforce, and it is TWO-SIDED

| binder | target | why |
|---|---|---|
| object, sort `i` | `forall x. (set(x) -> …)` / `exists x. (set(x) & …)` | R3, S6 — an unguarded `∀x` quantifies over CLASSES and is not the Isabelle theorem |
| **class** | `forall A. …` — **NO GUARD** | a class is not a set, so `set(A)` makes the claim **FALSE, not redundant** |
| propositional, arity 0 | a schema parameter in the header — **not quantified at all** | S4: `o` is not `i`, and a truth-value set is what S4 refuses |

Guarding is easy. **Knowing which side a binder is on is the entire problem**, and
it is decided in §5's first pass, not at the guard site.

### ⚠ THE IR CANNOT EXPRESS THE DISTINCTION, AND THE GATE FALSE-POSITIVES ON IT

`ir::fol::Formula::Quant { kind, var, body }` carries no binder sort. The only
thing that marks a class binder today is the `_C`-prefix naming convention, which
nothing reads. Measured:

```
RENDERED: (forall x. (set(x) -> (forall _C0. (elem(x, _C0) -> elem(x, _C0)))))
G5 REPORTS UNGUARDED: [(Forall, "_C0")]
```

`gate::guards::unguarded` reports a **correct** S4 class quantifier as an R3
violation. So G5 is unsound in one direction and absent in the other: it cannot
catch a class that IS guarded — the error that silently makes a claim false.

**The fix is one field.**

```rust
enum Binder { Set, Class }
Formula::Quant { kind, var, binder: Binder, body }
```

Then guard insertion is driven by `binder`, G5 becomes two-sided and total, and
the naming convention stops being load-bearing. Everything else in this document
depends on this change landing first.

---

## 2. Where the foundation is injected

A declaration cites nothing, so the proof-side injection point (a `use`) has no
analogue here. The declaration-side analogue is the **vocabulary**: what each
Isabelle constant becomes in the target.

Two sources, and they must stay distinguishable:

| source | supplies |
|---|---|
| **`base/`** — our own `.fol` foundation | `elem`, `eq`, `set`; `pmem`/`tmem` (S5's lookup vocabulary); the 19; the tiers |
| **translated Isabelle formalization under NBG** | one `C_GRAPH` per term constant — `Pair`, `Sigma`, `Upair`, … |

```rust
trait Vocabulary {
    fn constant(&self, isabelle_name: &str) -> Option<Entry>;
}
struct Entry { pred: String, arity: usize, source: Source }
enum Source { Base, Translated }
```

`Vocabulary` is the declaration-side seam, exactly as `Provider` is the proof-side
one. A constant absent from it is **Waiting**, not Refused — §18's L1.

**⚠ ISABELLE'S `Pair` IS NOT THE COMPILER'S TUPLE.** FOUNDATION §3: Isabelle's own
pairs stay Kuratowski; "an Isabelle pair is a VALUE inside an assignment, never an
assignment." `Source` exists so this stays visible: a `Translated` entry is what
Isabelle means, a `Base` entry is ours, and silently serving one for the other is
FOUNDATION §4's failure mode at a new site.

---

## 3. The three binder-ish kinds, named once

Conflating any two is how the current renderer ended up with a 13-field `Ctx`.

| kind | in the target | closed by |
|---|---|---|
| **object** | a guarded quantifier | R3 closure over free `i`-variables |
| **class** | an unguarded quantifier, or a class PARAMETER | unguarded outer `forall A.` |
| **schema parameter** | `schema n [P(1), Q(2)]: …` | the declaration header — never quantified |

A class parameter and a schema parameter are different objects: the first is a
first-order variable the target quantifies, the second is a kernel metavariable.
`Rendered` already carries both (`class_params`, `schema_params`) and the
distinction is invisible in the formula.

---

## 4. Kinds, and why this is the only hard pass

Every variable gets exactly one kind, decided from IR1's sorts plus its
application arity:

| source shape | kind |
|---|---|
| `Var` at sort `i` | **Object** |
| `?P` applied at arity ≥ 1, or `⋀P` with `P` so applied | **Class**(arity) |
| `?P` at arity 0 | **Prop0** — a schema parameter (S4) |
| a variable at a function sort, applied | **MetaFn**(arity) — S5, a class parameter with a `FunctionGraph` obligation |
| a `Const` | resolved through §2's `Vocabulary` |

**⚠ ARITY IS A PROPERTY OF USE, NOT OF THE BINDER.** `statement/mod.rs`'s `Quant`
arm already records this: "the class is allocated lazily at first application, so
the body renders BEFORE the binder is written." A pass that decides kinds by
looking only at binders will get `⋀P` wrong. D1 must see the whole statement.

---

## 5. The passes

```
   meta::Prop                          IR1 — FROZEN (§14)
       │
       │  D1  KIND      assign every variable exactly one kind (§4)
       ▼                consults: sorts + application arity
   Kinded               ✓ no variable is Unknown
       │
       │  D2  TERM      S1 — every compound `i`-term becomes a fresh variable
       ▼                plus a graph atom. consults: Vocabulary (§2)
   Relational           ✓ EVERY `i`-term is a variable
       │
       │  D3  ATOM      elem / eq; `P x ↦ elem(x,A)`; pmem / tmem
       ▼
   Bare                 ✓ no Isabelle constant remains
       │                ✓ binders are KINDED and carry NO guards
       │  D4  GUARD     Set → set(·) interleaved.  Class → nothing.
       ▼                purely mechanical, driven by §1's Binder
   Guarded              ✓ two-sided G5
       │
       │  D5  DECL      claim vs schema; the name; the closure; the text
       ▼
   decl::Decl           ✓ round-trips through decl::parse
```

**Every arrow has a decidable invariant.** That is what makes these passes and not
a fold — and it is the difference from today, where all five happen inside one
recursion with a 13-field context (`statement/mod.rs`, 821 lines).

**D4 is trivial by construction.** All the difficulty is upstream in D1 and D2,
which is the point of separating them: the guard rule stops being a thing you can
get wrong and becomes a thing you can only fail to *decide*.

---

## 6. The invariants, as gates

| after | invariant | decides |
|---|---|---|
| D1 | every variable has a kind | a missing sort is a refusal, never a default |
| D2 | no compound `i`-term | S1 at statement level — §14's IR3 analogue |
| D3 | no Isabelle constant | the Vocabulary was total on this statement |
| **D4** | **every Set binder guarded AND every Class binder unguarded** | **G5, two-sided** |
| D5 | `decl::parse(text) == decl` | the emitter and the parser agree |

D4's second conjunct is new and is the one that catches a false claim.

---

## 7. Order

**None among declarations.** A statement renders from its own term plus the
Vocabulary; no declaration reads another. The only ordering anywhere is the
constant layer — FOUNDATION_TO_FOLZFC §18's L0→L1→L2 — and it enters through §2's
`Vocabulary` alone.

So the driver is: for each theorem, independently, D1→D5. A constant below L1
yields `Waiting { on }`; everything else is `Declared` or `Refused`. Embarrassingly
parallel, resumable, and with no schedule.

---

## 8. What the corpus says this is worth

From `replay::tests::the_corpus_ledger` over all 16,798 — the numbers survive the
rewrite because they are measurements of the statement path, not of the framework:

| | |
|---|---|
| declared today | **868** |
| **waiting** on a constant below L1 | **15,243** — D2's Vocabulary, i.e. §18 |
| genuinely **refused** | **705** |

Of the 705, **463 are `sort 'a is outside I \| O \| Prop \| Arrow`** — polymorphism,
FOUNDATION_TO_FOLZFC §11.0's `split` finding reaching far past `split`. It outranks
every other genuine cause by an order of magnitude and it is a **D1** problem.

**So the work-list this design implies is: D1's polymorphism (463), then D2's
Vocabulary (15,243).** Nothing else is close.

---

## 9. What dies

`src/replay/` as written. It was built around a proof-order closure the kernel does
not require — the checker reports `Conditional (1): ~ thm_a (depends on: lemma_b)`
and exits 0, so a proof is checked *relative to* its citations and the closure is
the checker's own arithmetic.

What survives as ideas, to be rebuilt where they belong:

| idea | keep because |
|---|---|
| `Verdict` / `Ledger` | separating **Waiting** from **Refused** changed the reading of the corpus by 20× |
| `Levels` (§18 L0/L1/L2) | it is the Vocabulary's state, and §18 is real |
| the citation graph | as **analysis** — blame and cone over the ledger — never as a schedule |
| `Conditional` | a third verdict the kernel already computes and we were discarding |

⚠ **DO NOT PORT `pipeline.rs` OR `mod.rs`'s round loop.** They encode the order
assumption this document removes.
