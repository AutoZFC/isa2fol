# Foundation → fol-zfc

Companion to `FOUNDATION.md`. That document says **what must hold**. This says
**how it lands in the checker's concrete language** — what the checker
guarantees, what it does not, and the plan that follows.

Claims marked **✓** were verified against the checker; the probe is named and
lives in `phase2_probes/`. Everything else is an argument, and is labelled as
one. The distinction is not decoration: every wrong turn in this document's
drafting came from asserting something a two-minute probe would have settled.

**Reference convention:** a bare `§n` cites *this* document; the other is always
named, as `FOUNDATION §n`.

> **⚠ FOUNDATION §3 HAS BEEN REPLACED and this document has NOT been reworked to
> match.** The class context is now an ASSIGNMENT (a function from an index set to
> V), not a position-indexed tuple: the source owns the coordinate order, so the
> canonical discipline that makes iterated pairing adequate is unavailable, and
> interior access forces a placement law per arity and position. Everything here
> about width, contiguity, seeds, `mem_n`, Expansion and the placement family —
> §11.1, §18, and the phase tables — describes `FOUNDATION §3a`, the SUPERSEDED
> construction the code still realises. Read it as a record of what is built, not
> of what is intended.

---

## 0. One correction to FOUNDATION.md — LANDED

**FOUNDATION §1 axiom 3 is a biconditional.** It formerly read

```
3.  ∀A B. (∀u. elem(u,A) ↔ elem(u,B)) → eq(A,B)
```

but must be `↔`. The `←` direction is the only route from `eq(A,B)` back to
membership agreement, and without it `eq(A,B) → (u∈A → u∈B)` is underivable:
Extensionality runs the wrong way and hygiene axiom 2 (`elem_first_subst`)
substitutes only on the *left* of `∈`. `eq` stays a primitive predicate — nothing
is defined away and the count stays 19.

Two things depend on this beyond ordinary congruence reasoning:

- The class-existence compiler (§5) **cannot run** without it. Its normalisation
  phase rewrites every equality atom `Δ = Γ` into `∀z.(z∈Δ ↔ z∈Γ)`, which is
  exactly the missing direction.
- `set`-congruence, `eq(A,B) → set(A) → set(B)`, is then a *theorem* rather than
  a gap: Pairing on `set(A)` yields `p` with `set(p)` and
  `∀u. u∈p ↔ (eq(u,A) ∨ eq(u,A))`; `eq(A,A)` puts `A∈p`; `elem_first_subst`
  gives `B∈p`; `members_are_sets` gives `set(B)`. This pins Pairing's exact
  statement — the derivation needs the `eq`-form, not a weaker one.

---

## 1. What the checker is

`N1` names the kernel as sole arbiter. That is true of the **logic core** and of
nothing above it:

| layer | what it is | arbiter? |
|---|---|---|
| ND rules over FOL formulas | `and_intro`, `forall_elim`, scope/dependency tracking | **yes** |
| `axiom` declarations | whatever text you write | no |
| `schema` / `schema_inst` | a macro table | no |
| `@def(p)` | an annotation marking a predicate as defined, blocking redefinition | no |
| the five-bucket report | an accounting tool over claims | no |

So **R1 and R2 are our obligations, not properties of the kernel.** The checker
accepts any axiom you write and any schema you declare, exactly as a C
preprocessor accepts any macro. That is correct behaviour for a macro layer, not
a defect — and it means the enforcement has to live on our side.

### The checker cannot report a failed schema ✓

`probes: schema_link_gate.{def,proof}`

A schema is not a "claim", so it never enters the classification.
`runner.cpp:48` marks it proven *before* dispatch and nothing un-marks it on
failure — whereas the explicitly-`UNPROVED` path (`runtime.cpp:137-145`) marks
both proven *and* unproved, and so classifies dependents correctly. The gap is
specific to **failed** implementations, not admitted ones. Running the
same file with a correct and a broken schema implementation:

```
stdout    Proved (1): demo  /  OK: 1 claim(s) checked      IDENTICAL
exit      0                                                 IDENTICAL
stderr    (empty)  vs  ERROR: disjE: ... or_elim: ...        the only difference
```

The consumer of a broken kernel classifies **PROVED**. This is R2's exact failure
mode presenting as success. It is not a bug to fix in the checker; it is the
reason §2 exists.

---

## 2. The linker — the gate we own

"No declaration without implementation." A schema is a kernel; a kernel with no
body is a link error. The check, in full:

```
exit status 0
stderr empty                                  ← the only channel carrying kernel failures
FAILED, MISSING, UNPROVED, CONDITIONAL all empty
every declared schema has a proof block, and it is not UNPROVED   ← static, our own files
```

Required-to-reject case: `schema_link_gate` above. An instrument that cannot fail
proves nothing (`FOUNDATION.md` §5), and this one has a case it must reject
before it ever sees real output.

---

## 3. The base

`FOUNDATION.md` §1's 19, transcribed, with axiom 3 as `↔` per §0. `eq` is an
ordinary binary predicate — no `@def`, nothing defined away.

What that buys, and what it costs:

| fact | source |
|---|---|
| `eq(A,B) → (u∈A → u∈B)` | axiom 3, `←` direction |
| `eq(x,y) → (x∈S → y∈S)` | axiom 2, `elem_first_subst` |
| `eq` refl / sym / trans | axiom 3 + `↔` reasoning |
| `eq(A,B) → set(A) → set(B)` | theorem via Pairing (§0) |

**Consequence for the kernel-op budget.** The checker's `eq_sym` and `eq_subst`
match a predicate *named* `eq` by name (`stack.cpp:657`, `:680`). Both are
derivable from the table above, so neither is needed, and emitting either would
be admitting a principle outside the 19. `Step` already makes `EqSubst` and
`IotaElim` unrepresentable; **`Step::EqSym` joins them.**

Emittable ops are exactly those that are pure logic — no knowledge of any
signature symbol:

```
fix  assume  use  let  qed
forall_intro  forall_elim  implies_intro  implies_elim
and_intro  and_elim_l  and_elim_r
or_intro_l  or_intro_r  or_elim
not_intro  not_elim  bottom_elim
iff_intro  iff_elim_l  iff_elim_r
exists_intro  exists_elim
double_neg_elim
schema_inst
```

Banned: `eq_subst`, `eq_sym`, `iota_elim`.

---

## 4. Schemas are kernels

A schema is a GPU kernel in a compute graph: declared once, implemented once,
called many times. The implementation is a proof of the body with every schema
variable **uninterpreted** — which is precisely `FOUNDATION.md` §1 R2's
parametric criterion, and it is what makes each expansion sound.

**Definition.** A schema is *implementable parametrically* iff there is a single
proof of its body from the 19 in which each schema variable occurs only as an
opaque predicate symbol — the proof never inspects its structure, and never
requires a class whose extension is `{x : P(x)}`.

### What is implementable

**The logic layer.** ✓ `probes: logic_kernels.{def,proof}` — `conjI`, `disjE`,
`spec` all prove with `P`, `Q`, `R` as `SchemaVar` nodes. The whole IFOL/FOL
layer is shared kernels, not inlined per call site.

**The ZF operations — with the class as a parameter.** ✓ This was the
architectural question, and the answer is yes. `probes:
collect_kernel.{def,proof}`, `replace_kernel.{def,proof}`:

```
schema collect_char [P(1)]:
  ∀A C. (∀u. set(u) → (u∈C ↔ P(u)))            ← the class arrives as a hypothesis
      → set(A) → ∃c. set(c) ∧ (∀x. set(x) → (x∈c ↔ (x∈A ∧ P(x))))
```

Proved from axiom 17 alone, `P` never inspected. `replace_char [P(2)]` has the
same shape against axiom 16, deriving `Fun(F)` from the graph hypothesis plus
single-valuedness of `P`. `The` needs no class at all — uniqueness is a
hypothesis and the `∅`-default branch is pure logic — so `The`-derived constants
are markedly cheaper than `Collect`/`Replace`-derived ones, which matters because
S3 routes recursion back through `The`.

### What is not implementable

Only the **unconditional** form: `∃c. set(c) ∧ ∀x. set(x) → (x∈c ↔ (x∈A ∧ P(x)))`
with no class hypothesis.

*Argument (not a probe — an impossibility claim needs one).* A parametric proof
is a derivation in the language extended by an uninterpreted `P`, so it stays
sound when *any* formula is substituted for `P`, including formulas with class
quantifiers. A uniform proof of `∃C. ∀u.(u∈C ↔ P(u))` would therefore yield full
impredicative comprehension — Morse–Kelley, which proves `Con(NBG)` and is not
conservative over ZFC. FOUNDATION §1 rules this out in the same breath it forbids
`set(x) := ∃C. x∈C`.

The remedy is to **add the hypothesis, not delete the schema**. This is how to
read FOUNDATION §1's "delete it and instantiate its uses at concrete formulas": what gets
instantiated at concrete formulas is the *class argument*.

---

## 5. Classes are a compiler, not an axiom

`FOUNDATION.md` §3 is a mechanisation of NBG's **Class Existence Theorem**, and
that theorem is what turns a metalinguistic schema into first-order content:

| layer | object | status |
|---|---|---|
| ZFC | Replacement **schema** — one axiom per formula φ | infinitely many axioms |
| NBG | Replacement **axiom** — `∀F. Fun(F) → ∀x. set(x) → ∃z. …` | **one** axiom, `F` a class variable |
| bridge | build the class `F` with `⟨u,v⟩∈F ↔ φ(u,v)` for concrete φ | a **metatheorem** — i.e. a compiler |

A meta-level function becomes first-order as its **graph, held as a class
parameter**: `Fun(F) := ∀x y z. (⟨x,y⟩∈F ∧ ⟨x,z⟩∈F → eq(y,z))`.

The bridge cannot be an axiom — it quantifies over formulas. Hence FOUNDATION §3 is a
compiler in the pipeline, never something admitted. The **predicativity
restriction** (φ may quantify over sets, never over classes) is what buys both
finite axiomatisability and conservativity over ZFC; dropping it is MK.

### This is what S5's side condition means

Normalisation has exactly three rules, and its postcondition is that class
parameters **do not appear left of `∈`**:

1. `Y ∈ Γ` → `∃z.(z = Y ∧ z ∈ Γ)`
2. `Δ = Γ` → `∀z.(z ∈ Δ ↔ z ∈ Γ)`  ← needs §0's biconditional
3. `∨, →, ↔, ∀` → `¬, ∧, ∃`

So S5's "no graph is ever passed as an argument" and NBG's class-parameter
Replacement are not in tension. A class parameter right of `∈` is used *as a
class*; left of `∈` it is used *as a member*, i.e. as a set-valued argument. S5
bans the second. NBG Replacement is squarely the first.

We are stricter than the textbook in one place: rule 1 *handles* `Y ∈ Γ` by
finding a set coextensive with `Y` (correctly false when `Y` is proper), whereas
S5 says such sites must be eliminated. Read as deliberate — a reified graph
appearing as a value means the emitted statement is no longer the Isabelle
theorem, which is an N2 question the compiler cannot adjudicate.

`set(x)` compiles as `x ∈ V`, the hoisted-parameter case. Half is free
(`x∈V → set(x)` by `members_are_sets`); the other half, `set(x) → x∈V`, is a
proof debt on `V`'s construction, not a freebie.

### FOUNDATION §3 checked against the standard treatment

**Agrees:** T1–T4 are the Tuple Lemma; `T3 = A×V` (B5), `T1 = circ(T3)`,
`T2 = transp(T3)`. The Expansion count `1×T1 + (j−i−1)×T2 + (n−j)×T3` is
identical. FOUNDATION §3's explanation of *why* T1 fires exactly once — a compound block
substituted into slot 1 flattens — is sharper than the textbook's.

**FOUNDATION §3 is more careful in one place:** it notes T4 "needs Empty," which the
standard presentation omits. Correct: `Dom` drops a component, so recovering
`(y,x)` from `((y,x),z)` requires some `z` to exist.

**T4's route — settled ✓** `probes: tuple_lemma.{def,proof}`. **Both routes are
correct.** FOUNDATION §3's `Dom(transp(circ(circ(A×V))))` and the textbook's
`Dom(circ(transp(A×V)))` reach the *identical* triple class, verified by proving
one statement twice:

```
swap_triple_short   B5 → B7 → B6 → B4        4 closer applications
swap_triple_long    B5 → B6 → B6 → B7 → B4   5   ← FOUNDATION §3's route
        both:  ∀u v w. set → (tmem(u,v,w,D) ↔ pmem(v,u,A))
```

So FOUNDATION §3 is sound but not minimal. Prefer the short route when
mechanising — one fewer closer means one fewer guard-threading pass per swap, and
swaps fire once per `i>j` atom in Expansion.

**And `Empty` is needed exactly where FOUNDATION §3 says.** It appears once, in
T4's backward direction: `Dom` drops a component, so recovering `⟨y,x⟩` from
`⟨⟨y,x⟩,s⟩` requires *some* set `s` to exist. The standard presentation omits
this; FOUNDATION §3 does not.

**The `Vⁿ` intersection** remains a deliberate difference. The textbook intersects
to force tuple-purity; FOUNDATION §3 omits it, and is right to — §6 says why: the
statement is `∀x⃗` over *guarded* set variables, so nothing outside the guarded
range is ever asked about. Recorded as intentional, not an inherited oversight.

---

## 6. Set guards

**The rule.** Every quantifier arising from an Isabelle `i`-quantifier carries a
guard: `∀x::i. φ` → `∀x. set(x) → φ*`, and `∃x::i. φ` → `∃x. set(x) ∧ φ*`.
Non-negotiable, because conservativity is `NBG ⊢ σ* ⟺ ZFC ⊢ σ` stated for the
*relativised* `σ*`; our variables range over classes, Isabelle's `i` ranges over
sets, so an unguarded quantifier is a statement about a strictly larger domain.

**It breaks in both directions, and the kernel sees neither:**

| position | dropping the guard | consequence |
|---|---|---|
| conclusion (positive) | claim becomes **stronger** than the Isabelle theorem | N2 violation — we assert more than we proved, and it checks green |
| hypothesis (negative) | hypothesis becomes **stronger**, kernel becomes weaker | kernel is **uncallable** — §5's compiler output cannot discharge it |

The second is not hypothetical. The first draft of `collect_char` had the
hypothesis `∀u. (u∈C ↔ P(u))` unguarded. Since `members_are_sets` falsifies
`u∈C` for proper `u`, that biconditional *forces `P` false on proper classes* —
strictly stronger than "C is the class of sets satisfying P," and not what the
compiler hands back. It proved fine and would have linked to nothing.

**Discipline: always emit the guard.** Some guards are provably redundant — in
`∀u.(u∈z ↔ (u∈B ∧ u∈A))` both sides are `∈`-atoms, so a non-set falsifies both.
But that redundancy is a *theorem*, not a syntactic property, and deciding it
per-occurrence is exactly the local judgment that produced the bug. A redundant
guard costs proof steps; a missing guard costs faithfulness. Only one is
recoverable.

### The Compiler B ↔ kernel-library interface contract

```
compiler emits:   ∀u. set(u) → (u∈C ↔ φ(u))
kernel demands:   ∀u. set(u) → (u∈C ↔ P(u))
```

Mismatched guarding here is a silent link failure at *every* call site: kernel
proves, compiler proves, nothing connects. Pin it in writing before either side
is built.

---

## 7. The architecture

The gap between Isabelle/ZF (HOL over ZF) and fol-zfc (FOL over `{elem, eq, set}`)
is **exactly four** constructs. Nothing else in Isabelle's meta-logic reaches the
target:

| # | construct | eliminated by |
|---|---|---|
| 1 | meta-connectives `⟹ ⋀ ≡` | mechanical: `→`, guarded `∀`, `↔` / relational eq |
| 2 | the simply-typed λ-calculus in terms (`i⇒i`, `i⇒o`) | β-substitution — *always* available |
| 3 | terms of type `i` (target has no function symbols) | S1 — variable plus constraint |
| 4 | schematic variables `?P`, `?f` | S4 — schema parameter |

**Why (2) always works.** In every ZF constant's defining equation the
meta-function argument `F` occurs *only* in applied position `F(t)` with `F ∉ t` —
necessarily so, because the object language has no terms of function type, and
application is the only thing one can do with `F`. So β-substitution discharges
any concrete λ. This is the elimination theorem, and it is what makes the problem
tractable at all.

**Why predicativity is free.** Isabelle/ZF has no class type. So no translated
formula can quantify over classes, so §5's predicativity side condition can never
be violated *by construction*. This is the keystone of the whole soundness chain:

```
Isabelle/ZF ⊢ σ
  → σ and its proof quantify over sets only        (no class type)
  → every comprehension instance is predicative
  → each is an NBG theorem                          (§5, per instance, from B1–B7)
  → NBG ⊢ σ*                                        (σ relativised, §6)
  → ZFC ⊢ σ                                         (conservativity)
```

### Three components

*The three below are the architecture; §9 is the full component inventory, with
build status and the two risks this framing understates.*

**Compiler A — terms and formulas.** Isabelle term → guarded FOL formula, plus a
list of *obligations*. Implements the elimination table and S1. Emits no proofs.

**The kernel library** (§4) — parametric schemas, proved once.

**Compiler B — classes** (§5) — concrete predicative φ → a derivation of
`∃C. ∀x⃗. set(x⃗) → (⟨x⃗⟩∈C ↔ φ)`, discharging kernel hypotheses per call site.

The resolution of any meta-function argument is fixed by two questions and nothing
else — is the argument a concrete λ or a schematic `?P`, and is the enclosing
construct proposition-, unique-object-, or set-valued:

| | proposition-valued | unique-object-valued | set-valued |
|---|---|---|---|
| **concrete λ** | β-substitute — **A only** | contextual definition — **A + the `The` kernel, no class** | **A + B + kernel** |
| **schematic `?P`** | stays a schema; each *use* is concrete, hence one of the above |

### The design rule

> **Parameter-or-hypothesis.** A kernel may derive *nothing* about an
> uninterpreted parameter. Everything it needs about that parameter becomes an
> explicit hypothesis, discharged where the parameter is concrete.

This is what made `collect_char` work, and applying it systematically the complete
list of what a kernel can need is short:

1. **its class exists** — `∀u. set(u) → (u∈C ↔ P(u))`
2. **it respects `eq`** — `eq(a,b) → (P(a) ↔ P(b))`
3. **it is single-valued** — `Replace` only

**Item 2 is not obvious and it is load-bearing.** S1 renders `φ(f(x))` as either
`∃v.(F(x,v) ∧ φ(v))` or `∀v.(F(x,v) → φ(v))`; proofs need both. They are
interchangeable given EX + UNIQ **and congruence of φ** — and for uninterpreted φ
that third condition *is* the banned `eq_subst`, so it is not derivable. It
becomes a hypothesis. ✓ `probes: ex_all_bridge.{def,proof}`.

Two consequences:

- **Compiler B emits two things per call site**, not one: the class witness *and*
  the congruence proof. Both are the same structural induction over φ — atoms
  give congruence from tier 1 and S2's CONG, connectives and guarded quantifiers
  preserve it — so it is one pass with two outputs.
- **S2's CONG obligation *is* the replacement for `eq_subst`.** Not a separate
  spec item: the same content, discharged per-constant instead of assumed
  per-step. This is what makes the permanent ban survivable.

### The proof layer

`ZAppt(thm, t)` at a complex term has no counterpart — there is no term `t`. It
becomes, innermost-first:

```
use G_EX;  exists_elim → u        -- G(x,u)
use F_EX;  exists_elim → v        -- F(u,v)
forall_elim thm, v
implies_elim ...                  -- discharge the constraint with F(u,v)
```

`iota_elim` replaced by `exists_elim` scopes — precisely what S1 buys. It is
expressible because bare `exists_intro` in Mode 2 has an else-branch: when the
body does not contain the eigenvariable it simply closes the scope and re-derives
in the parent, i.e. ordinary ∃-elimination. So a **materialisation prelude** at
the outermost scope works, and every materialised witness dominates its uses.
That is also the real reason `emit.rs` requires `exists_elim` before `fix`.

The Isabelle proof skeleton therefore maps essentially 1:1. I expected the content
to be concentrated in the Pure equational rules. **That was wrong** — see §8's
tier 7, where they were rendered and checked.

### Where a transformation may run

Two workloads share this pipeline and they are not the same shape.

**Synthesis** — FOUNDATION's obligations (S2's EX/UNIQ/CONG per constant, §5's class
existence per φ) are *generated*. There is no input proof, so `proof_builder::Script`
constructs forward and checks each rule as it applies it.

**Translation** — an Isabelle proof term is *rewritten*. There is an input tree nobody
controls, and rewriting it is the natural shape. The IR it rewrites is **§14's
`meta::Proof`**. Its predecessor `ir::ir1` discarded the binder SORT, so it could not
tell `ALL x:i` from `ALL x:o`, and dispatch on that sort is the whole of the
translation. `ir::ir1` and `linearize::build_ir1` are **deleted** — recoverable from
git history, and there is no reason to want them back.

> **A pass may rewrite anything up to `Script`. Nothing may rewrite an `ir::Proof`.**

The asymmetry is N1 against N2, and it is not a matter of taste.

*Downstream of `Script` the risk is N1.* A rewritten `ir::Proof` carries no witness that
it is still a proof — the only thing that answers is the kernel, a subprocess fork. Such
a pipeline either runs unverified, so a pass bug reappears as a kernel error a long way
from its cause (the failure the typed IR exists to remove), or it needs a
`Proof::recheck` re-deriving every step from its rule and operands, which is a second
checker. Both are refused: FOUNDATION N1 names the kernel sole arbiter, and the places
our model of it is already subtle are exactly where a second checker diverges silently.
`exists_intro` is the standing example — at two arguments the kernel generalises *every*
occurrence of the witness, so a target the witness still occurs in needs the GENERAL rule,
∃I indexed by its conclusion. **⚠ THE THREE-ARGUMENT `let` FORM IS ONE SPELLING OF THAT
RULE, NOT THE RULE, AND THIS PROJECT NO LONGER EMITS IT** — `fol-zfc-comb` accepts only one
or two arguments, `Rule::ExistsIntro` carries no target, and `derivation::parse_rule`
refuses a third argument, so the form is unrepresentable. The rule is DERIVED: fix a fresh `z`, assume `eq(z,t)`,
transport the preserved occurrences, two-argument `exists_intro`, then discharge and
instantiate back at `t` against `eq_refl`. Nothing in FOUNDATION requires it primitively.

*Upstream the risk is N2.* An IR1 tree is not yet a claim about anything; it is input. A
mistranslation there yields a **green proof of a theorem that is not Isabelle's** —
faithfulness, not soundness, and FOUNDATION says nothing checks N2 but us. That risk is
created by translation existing at all, not by passes; its mitigations are R3's
relativization and the claim naming which theorem it asserts.

**What the previous framework got wrong was not its passes.** FOUNDATION §4's indictment
is entirely about the target they lowered *into*: ι-terms with S2 undischarged,
propositions reified, the meta-function graph reified and passed as an argument,
unrelativized throughout. The finding that forced the rewrite is itself a translation
finding — parametric schemas proved *by* the reification (`ZFC_Separation → CollectI`,
whose statement names the reified graph of an uninterpreted `P`). Rebuilt passes must
lower into the relational fragment, and each lowering step needs a justification here
rather than an encoding trick.

**One shape change to expect.** "Native ND lowering" should not return as a step-list
rewrite. Since the skeleton maps 1:1 above, the natural form is a **recursive descent
that calls `Script`** — a walk that constructs rather than a pass that rewrites, so
per-step checking comes free. That descent is §14's `LOWER`, and by the time it runs
every decision has been made upstream: it makes no provider calls at all. The genuine
passes stay upstream, and §14 names them — βη-normalisation, object elimination,
equational elimination.

**What would reopen the question.** Proof size, and nothing else. `class::compile_at` is
arity-free and size is *proved* linear in width × atom count, but context width grows
with quantifier depth, and `the_worst_body_costs_this_much` already guards a two-atom
body at the checker's practical size limit. Should a real body — `lfp`, `Sigma` — pass that, a dedup
pass over the emitted proof stops being speculative and has to be paid for with the
`recheck` above. It is **unmeasured**: measure one before building anything.

---

## 8. The chain

Not an operational rail with a hack counter. A dependency DAG whose leaves are the
19, ordered by what the mathematics forces, with one mechanical invariant:

> every node is a `.fol.def`/`.fol.proof` pair the checker accepts with **empty
> stderr**, whose def contains only the 19, earlier nodes, and admissible
> introductions (§10's G1 table).

| tier | content | status |
|---|---|---|
| 0 | the 19, axiom 3 as `↔` | — |
| 1 | `eq` refl/sym/trans, both substitution directions, `set`-congruence | ✓ complete |
| 2 | Kuratowski pairs; the `set(·)` discharge through nested `Pair` chains | ✓ complete — see below |
| 3 | Tuple Lemma T1–T4, Expansion | ✓ complete |
| 4 | Compiler B | ✓ mathematics; implementation open |
| 5 | kernel library | `collect_char` ✓ `replace_char` ✓ `ex_all_bridge` ✓ `eq_reflection_rel` ✓ `subst_rel` ✓ |
| 6 | constants in definitional order, each with EX/UNIQ/CONG | ✓ propagation + base cases |
| 7 | the proof layer | ✓ rules + two real proofs end-to-end, incl. complex-term materialisation |

**Tier 1 is the `eq_subst` replacement** — every congruence step downstream routes
through it. **Tier 2 is a prerequisite of tier 3**, not a side issue: every one of
B1–B7 is stated over pairs and triples.

### Tier 2 result ✓ `probes: pair_flattening.{def,proof}`

FOUNDATION §3 names this as "where a silent error can hide." It was checked,
and the risk assessment is right but **narrower than the phrasing suggests**:

- **The flattening identity itself is free.** Tuples are left-nested, so
  `((z₁…z_k),x,y)` and `(z₁…z_k,x,y)` expand to formulas differing only in the
  name of the intermediate existential variable — alpha-equivalent, hence
  *identical* in the checker's de Bruijn representation. There is nothing to
  prove.
- **The content is `pair_ex`, not the identity.** The lemma that matters,
  `flatten_slot1 [Phi(0)]`, says: given T1 holds at every `z` that *is* the pair
  `⟨z₁,z₂⟩`, the flattened 4-tuple form is equivalent. Forward is free
  (destructure the existential); **backward needs a pair to exist**. So each
  flattening step consumes `set(z₁) → set(z₂) → ∃p. kpair(z₁,z₂,p)`.
- **The `set(·)` discharge closes uniformly and does not compound with depth.**
  `pair_set` is exactly three `upair_set` applications (`{x}`, `{x,y}`,
  `{{x},{x,y}}`), and `tuple_chain` shows an n-tuple is n−1 iterations of
  `pair_set` with no new device.
- **`upair_set` needs `set_cong`, which needs Pairing** — confirming tier 1
  precedes tier 2. The dependency graph is acyclic:
  `pairing → set_cong → upair_set → pair_set`.

Proved: `eq_refl`, `set_cong`, `upair_ex`, `upair_uniq`, `upair_set`, `pair_ex`,
`pair_set`, `tuple_chain`, and the `flatten_slot1` schema. All first-attempt, no
iteration. `@def(upair)` / `@def(kpair)` are the first exercise of §10's
definitional-introduction row, and it held.

### Tier 2 complete ✓ `probes: pair_injective.{def,proof}`

17 further claims, closing the tier: the tier-1 equality core (`eq_symm`,
`eq_trans`, `eq_join`, `elem_second`), the `upair` layer (`upair_mem1/2`,
`upair_elem`, `sing_elem`, `sing_eq_sing`, `pair_eq_sing`, `upair_uniq`,
`upair_cong`), and the theorems:

| | |
|---|---|
| `pair_fst` | `kpair(x,y,p) → kpair(u,v,p) → eq(x,u)` |
| `pair_snd` | `kpair(x,y,p) → kpair(u,v,p) → eq(y,v)` |
| `pair_inj` | both — the Kuratowski injectivity theorem |
| `pair_uniq` | `kpair(x,y,p) → kpair(x,y,q) → eq(p,q)` — **UNIQ for the Pair constant** (S2) |

**Injectivity needs no classical reasoning.** The textbook proof cases on
`x = y` and so wants excluded middle. Routed through `upair_elem` instead, every
case split comes from a *membership* disjunction — `z∈{a,b}` gives
`eq(z,a) ∨ eq(z,b)` directly — so the proof is intuitionistic. `double_neg_elim`
is never used. That matters beyond elegance: it means tier 2 imposes no classical
dependency on tiers 3–4.

**Naming hazard.** `eq_sym` is a **reserved token** in the checker's grammar — it
is the banned kernel op — so a claim cannot be named that. The derived symmetry
lemma is `eq_symm`. Any emitted name must avoid the op keywords, `eq_subst` and
`iota_elim` included.

### Tier 3 — Tuple Lemma T1–T4 ✓ `probes: tuple_lemma.{def,proof}`

B4–B7 stated over the guarded membership abbreviations, then:

| | | route |
|---|---|---|
| T3 | `(x,y,z)∈C ↔ ⟨x,y⟩∈A` | `B5` |
| T2 | `(x,z,y)∈C ↔ ⟨x,y⟩∈A` | `B7 ∘ B5` |
| T1 | `(z,x,y)∈C ↔ ⟨x,y⟩∈A` | `B6 ∘ B5` |
| T4 | `⟨y,x⟩∈C ↔ ⟨x,y⟩∈A` | `B4 ∘ swap_triple` |

The T4-route discrepancy is settled in §5 — both routes verify; FOUNDATION §3's
is one closer longer. `Empty` is used exactly once, where FOUNDATION §3 says.

**Two technique notes for Compiler B.** T2 and T1 need *no pair reasoning at all*
— they are pure biconditional chaining over T3, so the guard-threading cost is
confined to T3 and T4. And the pair-witness in T3/T4 is always *obtained from an
existential* rather than constructed by `pair_ex` and then matched: that avoids
needing congruence of `kpair`/`pmem` in their arguments entirely. Constructing the
witness independently would have forced a `kpair_cong` chain — i.e. exactly the
`eq_subst` work the ban makes expensive. Prefer destructuring over constructing.

### Tier 3 complete — Expansion ✓ `probes: expansion.{def,proof}`

**Expansion is a metalevel schema, one instance per `(n,i,j)`** — `n` is not
first-order-indexable, so it is a *compiler procedure*, and what can be verified
is the recipe on concrete instances. Four at `n=4`, covering every step type:

| instance | `⟨xᵢ,xⱼ⟩` | composition | exercises |
|---|---|---|---|
| `exp_12` | `⟨x₁,x₂⟩` | T3 + append | append iteration |
| `exp_23` | `⟨x₂,x₃⟩` | T1 + append | T1 at a **simple** prefix |
| `exp_13` | `⟨x₁,x₃⟩` | T2 + append | T2 insertion |
| `exp_34` | `⟨x₃,x₄⟩` | T1 at a **compound** block | slot-1 flattening |

**Three findings.**

- **Append is arity-independent.** `exp_append3` (triple → 4-tuple) is B5 again,
  with the whole triple in slot `u`. B5 does not care how deep `u` is, so
  appending never needs a new device — only the `set(·)` chain grows, linearly,
  through `pair_set`. The `(n−j)×T3` tail is therefore free.
- **Flattening fires only when `i ≥ 3`.** `exp_23`'s prefix is the single variable
  `x₁`, so T1 applies directly with `z := x₁`. Only `exp_34`, whose prefix
  `(x₁,x₂)` is compound, needs `flatten_slot1`. Exactly one `schema_inst` in the
  whole probe. This is FOUNDATION §3's "T1 fires exactly once, while `A` is still
  a class of pairs, prepending the whole prefix as one block" — confirmed, and
  sharpened: the *flattening* is needed only when that block has ≥2 components.
- **`schema_inst` accepts bindings over enclosing fixed variables.**
  `Phi: pmem(x3,x4,A)` with `x3`, `x4`, `A` under `fix`. That is what makes a
  kernel usable mid-proof rather than only at closed formulas — load-bearing for
  the whole kernel-library architecture, and not something the schema resolver's
  docs promise (they describe the closed-binding case as typical).

**One imprecision in FOUNDATION §3's formula.** `1×T1 + (j−i−1)×T2 + (n−j)×T3`
should read `[i>1]×T1` — T1 fires *zero* times when `i=1`, since there is no
prefix to prepend. `exp_12` and `exp_13` both have `i=1` and use no T1.

### Tier 4 — Compiler B, mathematics ✓ `probes: compiler_b.{def,proof}`

The four induction steps, and an **end-to-end compile** of a concrete φ:

| case | step | source |
|---|---|---|
| atom | `pmem(u,v,E) ↔ u∈v`, then Expansion to position `(i,j)` | B1 + tier 3 |
| `∧` | `step_and` | B2 at the tuple level |
| `¬` | `step_not` | B3 (**guarded** — unguarded, the complement of `∅` collapses the base) |
| `∃` | B4 directly, dropping the last component | B4 |

`compile_psi` compiles `ψ(x) := ∃y. (y ∈ x ∧ ¬(x ∈ y))` along
`B1 → T4 → B3 → B2 → B4` and derives
`∃C. ∀x. set(x) → (x∈C ↔ ψ(x))`. The `T4` step is there because the first atom is
`y∈x` — index `i>j`, so the swap fires exactly as FOUNDATION §3 prescribes. Every
induction case is exercised.

**The systematic cost is witness reconciliation, and it is avoidable.**
`pmem(x,y,·)` unfolds to `∃p.(kpair(x,y,p) ∧ p∈·)`, so a step that *combines* two
`pmem` facts receives two different pair witnesses and must identify them —
`pair_uniq` then `elem_first_subst`. This is the CONG-replaces-`eq_subst` pattern
again, and it recurs in every combining step.

> **Design note for the implementation.** Tier 3's lesson was *destructure, don't
> construct*. Here it inverts: a compiler that materialises **one** canonical pair
> witness per tuple via `pair_ex` at the top of the chain, and threads it through
> every step, never reconciles at all. The reconciliation in these probes is an
> artifact of proving each step standalone. Thread the witness.

**What is not verified here.** Compiler B's *refusal* obligation — a φ containing a
bound class variable must be rejected, not compiled. That is an input gate, not a
derivation, so it cannot be a probe; it belongs to the implementation and to G4.
And the compile is verified on one φ: the general procedure is the induction, and
each concrete φ yields a straight-line chain of exactly these steps.

### Tier 6 — S2/S3 ✓ `probes: constants_s2s3.{def,proof}`

**The propagation lemma is a kernel, parametric in the constants.** For a composite
`G(x,r) := ∃t.(set(t) ∧ F(x,t) ∧ H(t,r))`, three schemas over `[F(2), H(2)]`:

| | needs | why |
|---|---|---|
| `compose_ex` | EX(F), EX(H) | chain the witnesses |
| `compose_uniq` | UNIQ(F), UNIQ(H), **CONG(H)** | ← see below |
| `compose_cong` | CONG(F) | rebuild the witness |

**UNIQ does not compose without CONG, and that is why S2 lists three obligations
rather than two.** Given `G(x,r)` and `G(x,r')` you get *different* intermediates
`t`, `t'`. UNIQ(F) gives `eq(t,t')` — but UNIQ(H) is stated at a *single* `t`, so
you cannot apply it until CONG(H) transports `H(t',r')` to `H(t,r')`. Drop CONG and
the induction of S3 breaks at the first composite. A negative control confirms it:
supplying `eq(t,t')` where `eq(t',t)` is needed fails at `implies_elim`.

**`[F(2), H(2)]` IS THE ONLY SHAPE, AND MULTI-ARGUMENT APPLICATION DOES NOT NEED
A WIDER ONE.** A function is unary, so `h(a,b)` is `h(⟨a,b⟩)` and the emitted
`H(a,b,r)` is an uncurried presentation rather than a ternary primitive. A body
`h(g₁(x), g₂(x))` therefore factors into two DEFINITIONAL introductions —
`P(x,p) ↔ ∃t₁t₂.(G₁(x,t₁) ∧ G₂(x,t₂) ∧ kpair(t₁,t₂,p))` and
`H_t(p,r) ↔ ∃t₁t₂.(kpair(t₁,t₂,p) ∧ H(t₁,t₂,r))` — after which the body is
`∃p.(P(x,p) ∧ H_t(p,r))`, which is the shape above. Obligations discharge from
`pair_ex`/`pair_uniq`/`pair_inj`/`upair_cong`, width iterates by `tuple_chain`,
and **no composition schema indexed by arity exists or is wanted**. FOUNDATION §2
carries the derivation and the ⚠ against the reading that asked for one.

**A class argument does not block this when the function is CONSTANT.** S5 emits
a class for `λx. b` even where `b` ignores `x`; that class is
`{⟨x,y⟩ : y = b}`, determined by `b` alone, so the step is a function of two
SETS and pairing applies unchanged. The test is that the tuple's domain slot does
not occur free in φ — an occurrence check, never the binder's name. Measured over
the eight constants blocked as "not a two-step chain": **all eight carry such a
class, fourteen between them, and `Sum.sum`/`QPair.qsum` carry no other kind.**

**The base cases.** `Pow` carries all three: EX from the Power axiom, UNIQ from
Extensionality, CONG by transporting `v∈A ↔ v∈B` through the characterisation.
Notably UNIQ needs *no* `set(u)` guard on the Extensionality step — `u∈r` gives
`set(u)` via `members_are_sets`, so the guarded characterisation applies without a
case split.

**`The` with the `∅`-default ✓.** `the_EX` and `the_UNIQ` over `[P(1)]`, with

```
The(r) := (U ∧ P(r)) ∨ (¬U ∧ r is empty)      U := "exactly one set satisfies P"
```

FOUNDATION §2 S3 says descriptions are total and single-valued *provided the
`∅`-default is emitted*, and the proof shows exactly why: **`use empty` appears
once in the entire probe**, in the `¬U` branch of `the_EX`. Without the default
branch there is nothing to return when `U` fails, so EX would need `U` as a
hypothesis — precisely "a bare Hilbert `ι` loses totality". `the_UNIQ` needs no
Empty and no classical reasoning; only EX does.

**These two are evidence about `D`, NOT about `ZF_Base_2eThe`, and they are
deleted from `base/tiers/s2s3`** — the probe keeps them, as tier-6 evidence that
the `∅`-default description is derivable from the spec. `The` is a *defined*
constant here (below), so its EX/UNIQ come from the induction step and `walk`
emits them; nothing ever cited these schemas. What made deleting them worth doing
rather than merely tidy: the one thing they were reachable for was rendering a
constant's `@def` **as `D`**, which needs no class and no `Pair` graph, checks
green, and is an N2 violation — the `@def` then no longer says what Isabelle
says. `constant::description_tests` now derives `The(C,r) ↔ D(r)` instead.

**`lem` is derivable, and needed once.** `Q ∨ ¬Q` from `double_neg_elim` as a
`[Q(0)]` kernel. Used solely to case-split on `U` in `the_EX` — the only classical
step anywhere in tiers 0–6.

**Two more mechanical facts.** `schema_inst lem { Q: … }` works *inside another
schema's proof*, with the binding mentioning the enclosing schema's variable `P`.
And `bottom_elim` needs its target named by a `let`, since it takes a handle, not a
formula.

### Tier 7 — the proof layer ✓ `probes: proof_layer.{def,proof}`

FOUNDATION §4's open question. Renderings, per S1:

```
term  a : i        ->  unary relation   A(r)
meta-fn f : i=>i   ->  binary relation  F(x,r)
a ≡ b              ->  ∀r. set(r) → (A(r) ↔ B(r))            relation extensionality
f ≡ g              ->  ∀x r. set → (F(x,r) ↔ G(x,r))
f a                ->  ∃t. (set(t) ∧ A(t) ∧ F(t,r))
```

All seven Pure rules re-render, plus the two term-instantiation patterns:

| Pure rule | relational counterpart | cost |
|---|---|---|
| `reflexive` / `symmetric` / `transitive` | refl/symm/trans of `↔` | trivial |
| `equal_intr` / `equal_elim` | `iff_intro` / `iff_elim_l` | trivial |
| `combination` | **pointwise rewriting under the `∃`** | no CONG |
| `abstract_rule` | **a quantifier reordering** | no extensionality |
| `ZAppt` at a complex term | `appt_complex` — EX supplies the witness | mechanical |
| nested, `f(g(x))` | `appt_nested` — innermost-first prelude | composes |

**Two claims in §7 above were wrong, and the correction is the finding.** I had
`combination → CONG` and `abstract_rule → Extensionality + UNIQ`. Neither holds,
because I had conflated two different equalities:

| | renders as | rewriting costs |
|---|---|---|
| **Pure `≡`** on `i`-terms | *relation* extensionality, `∀r. A(r) ↔ B(r)` | nothing — pointwise |
| **HOL `=`** on `i` | *object* equality, `eq(a,b)` | CONG, per constant |

`abstract_rule` needs function extensionality only if `f` is an *object*. Under S1
it never is — it is a relation — so the rule degenerates to swapping `∀x.∀r` for
`∀x r`. Likewise `combination`'s hypotheses are relation equalities, which rewrite
under the existential without touching object equality at all.

**So FOUNDATION §4's question resolves in the affirmative, at rule level.** There is
no rule-level obstruction: the skeleton maps 1:1, the equational layer is nearly
free, and materialisation composes. What cost remains sits in exactly two places,
both already discharged elsewhere — CONG per constant (tier 6) and the `set(·)`
chain through pairs (tier 2).

### End-to-end on a real Isabelle proof ✓ `probes: zf_pair_e2e.{def,proof}`

`ZF.pair` serial **3448**, decoded from the export with
`zf_pair_e2e_decode.py`. 3448 is the proof node of entity **3450 =
`pair.Pair_inject1`** — entities pair with the node two serials back, so 3446
(`Pair_inject`, the `[elim!]` rule concluding `a=c ∧ b=d`) is proved by 3444 and
is a *stronger* theorem than anything below:

```
Pair_inject1(a,b,c,d) :  ⟨a,b⟩=⟨c,d⟩ ⟹ a=c
  = λH. conjunct1[a=c, b=d] ( iffD1[⟨a,b⟩=⟨c,d⟩, a=c ∧ b=d] (Pair_iff a b c d) H )
        ZThm 246/IFOL           ZThm 426/IFOL             ZThm 3442/ZF.pair   ZAbsp
```

Every node maps, one for one:

| proof-term node | emitted |
|---|---|
| `ZAbsp H` | `assume eq(p,q)` … `implies_intro` |
| `ZAppt` at **terms** `a,b,c,d` | `forall_elim` ×4 |
| `ZAppt` at **propositions** (IFOL schematics) | `schema_inst iffD1 { P: …, Q: … }` |
| `ZAppp` ×3 | `implies_elim` ×3 |
| `ZThm 246`, `ZThm 426` | logic kernels `conjunct1`, `iffD1` |
| `ZThm 3442` (`Pair_iff`) | a claim, **proved here from tier 2** — not assumed |

`Pair_iff` needed four new congruence lemmas — `upair_res_cong`,
`upair_arg_cong`, `kpair_res_cong`, `kpair_arg_cong` — then falls out of tier 2's
`pair_inj` and `pair_uniq`. 23 claims, all rooted in the 19.

**Three findings about the export, all affecting the encoder.**

- **Named theorems are thin wrappers.** Every one of the 33 named theorems in
  `ZF.pair` is a single `ZThm` citation wrapped in `ZAppt`s — no `ZAppp` at all.
  The real proofs live in *anonymous* serials — most of the files. The encoder
  must follow the citation chain; translating only what `theory/thms` names would
  produce nothing but forwarding stubs.
- **The proof-term tag space overlaps the term tag space.** `5` is `App` in a term
  and `ZAppp` in a proof, `1` is `Free` vs `BoundP`. Any traversal must know which
  subtree it is in — the statement or the proof — or it miscounts. `yxml.rs`
  documents this; it is easy to lose when writing analysis tooling.
- **`ZAppt` is overloaded across S1 and S4.** The *same* node instantiates a term
  variable (→ `forall_elim`, materialising if the term is complex) and a
  proposition variable (→ `schema_inst`). Which one it is depends on the cited
  theorem's type, not on the node. This is the one place the encoder must consult
  the theorem database rather than the proof term.

**Scope, stated precisely.** One real proof, chosen because it exercises `ZAbsp`,
`ZAppp`, and both readings of `ZAppt`. It does **not** exercise complex-term
materialisation — `Pair_iff` is cited at plain variables, so the `appt_complex`
path above is still unexercised against real data. FOUNDATION §4 asks whether
proof terms re-render "or whether large classes of proofs must be regenerated
differently": on this evidence they re-render, node for node, with no
regeneration. One proof is not a large class.

### Recursion is not a third base case ✓ `probes: lfp_recursion.{def,proof}`

§9 called this the single load-bearing unknown — 39 package axioms, 77 entry
sites, **about a third of the corpus downstream**, and no probe. It was probed before
P0, on the argument that no other premise of §10 fails first.

**Read the defining equations off the export and the risk dissolves into two
routes, both definitional.** FOUNDATION §2 S3 lists recursion as a base case
beside primitives and `The`; it is not one.

```
lfp(D,h)          == Inter(Collect(Pow(D), λX. Subset(h(X), X)))
Inter(A)          == Collect(Union(A), λx. Ball(A, λy. mem(x,y)))
   ⇒ lfp bottoms out in Power + Separation + Union

Vrecursor(H,a)    == apply(transrec(rank(a), …), a)
transrec(a,H)     == wfrec(Memrel(eclose({a})), a, H)
wfrec(r,a,H)      == wftrec(trancl(r), a, λx f. H(x, restrict(f, r-``{x})))
wftrec(r,a,H)     == H(a, the_recfun(r,a,H))
the_recfun(r,a,H) == The(λf. is_recfun(r,a,H,f))
   ⇒ every recursion route bottoms out in `The`
The(P)            == Union(Replace(cons(0,0), λ_ y. P(y)))
```

`list(A)` and `Fin(A)` take the first route; `list_rec`, `nat_rec`, `rank`,
`wfrank` and the `*_list_def` / `*_nat_def` family take the second.

**The lfp route is derived here.** `pow_sep_ex`, `inter_ex`, `lfp_ex`,
`inter_uniq` — EX and UNIQ for `lfp` from **Power + Separation + Union alone**.
Nothing new is admitted. Note the shape: the class arrives as a **first-order
parameter, not a schema variable**, which is §6's interface contract taken
literally — Compiler B emits a class, the kernel takes one — so R2 has nothing to
discharge and no schema is declared.

**The `The` route is closed by Isabelle's own definition, not by tier 6** — an
earlier version of this paragraph had it the other way round. `Replace` filters to
the single-valued case, so `Replace({0}, λ_ y. P(y))` is `{the y}` when `∃!y. P(y)`
and `∅` otherwise, and `⋃` then strips the braces: `The` reduces through
`zero`/`cons`/`Replace`/`Union` and `walk` emits its four claims. Tier 6's
`the_EX`/`the_UNIQ` derived the same *shape* `(U ∧ P(r)) ∨ (¬U ∧ empty(r))` from
S3, at a different relation, and nothing connected the two.

**That agreement is now checked rather than asserted** ✓
`constant::description_tests::the_description_bridge_checks`: over a class `C`
with `pmem(x,y,C) ↔ P(y)`, `The(C,r) ↔ D(r)`. The chain it rests on is four
kernel-checked lemmas — `∅ ∈ Pow(A)`, `0 ≠ Pow(0)`, `a ∈ Upair(a,b)`,
`a ∈ cons(a,A)` — because `Upair`'s `@def` is the `Pow`/`Pow`/`Replace` chain and
`0 ∈ {0}` therefore is not free. **`{0}` contributes nothing but INHABITEDNESS**:
`replace_is_description` takes `∃u. u ∈ v2` as its hypothesis and never looks at
which set `v2` is.

**Congruence for `P` is load-bearing, one-directional, and was not in the
prose.** `The`'s value is only *extensionally* equal to the witness, so
`The(C,r) → D(r)` must move `P` along `eq(a,r)`; `eq` is a defined predicate, so
that transport is not free for an uninterpreted `P`. The converse never needs it,
and neither do `the_EX`/`the_UNIQ` themselves. Required-to-reject ✓: with the
hypothesis inert the forward direction lands on `P(a₀)` and never reaches `P(r)`
(`the_bridge_cannot_move_p_without_congruence`). Isabelle's `the_equality` and
`the_0` are the CONG-free halves and go straight from the `@def`; `theI` is the
member of that family that needs it.

**Required-to-reject ✓.** Weakening the class hypothesis to a triviality
(`u∈K ↔ u∈K`) makes `lfp_ex` fail. The Compiler-B class is load-bearing, not
decoration.

**What is *not* shown here.** CONG for `lfp` (it propagates by `compose_cong` ✓,
but is not derived in this probe); the `wfrec` composition itself, which rests on
the definitional chase above plus tier 6 rather than on a derivation; and the
per-datatype `bnd_mono` obligations, which are ordinary theorems for the proof
layer, not constant obligations. So: **the base cases are closed, and what remains
is S3's mechanical propagation.**

### The equality-rewriting family survives the ban ✓ `probes: eq_reflection_kernel.{def,proof}`

§3 bans `eq_subst` permanently. The obvious objection is that a large family of
*cited IFOL theorems* is `eq_subst` — and none of them can be a kernel over
uninterpreted parameters, because deriving `P(b)` from `P(a)` is precisely the
banned move. This was the likeliest single thing to force a redesign, so it was
measured and then probed.

**The load.** Corpus-wide the family is a large minority of all IFOL citations,
overwhelmingly `eq_reflection`, then `subst`, `ssubst`, `subst_context`
29, `forw_subst`/`back_subst` 6 each, `pred{1,2,3}_cong` / `eq_cong` /
`subst_context{2,3}` one each.

**The resolution is §7's parameter-or-hypothesis rule, and it holds.** Under S1 a
term of type `i` is a unary relation, so the two equalities separate (§8 tier 7):
object `a = b` is `∀x y. A(x) → B(y) → eq(x,y)`, meta `a ≡ b` is relation
extensionality. `eq_reflection` is then exactly *object equality ⇒ relation
extensionality*, and both it and `subst` are parametric once congruence is a
hypothesis:

```
eq_reflection_rel [A(1),B(1)]:  EX(A) → EX(B) → CONG(A) → CONG(B)
                                → (object equation) → (relation extensionality)
subst_rel [P(1)]:               CONG(P) → eq(a,b) → P(a) → P(b)
```

**UNIQ is not needed** — only existence and result-congruence. That was not the
expectation going in; the probe corrected it.

**What discharges the hypothesis is what makes this factor**, and it needs no new
machinery:

| family | sites | discharged by |
|---|---|---|
| `eq_reflection` | the bulk | the **constant table** — EX/CONG are per-constant facts (S2) |
| `subst` and kin | the remainder | **Compiler B's congruence output** — per concrete φ |

So §7's "S2's CONG obligation *is* the replacement for `eq_subst`" is now
measured rather than asserted, and equality needs no fourth generator (§12): it is
the principal *consumer* of the two that exist.

**⚠ THE SITE COUNT IS NOT A DERIVATION COUNT — it is one per constant.** CONG propagates by
definitional order, and `compose_cong` ✓ (tier 6) needs only `CONG(F)` to give
congruence of a composite. So a compound rendering's congruence composes from the
per-constant ones, and the work is one CONG derivation per constant, not one per
citation. The site count measures *load on* the constant table, not its size.

**Where the extra equality axioms are actually spent.** The signature has three
predicates, and §3's table gives substitution in every atom of each: `elem` left
by axiom 2 (`elem_first_subst`), `elem` right by axiom 3's `←` (what §0 bought),
`eq` by refl/sym/trans, `set` by `set_cong` via Pairing. That is the complete base
case, and it is why §8 calls tier 1 the `eq_subst` replacement. Note what the probe
shows about *where* it is spent: `eq_reflection_kernel` needs **Extensionality
alone** — dropping `members_are_sets` or `elem_first_subst` leaves it green. A
parametric kernel's congruence is hypothetical, so the atom-level substitution
axioms are consumed by whatever *discharges* the hypothesis, never by the kernel.

**Why more axioms would not help.** The one thing unavailable is a *parametric*
schema `eq(a,b) → P(a) → P(b)` over uninterpreted `P`. That is not a shortage of
equality principles — it is that the structural induction cannot run on an opaque
predicate, so no additional axiom reaches it. The schema's *content* is perfectly
legitimate (in FOL-with-equality it is the substitution schema, instance by
instance); R2's rule is only that each instance must be **derived** rather than
the schema **assumed**. Deriving them per concrete φ is exactly Compiler B's
second output.

**Required-to-reject ✓, and it reproduces §1's failure mode live.** Dropping the
`CONG(B)` hypothesis makes the kernel underivable. The checker then prints
`Proved (2)`, `OK: 2 claim(s) checked`, **exit 0** — and a non-empty stderr. The
buckets are clean; only stderr carries the failure. This is the exact reason §2's
gate is *exit 0 **and** empty stderr*, demonstrated on a real kernel rather than
on the synthetic `schema_link_gate`.

### Compound-term materialisation, on real data `probes: zf_fst_conv_e2e — DELETED`

> **⚠ `zf_fst_conv_e2e` IS GONE, AND EVERY REFERENCE TO IT BELOW IS HISTORICAL.**
> It rendered `fst` through a hand-built `qfst`/`ufst`/`fstrel` chain with an
> ASSUMED empty-set default. FOUNDATION §2 S3 records that reading as superseded:
> `The` is defined (`ZF_Base.the_def`, serial 1928) and reduces through
> `zero`/`cons`/`Replace`/`Union`, so the default is DELIVERED. The probe could
> never check — its `qfst_char` used a three-argument `exists_intro` the kernel
> does not implement — and it was a relic of the wrong route, so it is deleted
> rather than repaired. Where the text below names it as a target the generator
> must reproduce, read that as `zf_pair_e2e` alone.

The scope note above named the gap: `Pair_iff` is cited at plain variables, so
`appt_complex` was still untested. `ZF.pair.fst_conv` closes it —

```
fst_conv :  fst(⟨a,b⟩) = a          serial 3556; the real proof is anonymous 3552
fst(p)   ≡  The(λx. ∃y. p = ⟨x,y⟩)   ZThm 1952/ZF_Base, cited AT THE COMPOUND TERM ⟨a,b⟩
```

33 claims, empty stderr, first attempt. Four axioms of the 19 (`members_are_sets`,
`elem_first_subst`, Extensionality, Pairing) and five definitional introductions
(`upair`, `kpair`, `qfst`, `ufst`, `fstrel`); the `The` shape is tier 6's verbatim.

**The compound-term path costs nothing new — it is `exists_elim`, innermost-first.**
`fst_conv_prelude` materialises *both* levels with **neither witness a term**:

```
use pair_ex;      exists_elim → p     -- the inner term ⟨a,b⟩
use fst_EX_pair;  exists_elim → r     -- the outer term fst(p)
use fst_conv_all  -- ... then identify: eq(r,a)
exists_intro ×2                       -- close r, then p (LIFO)
```

This is §7's recipe run against a real citation, and it is the whole of the
`iota_elim` replacement. The theorem is stated both ways per `ex_all_bridge`:
`fst_conv_all` (∀-form) and `fst_conv_ex` / `fst_conv_prelude` (∃-form). Only the
∃-form materialises; the ∀-form is what the ∃-form's body is discharged with.

**Three findings.**

- **The `∅`-default is dead wherever uniqueness is provable, and that is every
  site the corpus cites.** Tier 6's `the_EX` needed `use empty` and `lem` — the
  only classical step in tiers 0–6. Here **neither appears, and `empty` is not in
  the def file at all**: on a pair `U` holds, so the left disjunct is taken
  directly. So the default branch is what makes the *constant* total, not what
  makes any *call site* work. `The`-derived constants are even cheaper than §4
  suggested — their classical cost sits entirely in the unrestricted EX.
- **The content is `Pair_iff`; the description machinery is bookkeeping.** All of
  it lives in `qfst_char`: `(∃y. ⟨a,b⟩=⟨x,y⟩) ↔ a=x`, forward by `pair_fst` after
  transporting along `eq(p,q)`, backward by `kpair_arg_cong` at `y:=b`. `ufst_pair`
  and the two `fst_conv` forms are then mechanical.
- **The Pure-equational tower collapses, confirming tier 7 on real data.** Serial
  3552 is simp-generated and is overwhelmingly `Pure.combination` / `transitive` /
  `reflexive` / `abstract_rule`, nested ~20 deep. Under S1 all of it is *rewriting
  the description's body pointwise under its binder* — free, per tier 7 — and it
  reduces to `qfst_char` being stated `∀x`. The three Pure-equational steps still
  map one for one (`fst_def` at ⟨a,b⟩ → the materialised `fstrel`/`qfst`;
  `abstract_rule`+`combination` over `Pair_iff` → `qfst_char`; ZThm 2740 → the
  left-disjunct step of `ufst_pair`), but node-for-node is an **upper bound on the
  emitted proof, not its shape**.

**Required-to-reject ✓.** Dropping the `set(b)` guard from `qfst_char` is
rejected (`qed: derived formula doesn't match goal`). The backward direction
consumes `set(b)` as the witness's `set(y)` conjunct, so the guard is load-bearing
for the derivation — §6's discipline, made mechanical here. *(This shows the guard
is consumed, not that the unguarded statement is unprovable; that would need a
model argument, and is not claimed.)*

**Scope, stated precisely.** One theorem, chosen because it is the smallest real
citation at a compound term. The probe proves `fst_conv` from tier 2; it does not
re-render every node of 3552's equational tower, and the third finding is
exactly the claim that it should not have to.

---

## 9. The components

§7 names three components; this is the full inventory, and the organising fact is
that **every entry eliminates one of §7's four constructs**. Constructs 1 and 2
are free — a mechanical rewrite and β-substitution. Constructs 3 and 4 are the
project, and they are why there are *two* compilers rather than one: a term of
type `i` needs a **translator**, a schematic `?P` needs a **prover** that
manufactures a class per concrete φ.

Status is one of **exists** (in the tree), **✓ math** (probe-verified, code open),
or **open**.

### The census — §7's premise, tested corpus-wide

§7's "exactly four constructs" was derived before any theory but `ZF.pair` had
been read. Measured over every proof file (sizing, not a premise):

- **Proof-space tags are exactly the seven** — `BoundP`, `ZAbst`, `ZAbsp`,
  `ZAppt`, `ZAppp`, `ZAxiom`, `ZThm`. No `Hyp`, no `OfClass`, no `MinProof`.
- **No `Oracle`, no `sorry`, no `skip_proof`.** Nothing unsound is imported.
- **Tier 7's seven Pure rules are confirmed** — in descending traffic
  `reflexive`, `combination`, `equal_elim`, `transitive`, `symmetric`,
  `abstract_rule`, `equal_intr`. **Correction:** there are also
  four Pure axioms tier 7 does not mention — `conjunction_def` (4), `prop_def`
  (3), `sort_constraint_def` (2), `term_def` (2). Eleven occurrences, presumably
  trivial definitional unfolds, but eleven sites is not "no plan".
- **Sizes.** The kernel library K1 is a fixed set of IFOL+FOL+Pure theorems called
  very many times; the constant table is the `*_def_raw` definitions; the package
  axioms are a small set (see the risks below). **The magnitudes are in
  `export/tests.rs`; what matters here is that all four sets are FINITE and
  ENUMERATED.**

*Method note, because it nearly produced a false finding.* The first pass of this
census descended blindly and counted term-space `Const`/`App`/`Free` as proof
nodes, inventing occurrences of an "unknown tag 6". The proof and term tag
spaces overlap (§8), so a traversal must select children **per node kind**:
`ZAbsp = [prop, proof]`, `ZAbst = [type, proof]`, `ZAppt = [proof, term]`,
`ZAppp = [proof, proof]`. §12 makes this a type, not a convention.

### Already in the tree — encoding-agnostic

| component | note |
|---|---|
| YXML parser | knows the proof/term tag-space overlap (§8) |
| Isabelle AST | |
| `linearize` → IR1 | as far as the tree currently goes |
| FOL AST | **S1 enforced by types**: `FolTerm = Var \| HandleRef`, no description former |
| `ir::Step` | `EqSubst` / `IotaElim` unrepresentable |
| emitter | skeleton |

One live delta: **`Step::EqSym` is still representable**, and §3 bans it. It is
§10 P1's small change.

### The eight to build

**1. The theorem database — open.** Indexes `theory/thms` and `theory/consts`
across all theories: serial → statement, type signature, citation graph. §7 does
not list it; two of §8's findings force it. Named theorems are thin wrappers, so
the citation chain must be followed to reach the anonymous serial that holds the
real proof; and `ZAppt` is overloaded across S1 and S4, where **which reading
applies depends on the cited theorem's type, not on the node**. This is the one
place the encoder cannot work from the proof term alone.

**2. Compiler A — terms and formulas — open.** Isabelle term → guarded FOL
formula plus obligations; emits no proofs.

| | |
|---|---|
| A1 | meta-connective elimination (construct 1) |
| A2 | β-reduction of concrete λs (construct 2) |
| A3 | S1 rendering, **both** readings — `∃v.(F(x,v) ∧ φ(v))` and `∀v.(F(x,v) → φ(v))`; interchangeable only given CONG (§7, `ex_all_bridge` ✓) |
| A4 | S6 guard insertion — **always emit**; per-occurrence redundancy judgment is what produced §6's bug |
| A5 | obligation collection, per constant |
| A6 | the `ZAppt` dispatcher — term → materialisation prelude, proposition → `schema_inst` (needs component 1) |

**3. The constant table (S2/S3)** — ✓ math for propagation, open for the list.
The ZF constants in definitional order, each with a `@def` introduction plus
EX/UNIQ/CONG. `compose_ex` / `compose_uniq` / `compose_cong` ✓. Three base-case
generators: primitive/Skolem (`∃!r`), `The` with the `∅`-default ✓, and
**recursion** — see the risks below.

**4. The kernel library.** K1 the IFOL/FOL logic layer — a fixed schema set,
mechanical but not small; shape ✓ (`logic_kernels`). K2 the ZF operation characterisations, each conditional
on its class hypothesis — `collect_char` ✓ `replace_char` ✓ `the_EX`/`the_UNIQ` ✓
`ex_all_bridge` ✓. K3 tiers 1–3 ✓.

**5. Compiler B — classes — ✓ math, code open.** B1 the induction driver
(atom→B1+Expansion, ∧→B2, ¬→B3 guarded, ∃→B4). B2 the Expansion/Tuple-Lemma
instance generator per `(n,i,j)`. B3 the **congruence emitter** — two outputs per
call site, not one. B4 canonical pair-witness threading. B5 the **predicativity
refusal gate**: reject any φ with a bound class variable. B5 is what buys
conservativity over ZFC, and being an input gate it is the one part no probe can
cover.

**6. The proof-layer renderer — ✓ rules, open.** Proof term → ND skeleton
(`ZAbsp`→assume/`implies_intro`, `ZAppp`→`implies_elim`, `ZAbst`→`forall_intro`,
`ZAppt`→dispatch), the materialisation prelude ✓, the seven Pure equational rules
✓, and citation-chain following.

**7. The gates** — §10's table. Each needs a case it is *required to reject*.

**8. The driver — open.** Topological emission over definitional and citation
order; per-theory orchestration; and a metric in which "Proved" means the
transitive dependency closure bottoms out in the 19.

### Two risks the tier table understates

**G0 — the N2 back-renderer is the largest unbuilt component, and the only guard
on faithfulness.** `FOUNDATION.md` is blunt: *nothing checks N2 but us*. The
checker certifies a **weaker** statement than the Isabelle theorem just as
happily as the right one — that is exactly §6's dropped-guard failure, and it
reports green. Checking it means back-rendering `σ*` and diffing against the
export's `prop` node, i.e. a second translator running backwards. Every other
component has a probe; this one has none, and it *cannot* be probed the same way,
because it is a claim about a **pair** of artifacts rather than about a
derivation.

**Recursion — the thinnest part of the spec, now the best-understood part of it.**
FOUNDATION §2 S3 disposes of it in one sentence — "needs the recursion theorem,
which routes back to `The`". That sentence turns out to be *right and complete*
for the WF half, and the `lfp` half does not need `The` at all.

**A narrow gate with a wide blast radius.** Two numbers, and they measure
different things — conflating them produced two successive wrong framings of this
risk, recorded here so the third is not attempted.

| | measured |
|---|---|
| **the work** — package axioms to introduce, each needing EX/UNIQ/CONG | **39 distinct, 77 citation sites** |
| **the exposure** — proofs transitively depending on one | **about a third of the corpus** |

The 39: `List.list_def` / `list_rec_def` / `Cons_def` / `Nil_def`, `Bin.bin_def` /
`bin_rec_def` / `Bit_def` / `Pls_def` / `Min_def`, `Finite.Fin_def` /
`FiniteFun_def`, `Zorn.TFin_def`, `Arith.raw_add` / `raw_diff` / `raw_mult`,
`ZF.iterates`, and the per-function `*_list_def` / `*_nat_def` family. Downstream
by theory, heaviest first: `List`, `Int`, `Bin`, `IntDiv`, `ArithSimp`, `Arith`,
`Finite`, `CardinalArith`, `Zorn`, `Cardinal_AC`.

*Two corrections, both mine.* The first version sized this by summing the proof
counts of theories whose **names** suggest `Fixedpt` ("the top risk").
The second called that "wrong" and replaced it with the 39 axioms. **Both were
half-right and the second over-corrected**: the work really is 39 constants, and
the exposure really is about a third of the corpus. The name-based estimate was in
fact close to the measured dependency figure — what was wrong
about it was not the number but calling the *work* unbounded.

**RESOLVED — probed before P0** (§8, `lfp_recursion`). Reading the defining
equations off the export dissolves this into two routes, both *definitional*:
`lfp` bottoms out in **Power + Separation + Union** (derived: `lfp_ex` ✓), and
every WF/transfinite route — `wfrec`, `wftrec`, `transrec`, `Vrecursor`,
`nat_rec`, `rank` — bottoms out in **`The`**, closed by tier 6 ✓. So recursion is
**not a third base case** despite FOUNDATION §2 S3 listing it as one, nothing new
is admitted, and that exposure is no longer gated on an unknown. What is
left is S3's mechanical propagation over the 39 constants.

*How these components are arranged — and why the arrangement, not the list, is
what keeps hacks from leaking — is §12.*

### One constraint, not a component

**The checker is a dependency we must not modify.** It is the sole independent
arbiter (§1); making our output pass by changing it is self-certification, and it
retires the only thing standing behind N1.

---

## 10. The plan

The plan is the dependency DAG of §12's Units, walked in order. Every phase has
**one falsifiable criterion**, and the reason not to reorder is not taste: each
phase's criterion is *built out of the previous phase's artifacts*. P6 cannot be
checked before P0 exists, because P6's criterion is "the checker accepts these
Units" and P0 is what makes a Unit checkable.

That cuts both ways, and once against this document. The order is a claim about
the DAG, so it is **falsifiable like any other claim here** — and the P4→P5 edge
was drawn backwards, found by measuring the constant table rather than by
argument (below). The discipline is not "the order is fixed"; it is that an
order may only be changed by showing the dependency runs the other way.

### The gates

The linker (§2), plus one gate per FOUNDATION §5 property, each with a case it
is *required to reject*:

| gate | checks | reject-case |
|---|---|---|
| L | no declaration without implementation | `schema_link_gate` |
| G1 | only the 19 admitted, plus admissible *introductions* (below); no `axiom` carrying a predicate outside `{elem,eq,set}` ∪ declared constants | a free-`P` axiom (the `separation_P` shape) |
| G2 | R2 — every schema implemented | = L's schema half |
| G3 | EX/UNIQ/CONG closed over definitional order | a constant whose EX cites a later constant |
| G4 | no term-former, no reified proposition, no reified graph | partly free from `FolTerm`; extend |
| G5 | every `i`-quantifier guarded | unguarded `collect_char` (§6) |
| G0 | **N2** — `σ* = ⟦σ_isa⟧`, the conformance check of §13 | a deliberately weakened rendering |

**G1 cannot be literal.** "Only the 19" would forbid every constant, since each
adds axioms to the def file. The checkable rule distinguishes *introduction* from
*admission*:

| form | admissible when | content |
|---|---|---|
| definitional — `C(x⃗,r) ↔ body` over earlier symbols | always; EX/UNIQ are then **derived** from `body` | zero |
| Skolem — `∃!r. C(r)` together with `C(r) → φ(r)` | `∃r. φ(r)` is **proved** from earlier material | zero, by model expansion |
| anything else | never | — |

Definitional covers nearly everything: `Pow(A)` is unique by Extensionality, and
S3 routes recursion through `The`. Skolem is needed only for genuinely non-unique
primitives — essentially just `Inf`. Note this makes G1 and G3 one gate. First
exercised by `@def(upair)` / `@def(kpair)` in §8, and it held.

> **⚠ THIS TABLE IS ONE ROW SHORT OF THE ROUTES ACTUALLY NEEDED, AND "G1 and G3
> are one gate" IS WHY.** A constant introduced by a fixpoint or a recursion is
> definitional in form, but its `_GRAPH` is not derivable from its body — it needs
> a *theorem about the constant*. §18 adds that third route (**characterised**),
> separates `GRAPH` from the definitional closure G3 governs, and states the gate
> (**G6**) that keeps it acyclic. Read §18 before concluding a constant is
> permanently refused because its body will not compile.

### The phases

**Read the left column as identity, not as sequence.** The rows below are in
**execution order**, and P5 precedes P4 — the one place where the numbering and
the dependency disagree. The numbers were assigned before the constant table was
measured and are kept because they name phases across the code and the history;
the order is what was wrong, and it is corrected here rather than by renaming.

**STATUS IS PART OF THE TABLE, and every cell carries a handle.** A status with no
way to check it is the thing this document keeps getting wrong. If a row
disagrees with the code, the code wins and the row is stale — fix it here.

| | build | criterion — the thing that can fail | status · handle |
|---|---|---|---|
| **P0** | `unit.rs`, the checker harness, gates L and G1 with their reject fixtures | all probes load as Units and check; `schema_link_gate` and `eq_reflection_kernel`'s control **reject** | ✅ **DONE** · `gate::shapes_tests` runs `CHAIN_PROBES` through `unit::check`; `LINKER_REJECT` |
| **P1** | `base/` — the 19, tiers 1–3, the two equality kernels. Retire `Step::EqSym` | base green; `EqSym` absent from `ir.rs`; only `base/` declares a bare `axiom` | ✅ **DONE** · `EqSym` has **zero** occurrences in `src/`; `gate::admission`; all but Regularity and Choice pinned |
| **P2** | `export/` — typed `ProofTerm`, the theorem database, the citation graph | **the §9 census becomes a test**: every proof parses, the tag set is exactly the seven, no oracles, every cited serial resolves | ✅ **DONE** · `export/tests.rs` pins each |
| **P3** | `statement/` (Compiler A) A1–A5 | one theory's statements render; G4/G5 green; the first G0 diff | ◐ **PARTIAL** · rendering + G5 reject cases in `gate::guards_tests`. **§11.2's `ZAppt` term-vs-proposition dispatch is UNBUILT** — `ZAppt` has no non-test occurrence in `src/` |
| **P5** | `class/` (Compiler B) B1–B5 — **runs here** | regenerate `compiler_b`'s ψ compile; the bound-class-variable fixture **refuses** | ✅ **DONE for P4** · `the_{diagonal,seed_tier}_is_what_compiler_b_regenerates`. One named refusal open: §5 rule 1, which is what `Diff` hits |
| **P4** | `constant/` — the 197 term constants and the package axioms, in definitional order. **Needs P5** | each constant's Unit checks; G3 closed | ◐ **ACTIVE — THIS IS WHERE THE WORK IS, AND IT NOW GATES P6 TOO** · what emits, and what is refused by R6 (ceiling **195**), omitted, or cascaded: `every_refusal_carries_a_verdict`, which asserts each. G3 closed by `gate::claims`. Family C — a constant `ConstEnv` lacks — is the largest share of the goals the theorem side cannot render (`the_lower_reach_census`) |
| **P6** | `theorem/` — skeleton, dispatch, materialize, pure_rules | **regenerate `zf_pair_e2e` and `zf_fst_conv_e2e` as Units, and check them** | ❌ **CRITERION NOT MET** · both are HAND-WRITTEN probes loaded from `docs/phase2_probes`; **nothing regenerates them**. All four §14 passes now EXIST and compose (`norm`=H, `elim`=S, `eq`=E, `lower`=LOWER) and the kernel accepts a generated `Pair_inject1` — but **no pass has a production caller**, `zf_fst_conv_e2e` is untouched, and only that ONE proof has ever been through the kernel. **Designed in §17** |
| **P7** | outward, theory by theory | gates green at every step | ❌ not started |

> **⚠ THE P4 → P6 ORDER IS NOT ONE-WAY, AND THIS TABLE STILL DRAWS IT THAT WAY.**
> A constant of the fixpoint family reaches its `_GRAPH` only through a theorem
> about itself, so P6 feeds P4 as well as consuming it. §18 replaces the single
> "emitted" flag with three levels and makes the two phases one fixpoint. The
> phase numbering stays; what changes is that the arrow between P4 and P6 runs
> both ways.

> **⚠ P6 IS THE END-TO-END CLAIM AND IT IS EVIDENCE, NOT A PIPELINE.** The two
> e2e artifacts prove the route is derivable — they are kernel-checked with empty
> stderr — but they were written by hand. Nothing in `src/` produces them. Do not
> read "`zf_fst_conv_e2e` is green" as "the pipeline reaches `fst_conv`".

**Where the effort goes. THE SIZE LINE RAN, AND IT IS NOW PARKED AGAIN BEHIND E
AND LOWER — see §16's ⚠.** This paragraph twice said the opposite and both
readings were taken from the wrong object. The standing rule is §16's: *nothing
pays on the artifact as it stands today*, because that artifact is a fraction of
the 197 constants, overwhelmingly `_class`, and **zero theorem proofs** — so three
of the four O-phase closures are facts about a corpus that is not the product. Re-run every
O-phase after E and LOWER are in the artifact, not before.

The sizing argument that motivated running it early still holds and is not the
thing that was wrong: the artifact costs thousands of lines per constant, so at
R6's ceiling of 195 the total is large enough that a per-line lever compounds with
coverage. What was wrong was measuring that lever against a corpus with none of
the proofs in it.

That is a reason to MEASURE the remaining candidates now, not to build on faith.
§16 gates every one of them on a measurement and lets each end at
CLOSED-worth-nothing; two of the five are already closed that way.

**Why P5 precedes P4** `tests: export::defs::tests::only_one_constant_is_class_free`

An earlier draft of this table ordered P4 before P5, on the reading that a
constant is defined over *earlier constants* and so bottoms out without ever
needing a class. Measured against the export, that is false almost everywhere:

| | measured |
|---|---|
| term constants (`C(x⃗) ≡ body`) | **197** |
| of those, **class-free transitively** | **1** — `IFOL.Let`, not even a ZF constant |
| bodies carrying a λ | most of them |

The fourth constant in definitional order is
`Upair(a,b) ≡ Replace(Pow(Pow(0)), λx y. …)`, so `Upair_EX` is Replacement at a
concrete φ — a class. Every ZF constant routes through
`Upair`/`Collect`/`Replace`/`PrimReplace` this way, so **P4's criterion is not
reachable before P5 exists.** The obligations `statement/` records
(`Obligation::ClassExists`, `Cong`) were always Compiler B's to discharge; what
was wrong was believing the constant table could close first.

*The alternative, rejected:* define the constants by conservative
characterisation instead — `upair(x,y,w) ↔ ∀u.(u∈w ↔ (u=x ∨ u=y))`, as the tier-2
probes do — which needs no class. But that is **not Isabelle's `Upair`**, and
adopting it without proving the two coincide substitutes a different constant
under the same name. Every theorem about `Upair` would then be a theorem about
ours. That is FOUNDATION §4's failure mode at a new site, so the raw definition
is forced,
and with it the dependency on classes.

*Also corrected by the same measurement:* §9 once sized the constant table by
counting `*_def_raw` definitions. The `_def` theorems are **197 term constants
plus predicates, connective definitions, and one neither**. A predicate is S4
material and carries no EX/UNIQ/CONG — it denotes nothing, so there is no value
whose existence could be owed. **Only the 197 are P4's work.**

**P6 sized.** "Two hand-built proofs is not evidence about the corpus" is true and
unactionable. Measured instead (`export::tests::p6_leaf_table_and_shape`), the work
is a **finite table** of distinct `ZAxiom` names: a handful of Pure meta-rules
carrying nearly all the traffic, the ZF axioms, the constant definitions, and the
datatype/inductive package axioms. §8 tier 7 already verified most of the Pure
rules re-render and the rest are rare; the constant definitions are P4's output.
**So P6's genuinely new rule table is small, and the traffic is concentrated where
it is already verified.**

Shape, corpus-wide: the median proof term is a handful of nodes and the
distribution is extremely long-tailed, with about half of all proofs **thin
wrappers** — a `ZAppt` chain around a single `ZThm`, which is §8's "named theorems
are thin wrappers" finding quantified. **The residual risk is therefore the TAIL,
not the bulk**: whether the largest proofs contain shapes neither hand-built probe
exercised. That is the honest statement of what P6 still has to discover.

Three of these criteria are worth defending individually.

**P0 first, and it is not scaffolding.** Every later phase's test is "the checker
accepts this Unit". Until the harness exists, no other phase has a criterion at
all — it has only an opinion about its own output. This is FOUNDATION §5's
instrument rule applied to the build itself.

**P2's criterion is a regression test, not a milestone.** The §9 census is a
script; wiring it in means a future export that introduces an eighth proof tag,
or an oracle, fails the build rather than being silently mistranslated. The
premise §7 rests on stays checked instead of being checked once.

**P6's criterion is why the two end-to-end probes were built by hand.**
`zf_pair_e2e` and `zf_fst_conv_e2e` are the target the generator must reproduce.
If `theorem/` cannot regenerate them, it is wrong — and that is discovered on two
theorems rather than on the whole corpus. Hand-proving them first was not a
detour; it was building the acceptance test before the thing it accepts.

**Equality is not a phase — it threads.** Atom-level substitution is P1 (tier 1),
per-constant CONG is P4, per-formula congruence is P5, and P6 consumes all three
through the `eq_reflection_rel` / `subst_rel` kernels. §8 shows the family is 18%
of IFOL citations, so this thread is on the critical path; it is nonetheless not
separate work, which is the point of the measurement.

**On the metric.** "Proved" must mean the transitive dependency closure bottoms
out in the 19. FOUNDATION §4 records the old encoder buying 144 with 214 `axiom` stand-ins
and 109 UNPROVED schemas; §1 above shows a *failed* schema would have counted
too. Coverage restarts near zero, and that is the number being honest.

---

### Why executing P0–P7 translates the corpus

Not a hope about coverage — an induction, whose premises are measurements.

> **Claim.** After P0–P7, every exported theorem σ with proof term π yields a Unit
> the checker accepts with empty stderr, whose def contains only the 19 and §10's
> admissible introductions.

The proof is **structural induction on π**, and an induction needs exactly four
things. **Each phase supplies one of them** — which is why this is the plan and
not a work breakdown:

**I — the induction is well-founded.** A `ZThm` leaf recurses into *another
proof*, so termination requires the citation graph to be acyclic. ✓ **acyclic over
the whole export.** Established and kept by P2.

**II — the case analysis is exhaustive.** π is built from exactly seven
constructors, and there is no `Oracle`. ✓ measured corpus-wide (§9). Seven rules
⇒ every node has a case. Supplied by P6, regression-tested by P2.

**III — the leaves discharge.** `ZThm` resolves to another proof — ✓ **all but
one, and that one is the export gap named below** — so the induction handles it.
`ZAxiom` ranges over a *finite enumerated* set: the Pure meta-rules, the ZF axioms,
the constant definitions, the package definitions. Supplied by P1 and P4.

**IV — the side conditions discharge.** Statements must render, and the object
language has ✓ **only `i`, `o`, `fun`, `prop`** — no third base type, so §7's four
constructs are the whole gap (P3). A `ZAppt` at a compound term needs
materialisation — ✓ `zf_fst_conv_e2e` (P6). An equality rewrite needs CONG — ✓
`eq_reflection_kernel`, discharged per-constant (P4) or per-φ (P5). A ZF-operation
call site needs its class hypothesis, dischargeable **iff φ is predicative** —
which is **free by construction**: Isabelle/ZF has no class type, so no translated
formula can quantify over classes (P5).

Given I–IV the induction goes through; G1 confines every def to the 19 plus
admissible introductions and L/G2 keep every schema implemented, so the transitive
closure bottoms out in the 19 — the metric above. §7's chain then delivers
`ZFC ⊢ σ`.

**The premises, as measurements rather than assumptions:**

| premise | status |
|---|---|
| citation graph acyclic | ✓ no cycles |
| constructor set closed, no oracles | ✓ exactly the seven |
| citations resolve | ✓ all but the one export gap below |
| object language is `i`/`o` only | ✓ no third base type |
| predicativity | ✓ free — no class type in the source |

**⚠ THE MAGNITUDES ARE IN THE TESTS, NOT HERE.** `export/tests.rs` asserts each
row; a count copied into this table is stale the next time the export moves and
still reads as authoritative.

**Citation resolution is not by serial.** Serials are unique only *within* a
theory: many serials occur in two theories with **different content**
(`ZF.Arith/14846` is `Arith.pred`, `ZF.QUniv/14846` is `QUniv.quniv`). The rule P2
must implement is **(theory, serial), with a unique-serial fallback** — exact match
resolves the bulk, the fallback the remainder with *no* ambiguity, and every
citation into a colliding serial resolves exactly. **⚠ A GLOBAL serial→proof MAP
SILENTLY MERGES DISTINCT THEOREMS.**

### Four limits on the claim

1. **The ceiling is not the whole export.** One cited proof, `ZF.List/22636`, is
   absent from it, and a few theorems depend on that one. The shortfall is an
   *export* gap, not a translation gap.
2. **Completeness is relative to the export.** Whatever the exporter omitted or
   flattened, we inherit.
3. ~~**One base case is undemonstrated — recursion.**~~ **Closed** (§8,
   `lfp_recursion`, probed before P0): `lfp` derives from Power + Separation +
   Union, and every WF route bottoms out in `The` (tier 6 ✓). **The `Fixedpt`
   exposure — a large share of the corpus — is no longer gated on an unknown.**
   What remains there is S3's mechanical propagation over the affected constants,
   plus `lfp`'s CONG, which propagates by `compose_cong` ✓ but is not separately
   derived.
4. **Completeness is not faithfulness.** All of the above is N1. N2 is guarded by
   G0 alone. Translating the whole reachable corpus *unfaithfully* is worth
   nothing, so what this argument supports is "the checker accepts a Unit for every
   theorem" — that the Unit *says what Isabelle said* rests entirely on G0.

### What would falsify this

Named in advance, so a surprise is a decision rather than a reopening:

- **A proof-space tag outside the seven**, or an oracle, in some future export →
  `export/` breaks. Measured false across all 40 theories today, and P2 keeps it
  measured.
- **A cited schema that is not parametric even with hypotheses.** The escape
  valve is per-site instantiation, but it must be *measured*, not assumed.
  `eq_reflection` and `subst` were the likeliest candidates and both survived
  (§8).
- **`class/` output growing superlinearly in φ** → the unit-granularity decision
  (§12) comes back.
- **A constant whose EX/UNIQ/CONG does not propagate** — the recursion base cases
  are closed (§8), but the propagation over the 39 package constants and the ~246
  ordinary ones is exercised only at P4.
- **G0 finding systematic divergence** → `statement/` is wrong. That falsifies a
  component, not the architecture.

None of these is a corpus count. The counts size the phases; they do not hold the
design up — FOUNDATION §5's discipline applied to the plan itself.

---

## 11. Still open

0. **`split`'s refusal is POLYMORPHISM, not S5 — and it now gates 49 of the 83
   survey refusals.** `every_survey_refusal_attributes_to_a_root_that_is_not_a_cascade`
   walks each refusal to its transitive root; `ZF_Base_2esplit` is the root of 49.
   FOUNDATION R6 rules it a permanent refusal because "the constant's **value** is a
   meta-function". What the export actually says is
   `split :: [i ⇒ i ⇒ 'a, i] ⇒ 'a` — **polymorphic in `'a`**, so
   `export::consts::read_all` gives it no signature at all. Measured: exactly THREE
   term constants lack one, `IFOL_2eLet`, `QPair_2eqsplit`, `ZF_Base_2esplit`, and
   they are the same missing-data root, not three separate obstructions.

   With no signature the renderer cannot know the arity, so the point-free
   definition (`split` binds 1 argument) cannot be eta-expanded and its body
   renders as a meta-function — which is the message R6 was read off.

   **At `'a := i` the constant is `[i ⇒ i ⇒ i, i] ⇒ i`, an ordinary term constant.**
   Every ZF use instantiates `'a` at `i`, because ZF terms are all `i`. So the
   "route around `split`" that R6's ceiling of 195 requires is plausibly
   *monomorphisation at the use site*, not a translation of a meta-function.

   **⚠ NOT ACTED ON, DELIBERATELY.** Whether `'a := i` may be assumed is a question
   about §13's specification map and §14's source calculus, and R6's ceiling depends
   on the answer. It is recorded here rather than decided in passing. What IS
   established: the refusal message names the wrong cause, and the same wrong cause
   already cost this document two constants of ceiling once (FOUNDATION §303's
   `cond`/`update` correction).

1. **Compiler B's implementation** — **landed for P4's purposes** (`src/class/`).
   §10 P5's criterion is met: the ψ compile is regenerated and the kernel accepts
   it. The predicativity gate is in and is **exact rather than heuristic**:
   §6 makes every legitimate `i`-quantifier carry its `set(·)` guard, so an
   unguarded quantifier in φ *is* a class quantifier.

   Tier 3's **Expansion** is wired into the atom case (`tuple_lemma`), so an atom
   sits at `(i,j)` of a context up to 3, with T4 when the slots are reversed and
   B5 when one side is a parameter. §5's **normalisation rules 2 and 3** are in,
   as *local bridges* rather than a rewrite pass — `Node::Bridge` carries one
   fixed equivalence per connective over the ORIGINAL children, so the emitted
   claim quotes the caller's φ. `∨ → ↔ ∀` and `eq` therefore compile, and with
   them real constant bodies: `Upair`'s φ compiles as a graph.

   What remains:
   - ~~**Arity 4+.**~~ — **closed.** `class::mem` generates `mem_n`/`mem_n_at`
     at any width; `compiles_top_level_tuples_past_the_base_widths` checks 2–6
     and `expansion_is_the_arithmetic_foundation_3_states` runs to width 11.
     Expansion is likewise not capped at a context of 3.
   - **§5 rule 1**, for a parameter LEFT of `∈` (S5's side condition). Its
     rewrite introduces an `eq` atom that expands again — two levels of arity
     growth — so it is refused rather than half-applied. This is what `Diff`
     still refuses on, and it is NOT the graph obligation.

   The remaining one is a named refusal, so the gap is visible rather than
   silent.
2. ~~**Complex-term materialisation against real data.**~~ — **closed** by
   `zf_fst_conv_e2e` (§8): `fst_conv` cites `fst_def` at the compound term
   `⟨a,b⟩`, and both levels materialise by `exists_elim` with neither witness a
   term. No new device; `iota_elim` stays banned. What it opens instead is
   engineering: Compiler A must decide, per `ZAppt`, whether the argument is a
   term (→ prelude) or a proposition (→ `schema_inst`), and §8's third export
   finding says that decision needs the **theorem database**, not the proof term.
   **§17 refines this**: the dispatch is a property of the CITED THEOREM's
   rendering — non-empty `schema_params` — not of the argument.
3. **The remaining constants.** Tier 6 proves the *propagation* and two base
   cases. The list is now measured rather than estimated
   (`export::defs::tests::*`): **197** term constants, a dependency graph that is
   **acyclic** — so definitional order exists and G3 is checkable — bottoming out
   in **exactly 5 primitives**, `zero`/`Union`/`Pow`/`PrimReplace`/`Inf`, which
   are axioms 11, 13, 14, 16, 15. Nothing at the bottom is a new admission.

   **`Inf` no longer blocks closure** — `infinity` is pinned in `base/axioms`
   (`base::ADMITTED`), so all five primitives are admitted and the table bottoms
   out. `export::defs::tests::the_table_bottoms_out_in_five_admitted_axioms`
   checks both halves: the five, *and* that `base/` admits each one.

   **The two halves of the introduction.** The export states `ZF_Base.infinity`
   as `0 ∈ Inf ∧ (∀y∈Inf. succ(y) ∈ Inf)` — a property of the **constant**,
   using `zero` and `succ`. That is §10's G1 Skolem row, `Inf(r) → φ(r)`. It is
   *not* statable in `base/`, because `succ` is a defined constant far down the
   definitional order (`succ → cons → Un → Upair → Replace`). So `base/` carries
   the **existence** half — `∃r. φ(r)`, axiom 15, with successor spelled
   relationally, since S1 leaves no function symbols to write it with — and
   `Inf` is introduced as a Skolem constant when the constant table reaches it.
   The two statements are halves of one introduction, not rivals.

   **This is the one base axiom that is stated rather than transcribed**, so it
   is exercised rather than trusted: `empty_from_infinity` derives Empty from it.
   That establishes well-formedness and usability, **not** that the statement is
   the intended one — an over-strong axiom would pass the same test. The intent
   rests on the correspondence with `ZF_Base.infinity` above. Two remain
   unpinned: Regularity (18) and Choice (19).

   *Noted, not acted on:* axioms 11 and 15 now **overlap** — Empty is a theorem
   of Infinity here. Both stay admitted; R1 governs what may be admitted, not
   whether the 19 are independent.
5. **`Inf` never needs a graph, and `nat`'s comes from a proved equivalence.**
   `Nat_2enat` is the corpus's single largest root. It emits only if its graph
   compiles, and its graph meets an `Inf` atom, for which `class::read` has no rule.

   *Why `Inf_GRAPH` is IMPOSSIBLE rather than unbuilt.* `Inf` is the one
   `Intro::Skolem` primitive and the only one carrying no `_CONG` — `Pow`, `Union`,
   `PrimReplace`, `kpair` each have one, and `zero` gets substitution through its
   `@def`. Compiling `{r : Inf(r)}` needs `eq(r,c) → Inf(c) → Inf(r)`. That follows
   from neither `Inf_intro` — uniqueness runs the other way — nor `Inf_prop`, which
   is one-directional *by design*, because Infinity's φ holds of MANY sets. So it
   could only be ADMITTED, and R1 forbids that. `base/tiers/skolem`'s header already
   argues the definitional route is closed; this is the same wall from the graph side.

   *Why that does not block ω.* Read from the export rather than assumed —
   `nat ≡ lfp(Inf, λX. {0} ∪ {succ(i). i∈X})` (`ZF.Nat`, serial 10656) and
   `lfp(D,h) ≡ ⋂{X ∈ Pow(D). h(X) ⊆ X}`. So `nat = ⋂{X ⊆ Inf : X inductive}`:
   **minimality lives in `Inter`, and `Inf` is only the bound** that keeps the
   intersection over a set rather than a proper class. ω is unique by
   EXTENSIONALITY with no uniqueness assumption on `Inf`, so the base axiom and the
   Skolem introduction both stay exactly as they are.

   *The route.* Keep `@def(nat)` Isabelle's — defining ω by minimality and calling it
   `nat` substitutes a different constant under the same name, which is §4's failure
   mode and the one this section's own `Upair` argument (§10) rejects. Prove the
   characterisation alongside it,

       nat(r) ↔ ( inductive(r) ∧ ∀s. (inductive(s) → r ⊆ s) )

   **⚠ THIS ROUTE IS CIRCULAR AS WRITTEN, AND §18 IS THE FIX.** `nat_0I`,
   `nat_succI` and `nat_induct` all mention `nat` in their statements, so
   translating them needs `nat` in `ConstEnv` — which this section assumes comes
   after the graph. The order is: `nat` reaches L1 WITHOUT a graph, which is all
   `ConstEnv` requires; the three theorems then translate; the characterisation
   follows; the graph compiles last. Read §18 before acting on the paragraph
   below.

   and compile `nat_GRAPH` from the RHS through the equivalence hook `graph_unit`
   already takes (`class/graph.rs:352`). TRANSLATE the characterisation: `Nat.nat_0I`
   10736 and `Nat.nat_succI` 10742 give `inductive(nat)`, `Nat.nat_induct` 10770 at
   `P(x) := x ∈ s` gives minimality, and **`Fixedpt.lfp_Int_lowerbound` 5946** is what
   makes it hold against an inductive set not assumed `⊆ Inf` — without that lemma the
   characterisation stays Inf-relative and buys nothing.

4. **FOUNDATION §4's question** — answered at rule level (§8 tier 7) and now on
   real data at a compound term (§8, `zf_fst_conv_e2e`). No mathematical
   obstruction remains; what is left is item 1's and item 2's engineering.

### Corrections owed to FOUNDATION.md

- ~~**FOUNDATION §1 axiom 3** must read `↔`~~ — **landed** (§0).
- **FOUNDATION §2 S3's justification does not cover its claim.** It says introducing a
  primitive constant "means `∃!r. C(r)` — conservative because `⊢ ∃x. φ(x)`."
  Existence does not license *uniqueness*: Infinity's φ holds of many sets. The
  introduction is still conservative — any model expands by interpreting `C` as
  some chosen witness — but the reason is Skolemisation, not the existence proof.
  The reason matters because it is what §10's G1 has to check.
- **FOUNDATION §3's risk note** is right but overstated: the flattening identity is free, and
  the cost is `pair_ex` plus a linear `set(·)` chain (§8).
- **FOUNDATION §3's Expansion formula** should read `[i>1]×T1`, not `1×T1` — T1
  fires zero times when `i=1` (§8).
- ~~**FOUNDATION §2 S3's second base case.**~~ — **landed.** `The` is not a base
  case in this export: Isabelle defines it, so it reduces by the induction step,
  and item 3's five primitives never included it. The `∅`-default is delivered by
  `⋃∅ = ∅` rather than assumed. `the_EX`/`the_UNIQ` are deleted from `base/`
  (§8) and the agreement is now a kernel-checked bridge.

---

## 12. The design

§9 lists the components. This is how they are arranged, and the arrangement — not
the list — is what keeps a hack from leaking. Read after §9.

### The one structural decision

**This is a build graph of independently checkable units, not a compiler
pipeline.**

A pipeline is what produced the encoder §4 describes. Stages could repair what
earlier stages could not express, and that is exactly how reification went from a
convenience to load-bearing: in a pipeline the interface between stages is *our
own data structure*, so a compromise in stage 3 is invisible to stage 2 and
invisible to the kernel.

§8 already states the alternative, one node at a time. Generalise it:

> **The only currency between components is a Unit — a `.fol.def`, a
> `.fol.proof`, and a dependency list, which the checker has accepted with empty
> stderr.**

Nothing crosses a component boundary except FOL text the kernel has already
certified. A hack cannot propagate, because the only thing that propagates is
something independently verified. The probes in `phase2_probes/` are not
scaffolding for this design — they are the first instances of its one data type.

### What is fixed, what generates — forced, not chosen

| | why | multiplicity |
|---|---|---|
| **fixed content** — the 19, tiers 1–3, logic schemas, ZF-op characterisations | finite theorems, proved once, never vary | fixed |
| **generator, per constant** | S2/S3: obligations attach to constants and reduce by definitional order | one per constant |
| **generator, per formula φ** | class existence is a **metatheorem** (§5), so it cannot be fixed content — it must emit a fresh derivation per φ | per site, deduped |
| **generator, per theorem** | one proof term in, one derivation out | one per proof |

**Exactly three generators over a fixed base.** That is not a decomposition
chosen for tidiness; it is what "class existence is a metatheorem" and
"obligations reduce by definitional order" mean operationally. Any design with
four generators has invented one; any with two has merged two things the
mathematics separates.

### Layout

Each generator module is named for the **unit kind it emits**. `base/` is the one
kind never generated.

```
rs/
├── base/                    hand-written .fol — the ONLY place `axiom` may appear
│   ├── axioms.fol.def           the 19
│   ├── tiers/                   eq core · pairs · tuple lemma · expansion
│   ├── logic/                   the IFOL/FOL schemas
│   └── zfops/                   collect_char · replace_char · the_* · ex_all_bridge
│
└── src/
    ├── unit.rs              ★ Unit = { def, proof, deps }. The only currency.
    ├── export/              Isabelle in.  Knows nothing about FOL.
    ├── target/              FOL out.      Knows nothing about Isabelle.
    ├── statement/           Compiler A — Isabelle term → guarded formula + obligations
    ├── class/               Compiler B — φ → class unit + congruence unit
    ├── constant/            S2/S3      — constant → unit (@def + EX/UNIQ/CONG)
    ├── theorem/             proof layer — serial → unit (claim + derivation)
    ├── gate/                the instruments, each with its reject fixture
    └── build/               the DAG: resolve deps, generate, check, gate
```

Two properties fall out. **Content-hashed unit names** (`class/<sha of φ>`) dedup
automatically — one φ compiled at many call sites is one unit. And **every
module's test is the same test**: hand its output to the checker. The probe
methodology becomes the test suite unchanged, rather than being replaced by
something weaker once the code exists.

The checker supports this directly: the def grammar has `include`, and the CLI
takes dependency defs and proofs (`<def> <proof> [deps] -- [dep proofs]`). So the
base is built once and depended on, not re-checked per run.

### The seals — structural, not disciplinary

The tree already does this twice. Extend it systematically; each row is a
*category* of the errors §4 catalogues, closed by construction:

| leak | seal |
|---|---|
| Isabelle term reaches the target | `target/` does not import `export/` — a module-graph test |
| description term-former | `FolTerm` has no variant ✓ |
| `eq_subst` / `iota_elim` | `Step` has no variant ✓ |
| `eq_sym` | **still representable; §3 bans it.** §10 P1 |
| **reified proposition (S4)** | `Rendering` is `Prop(Formula)` \| `Value(Relation)` \| `MetaFn(..)`, with **no conversion from `Formula` to `Relation`**. Reification is untypable, not discouraged |
| **unguarded `i`-quantifier (S6)** | the constructor takes the guard: `forall_set(x, body)`. §6's "always emit" becomes an invariant rather than a pass that can be forgotten |
| unproved schema | no unit may declare without implementing (§2, per unit) |
| **stand-in axioms** | **only `base/` may emit a bare `axiom`**; every other unit gets `@def` over earlier symbols, or Skolem-with-proved-existence. This closes the 214-axiom mode in §4 permanently |
| proof/term tag confusion | `AppT { p: Box<ProofTerm>, t: Term }` — the second field is a `Term`, so no traversal can walk it as a proof (§9's method note) |
| silent fallback | every generator returns `Result<Unit, Refusal>`, and **`Refusal` is terminal** — no weaker unit, no `_\|_`, no default. A refusal fails the build |

### Two constraints worth stating explicitly

**G0 is a conformance check, not a back-renderer.** An earlier draft of this
section required back-rendering `σ*` and diffing against the export's `prop`
node. §13 supersedes that: back-rendering is ill-posed, because S1 is one-to-many
and β-reduction is not invertible. What is well posed is deciding
`σ* = ⟦σ_isa⟧` for a **fixed** specification map — §13 fixes it. Prefer a
parallel-walk matcher over a second renderer: matching is a different algorithm
from generating, so it is independent in the sense that matters, and it need not
duplicate the constant table.

**`Refusal` is terminal, and this will hurt before it helps.** Early on most
theorems will refuse. The pressure will be to emit a partial unit or a weakened
claim — which is precisely the N2 violation §6 describes, reporting green. §10's
note that coverage restarts near zero is the same point stated as a metric.

### Open decisions

- **`base/logic/`: generated or hand-proved?** Generating them from
  the export's own IFOL/FOL proofs is uniform, but makes the base depend on the
  proof layer — a cycle. Hand-proving is a large dull one-time job that keeps the
  base acyclic. Leaning hand-proved *for the acyclicity*, but the cost is real.
- **Unit granularity:** per theorem, or per SCC of the citation graph? Per
  theorem is simpler and dedups better; SCC means fewer checker invocations.
- **Module naming:** output-kind names (`statement`/`class`/`constant`/`theorem`)
  versus the doc's `Compiler A`/`B`. Resolved in favour of output-kind names with
  a `§` reference in each module doc; recorded because the doc and the code
  otherwise drift apart.

---

## 13. The specification map

§10's completeness argument and G0 both refer to "the rendering of σ". This
section makes that a **function**. Until it is one, G0 is not well defined and
two emitters can both be "right".

### The four objects, named apart

FOUNDATION uses two names where the chain has four, in three languages, and the
two-name notation hides exactly the step S1 and S2 govern.

| name | language | what it is |
|---|---|---|
| `σ_isa` | Pure over `{∈,=}` **plus defined function symbols** | the exported theorem as stated |
| `σ°` | pure ZFC, `{∈,=}`, **no function symbols** | `σ_isa` after Pure-elimination, β-normalisation and unnesting |
| `⟦σ_isa⟧` | `Σ = {elem,eq,set}` | the specification's value, `(σ°)^set` |
| `σ*` | `Σ` | what the emitter actually produced |

FOUNDATION's `σ`/`σ*` are this table's `σ°`/`⟦σ_isa⟧`. **N2 is `σ* = ⟦σ_isa⟧`.**

Worked, on `fst_conv`:

```
σ_isa    ⋀a b. Trueprop( fst(Pair(a,b)) = a )
σ°       ∀a b p. ( PairGraph(a,b,p) → ∀r. ( FstGraph(p,r) → r = a ) )
⟦σ_isa⟧  ∀a. set(a) → ∀b. set(b) → ∀p. set(p) → ( kpair(a,b,p) →
                      ∀r. set(r) → ( fstrel(p,r) → eq(r,a) ) )
```

which is `fst_conv_all` (§8) up to naming — the hand-built probe and the
specification agree, which is the first evidence the map is the intended one.

### N2 is decidable, and an earlier framing of it was wrong

An intermediate draft defined N2 as `T ⊢ σ* ↔ ⟦σ_isa⟧` — *provable* equivalence —
and concluded it was undecidable. **That was self-inflicted.** Nothing requires
the acceptable set to be closed under provable equivalence. We emit `σ*`; the
question is whether we emitted the prescribed formula, which is α-equality once
`⟦·⟧` is a function. The conventions below are what make it one.

The claim language contains **no classes**: every translated statement is
relativised ZFC. Classes occur only inside derivations (Compiler B's witnesses,
the kernel schemas' `∀C`), and those are N1's business. That separation is why
G0 is syntactic.

### The four conventions — binding on every emitter

**(a) Unnesting order.** An occurrence `f(t⃗)` is unnested only once every
application inside `t⃗` has been: **innermost first**, and leftmost among
occurrences at equal depth, scanning atoms left to right. This is the order the
proof layer already materialises in (§8's `appt_nested` prelude), so statement
and proof agree by construction rather than by coincidence.

**(b) The `∃`-reading, always, in claims.** `φ(f(t))` becomes

```
∃r. ( set(r) ∧ ( F(t,r) ∧ φ(r) ) )        NOT   ∀r. ( F(t,r) → φ(r) )
```

scoped at the **atom**, minimally. The two are equivalent given EX and UNIQ, so
the choice is free — *precisely because* G3 discharges EX and UNIQ before any
statement mentioning the constant is emitted. That is an ordering constraint on
the build, and it is the reason the choice is safe rather than arbitrary. The
tie-break is deliberate: without EX the `∀`-form is **vacuously true** and the
`∃`-form false, so the `∃`-reading fails loudly where the other hides the bug.

**(e) Closure order is FIRST OCCURRENCE, and it is not ours to choose.** A
theorem's free variables are universally closed (they are implicitly generalised
in the source), and the order is **forced**: Isabelle's proof terms instantiate
them with a `ZAppt` spine in first-occurrence order, and `forall_elim` must peel
the quantifiers in the same order or every use site breaks. Measured:
`ZF.pair/3518` is cited with args `[c, A, B, P]`, its first-occurrence order,
where alphabetical would be `[A, B, P, c]`; **the two orders differ for over a
thousand theorems in five theories alone.** An earlier implementation sorted
alphabetically — logically harmless, since `∀x∀y φ ⊣⊢ ∀y∀x φ`, and fatal in
practice for exactly that reason: nothing about the *statement* would look wrong.

**Why (b) does not conflict with §8's "thread the witness" ✓**
`probes: scoping_convention.{def,proof}`

§8's Compiler B note says a proof should materialise **one** canonical witness
and thread it, never reconciling. Convention (b) scopes at the atom, which for a
term occurring in two atoms gives two existentials. These look opposed. They are
not, and the reason is that the two directions have very different costs:

| direction | needs |
|---|---|
| threaded ⟹ atom-scoped | **nothing** — instantiate both with the same `r` |
| atom-scoped ⟹ threaded | UNIQ(F) **and** CONG of the surrounding formula |

Both are derived in the probe. The proof layer only ever travels the **first**:
it threads one witness internally and weakens to the atom-scoped *claim* at the
end. The expensive direction is never needed, so the canonical form is free to be
atom-scoped and the proof strategy is free to thread. The statement convention
and the proof strategy are simply different things.

**But (b)'s FAITHFULNESS is conditional on UNIQ, and that is a cross-dependency
worth naming.** Isabelle's `φ(f(t)) ∧ ψ(f(t))` asserts both hold at *the same*
value; atom-scoping asserts each holds at *some* value satisfying `F`. Without
UNIQ that is **strictly weaker** — an N2 violation of exactly §6's shape, which
would check green. Required-to-reject ✓: weakening UNIQ(F) to a triviality makes
`atom_to_thread` underivable, so the hypothesis is load-bearing rather than
decoration.

So convention (b) is faithful *because* G3 discharges UNIQ before any statement
mentioning the constant is emitted — the same ordering constraint that makes the
`∃`/`∀` choice free, now doing a second job.

**(c) Generated names.** `_v0, _v1, …`, numbered in the order (a) fixes, and
**freshness is verified against the statement, not assumed**.

The original justification — "a leading underscore suffices, since
`sanitize_name` never emits one" — is **false**: `sanitize_name` passes `_`
through unchanged, so a source variable named `_v0` sanitizes to `_v0`. Measured,
the corpus contains no name starting with `_` in ANY statement, so nothing
collides *today*; but that is an accident of this export, not a property
of the encoding, and capture is silent when it happens. Generation therefore
skips any name occurring in the statement, bound or free.

**(d) Guard placement.** The guard is the **first** conjunct/antecedent and the
body associates right: `∀x. set(x) → φ`, `∃x. set(x) ∧ φ`, and for (b)
`∃r. set(r) ∧ (F(t,r) ∧ φ(r))`. This is what `forall_set`/`exists_set` build.

### The schematic-variable rule

Dispatch is on the variable's sort, and it is **S4 and S5, not one rule**:

| sort / category | rendering | why |
|---|---|---|
| `i` | guarded quantifier (b),(d) | S6 |
| `o` | schema parameter, arity 0 | S4 — a proposition is never reified |
| `i ⇒ … ⇒ i ⇒ o` (n arrows) | schema parameter, **arity n** | S4 |
| `i ⇒ … ⇒ i ⇒ i` | **not** a schema parameter — its *graph* becomes a relation parameter carrying EX/UNIQ/CONG hypotheses | S5: a meta-function argument compiles to a class |
| anything higher-order | **refuse** | outside §7's four constructs |

Parameters are declared in **order of first occurrence**, left to right, in the
Pure-eliminated statement. A statement with at least one schema parameter is
emitted as a `schema`; otherwise as a `claim`. Under-application of an arity-`n`
parameter is refused — the checker's schema arity is fixed.

**Dispatch is on the syntactic category, and that is grammar, not inference.**
`i` and `o` are not a type theory. `i` is the single sort of terms and `o` is the
category of formulas — the term/formula distinction every first-order language
already has. So the translation is the standard shape for a first-order
translation: **two mutually recursive functions**

```
F(φ)   formula → Σ-formula
T(t)   term    → (variable, constraining formula)          -- S1
```

and which applies is fixed by the grammar: arguments of `elem` and of function
symbols are terms; arguments of connectives and quantifier bodies are formulas.
Nothing is inferred.

Isabelle distinguishes `Free` from schematic `Var`, and one might expect the
schematic ones to be the parameters. Measured corpus-wide: **zero statements
contain a schematic `Var` — every one uses `Free` exclusively.** The exporter has
already un-schematised. Since a theorem's free variables are implicitly
universally generalised, every one is generalised by us: those of sort `i` by a
guarded quantifier, those in formula position as schema parameters.

**The two overloaded symbols.** Isabelle overloads exactly two constants across
the two categories:

```
IFOL.eq : 'a ⇒ 'a ⇒ o        Pure.eq : 'a ⇒ 'a ⇒ prop
```

At `'a := i` each is equality between terms. At `'a := o` there is no such thing
as equality between formulas, and both simply mean `↔`. This is a **notational
overload, two entries long** — not polymorphism doing any work — and the export
records the instantiation on the head `Const` node, so resolving it is a lookup.
It is resolved in `convert_term`, before the translation runs, so `RelOp::Eq` and
`RelOp::MetaEq` downstream occur only between terms.

*Getting this wrong is not a small matter: guessing the category from context
rendered a formula as a term — `eq(_r, A)` for a proposition `A` — which is
reifying a proposition, exactly what S4 forbids. `IFOL.eq_reflection` and
`IFOL.meta_eq_to_iff` are the witnesses. An intermediate draft of this section
proposed a "type reconstruction phase" to fix it; that was over-engineering a
grammatical distinction into a type-theoretic one, and it is withdrawn.*

### Sort constraints — why dropping an antecedent is sound here

`CLAUDE.md`'s translation table says sort constraints are "stripped — trivially
true in ZFC". That is hand-waving over a real hazard: **dropping an antecedent
strengthens the statement**, so `A ⟹ B ↦ B` is an N2 violation of exactly §6's
shape unless `A` is a theorem.

Measured, the rule fires in two forms:

| antecedent dropped | occurrences | why it is a theorem |
|---|---|---|
| `Pure.sort_constraint(type)` | 4 | **`Pure.sort_constraint_eq : (sort_constraint(type) ⟹ A) ≡ A`** — Isabelle proves the drop itself |
| `OFCLASS(τ, IFOL.term)` | the bulk | `i` and `o` are instances of class `term` in Isabelle/FOL, so the judgment holds |

So the justification is not "trivially true in ZFC" but *named Isabelle theorems*:
`sort_constraint_eq` states the equivalence outright, and `sort_constraintI`
supplies the constraint. That is a much stronger footing than the table claimed,
and it should be recorded as such.

There is also a reason nothing else is possible: a class-membership judgment is a
**Pure-level statement about types**, not a formula of the object logic. Our
target has no types, so there is no Σ-formula it could become. Dropping is the
only rendering, and it is sound because the judgment is a theorem.

*Residual, stated rather than glossed:* the `sort_constraint` case is verified
from the export (`Pure.sort_constraint_eq` is there, and reads exactly as above).
The `OFCLASS(τ, term)` case rests on `i` and `o` being instances of `term` in
Isabelle/FOL — true by construction of that theory, but I have **not** located
the instance judgment in the export, so that whole form rests on knowledge of
Isabelle rather than on data in front of us.

### Hypothesis-strengthened schemas

§8's equality family (`eq_reflection`, `subst`) cannot be parametric without
congruence hypotheses, so their emitted form is

```
H₁ → … → H_k → ⟦σ_isa⟧
```

with each `Hᵢ` drawn from the fixed admissible set {EX, UNIQ, CONG,
class-existence}. This is *weaker* than `⟦σ_isa⟧`, so it never over-claims, and
G0 stays syntactic: it checks that the **conclusion** is exactly `⟦σ_isa⟧` and
that every added antecedent has admissible form.

### Which hypotheses a schema carries — the uniform rule

§8's equality family is not parametrically provable without congruence, so those
schemas emit as `H₁ → … → Hₖ → ⟦σ_isa⟧`. Computing `{Hᵢ}` looked like it might
require attempting the proof and reacting to failure, which would be this
design's first genuine fallback. It does not.

**First, a correction to how the question was posed.** The hypotheses are *not* a
property of the statement. Isabelle's `subst : a = b ⟹ P(a) ⟹ P(b)` is
**primitive** in IFOL and underivable for us at uninterpreted `P`, so what a
schema needs depends on which rules its *proof* invokes — a property of the proof
term. A syntactic test on σ cannot decide it.

**But the question dissolves on an asymmetry.** Attaching CONG(P) for **every**
predicate parameter is:

- **sound** — it weakens the schema, so it never over-claims, and G0 already
  admits antecedents of admissible form;
- **always dischargeable** — at a call site `P` is a concrete φ, and CONG(φ) is
  exactly Compiler B's second output;
- **analysis-free** — no search, no attempt-and-retry, no fallback.

Nullary parameters get `eq(a,b) → (P ↔ P)`, which is vacuous. So the uniform rule
is total, and the hypothesis set is computed by not computing it.

The cost is that call sites discharge congruence they may not need. Measured: a
syntactic test (*some parameter applied to ≥2 distinct argument tuples*) flags a
small minority of IFOL+FOL theorems. So an optimisation that omits CONG where the
proof never invokes `subst` at `P` would spare most call sites — worth
having, and strictly a **performance** pass, separately verifiable, never a
prerequisite for correctness.

**What remains genuinely open** is not *how to compute* the hypotheses but
**whether CONG is the only kind needed**: is every IFOL/FOL primitive either
derivable in tier 1, or reducible to a CONG hypothesis? That is a finite
enumeration over the logic layer and is answered by building it, not by argument.

### What G0 is, restated

A decision procedure. Input `(σ_isa, σ*)`; output pass/fail; decides
`σ* = ⟦σ_isa⟧` up to α, modulo the admissible antecedents above. Linear, total,
no search.

It establishes **row 3 of §10's chain and nothing else**. It does not establish
that `⟦·⟧` is the right map — if S1–S6 is wrong, G0 passes and we are wrong. §0
is the standing instance: Extensionality as `→` was a *specification* error, found
by failing to derive `set_cong`, not by any gate.

Division of labour with G5: **G5 says `σ*` is *a* relativised formula; G0 says it
is the relativisation of *this* `σ_isa`.** G5 without G0 permits translating the
wrong theorem correctly.

---

## 14. The source interface

`src/meta.rs`. Two things are **frozen**: `Proof`, what the export lowers into,
and `Provider`, what the foundation answers. The passes and the intermediate
IRs between them are not, and are meant to change.

### The source calculus

Strip the Isabelle vocabulary and the export is a two-level typed λ-calculus,
`Γ ; Δ ⊢ p : A` with object variables in `Γ` and proof variables in `Δ`.

```
  Sorts   s ::= i | o | prop | s -> s'
  Props   A ::= <t> | A ==> B | ALL x:s. A | t == t' : s | OFCLASS(s, c)
  Proofs  p ::= h | K | \h:A. p | p q | /\x:s. p | p<t>
```

Six rules plus two kinds of constant — exactly the seven proof-term shapes the
corpus contains. Four of Isabelle's eleven constructors (`MinProof`, `Hyp`,
`PClass`, `Oracle`) have **zero** occurrences anywhere in the export, so the source
language is closed and smaller than §7 assumed.

The measured shape, which is what the ceilings below rest on — **`export/tests.rs`
carries the magnitudes; only the shape belongs here:**

| | |
|---|---|
| `ALL` binds `i` | the overwhelming majority |
| binds `o`, `s->o`, `prop`, `i->i` | a small residue |
| binds a type variable | rare, and all in the generic `FOL`/`IFOL` layer |
| `==>` assumes an object formula | the overwhelming majority |
| assumes `ALL` / `==` / `==>` | **⚠ HYPOTHESES ARE NOT ALWAYS FIRST-ORDER** |
| assumes `OFCLASS` / meta conjunction | rare |

### The translation, and the three strata

```
  [[ <t> ]]           = F(t)
  [[ A ==> B ]]       = [[A]] -> [[B]]
  [[ ALL x:i. A ]]    = forall x. (set(x) -> [[A]])        R3, interleaved
  [[ t == t' : i ]]   = relational equality
  [[ t == t' : o ]]   = [[t]] <-> [[t']]
  [[ ALL x:s. A ]]    = UNDEFINED for s /= i
```

The strata are three statements about that map, not three categories to
dispatch on.

**A.** Where every binder sort is `i`, `[[.]]` extends from propositions to
*proofs* — a homomorphism onto target natural deduction. No classes.
`ALL`-elim at `t` owes a proof of `set(t)`, created by the guard on the third
line; **these discharges are the dominant cost of the whole translation.**

**B.** The `==`-fragment is an equational theory. Measured, it is *mostly
propositional* — `combination`, `symmetric`, `reflexive` and `transitive` at `o`
and `prop` account for a large share of all uses, and that share is `Trueprop` and
connective plumbing, which becomes `<->` reasoning. No classes. Function-sorted
equality is common but is almost always `c == c` for a **fixed constant**,
discharged by that constant's CONG.

**C.** `ALL` at `s /= i`, and congruence under a λ. Genuine function equality is
only `abstract_rule`, and most of its uses equate *predicates* at `[i,o]`, which
alone needs no class: `\x.φ == \x.ψ` at `i=>o` is
`forall x. (φ <-> ψ)`. A class is needed only when such a λ is passed as a
constant's argument, which is S5, which is object elimination.

### The pipeline, and why the order is forced

```
  IR1  TYPED PROOF TERM                                    FROZEN
    |      frozen MECHANICALLY: the exhaustive `frozen_*` matches in
    |      `ir/meta_tests.rs` do not compile if a variant is added, and
    |      `impl Provider for NoFoundation` does not compile if a fifth
    |      operation is. Verified by adding `Sort::Nat` and watching it fail.
    |  H   normalise to beta-eta-normal form
    v
  IR2  invariant: beta-eta-NORMAL, decided by `meta::Proof::redex`, which
    |            returns the offending term rather than a bool
    |  S   object elimination; compile every surviving lambda to a class
    |      calls ex, uniq, class                      ALL class work
    v
  IR3  invariant: every object is a variable, no lambda; every
    |            materialisation placed at the scope binding its free vars
    |  E   equational elimination; calls cong
    v
  IR4  invariant: no == anywhere
    |  LOWER   homomorphism + R3 guards; NO provider calls
    v
  Script -> ir::Proof
```

**H first, and its real job.** Not "λ are inconvenient". Isabelle's kernel
identifies terms up to **αβη** silently; everything beyond that — provable
equality — appears in the source as an *explicit* equational step. So

> S's syntactic memoisation is sound **iff** IR2 is βη-normal.

Then "Isabelle identifies these implicitly" and "these are syntactically equal
in IR2" are the same relation, which is what a syntactic memo key assumes. H is
total on a theorem, not an assumption: Pure's terms are simply typed, so βη
normalisation terminates and normal forms are unique.

**A dedicated class pass is not schedulable.** `class::compile_at` needs φ in
the relational fragment — R5: *a raw relation atom `C(x,r)` has no rule*. So a
λ-argument's body must already be relationalised, which is S's output. Class
compilation is therefore a step *inside* S's recursion over objects, never a
pass before it.

**S before E, and E gets simpler for it.** After S, `f x` is a variable `v`
with a constraint `F(f,x,v)`, so congruence-for-application becomes exactly the
CONG citation. S needs only EX to materialise and never consumes E's output;
the dependency runs one way.

**Why passes and not one fold.** A materialisation must sit at the scope
binding its free variables — a closed term goes in the outermost prelude — so
first-use emission is *not* sufficient. Emitting into a linear `Script` would
need buffering and splicing. A pass builds the tree that way for free, and
LOWER then walks an IR3 in which every witness already dominates its uses.

### The refusal ceiling, stated up front

| refused | reach |
|---|---|
| `ALL` at a non-`i` sort | a small fraction of all binders |
| meta conjunction | rare |
| `Pure` internal definitions | a handful, all in `Pure/proofs/` |
| sort outside `i \| o \| prop \| ->` | type variables, generic layer only |

### `prop_of` is total, with one bounded obligation

`PThm` resolves by the **pair** `(theory, serial)`, which covers all but a handful
of citations. Neither component alone is a key: **serials recur across theories
with different content**, so a serial-only map silently merges distinct theorems;
and the theory tag disagrees with the file's own location on the remainder.
`meta::ThmId` is therefore the resolver's own index, and how that remainder
resolves is the resolver's decision to state — **not a fallback to be taken
silently (rule 1)**. `PAxm` at a `Pure` name resolves in `Pure/theory/axioms`, the
only `theory/axioms` file that exists. The object-level definitional axioms have
**no exported statement**; the mapping `X_def_raw ↦ X_def` is total, but no `_def`
theorem is proved from its own `_def_raw`, so it must be *checked* — the `X_def`
statement's LHS head constant must be the constant `X_def_raw` names — not
assumed.

### Unverified

- ~~The split between `t` already a guarded variable and `t` a compound needing
  S1 materialisation is unmeasured.~~ — **measured**
  (`the_object_elimination_census`, which asserts every count). After H, the `AllE`
  objects fall into five classes — **⚠ λ ARE COUNTED ONCE, INSIDE `fun`**, and
  subtracting them again is what made an earlier total wrong:

  | | what S owes |
  |---|---|
  | already a variable | nothing |
  | compound at sort **`i`** | **S1 materialisation** |
  | compound at `o` / `prop` | nothing — a PROPOSITION, S4 forbids reifying it |
  | function-sorted (λ included) | S5 — a class, not a materialisation |
  | head is a variable, sort unknown | — |

  **⚠ MATERIALISATION IS OWED AT FAR FEWER `AllE` SITES THAN A SHAPE-ONLY CENSUS
  SUGGESTS**, which counted every `o`-proposition as if it were a term. Most of the
  sites that do owe it are **CLOSED**, so one outermost materialisation serves every
  use, and they span a modest number of distinct head constants. Only a minority of
  proofs need S at all.

  *This is why "every object is a variable" is the wrong reading of IR3's
  invariant.* Only `i`-objects become variables; `o`- and `prop`-objects stay
  compound, because they are propositions and S4 forbids reifying them. **⚠ A SHARE
  OF THE COMPOUND OBJECTS IS NOT A SHARE OF ALL OBJECTS** — quoting one for the
  other is how this paragraph was previously wrong.
- Three intermediate trees over the whole proof-term corpus: memory and time
  unmeasured.
- Freezing `Provider` freezes FOUNDATION §13's admissible set. An obligation
  outside {EX, UNIQ, CONG, class-existence} is a specification change, not a
  refusal.

---

## 15. The derivation interface

`src/derivation.rs`. **NOT YET FROZEN, and it does not get to be until §15.5
Phase A passes.** §14 froze `Proof` because the export's shape is settled and
measured; this object is new, and freezing it on a design argument is what §5's
method forbids. What would freeze it is stated below, as a gate.

### 15.1 The object

A DAG carrying a scope tree `T`. Openers (`assume`, `exists_elim`, `fix`) create
a child frame; closers return to the parent, so a closer's result belongs to the
ENCLOSING frame. Two conditions, both decidable in one pass:

```
  applied(h) = the frame h CLOSED, if it closes one; otherwise f(h)

  LEGALITY    ∀ g ∈ ops(h).  f(g) ⊑ applied(h)
  PLACEMENT   f(h) = deepest of  { f(g) : g ∈ ops(h) } ∪ { binder(t) : t ∈ refs(h) }
```

**Both lines read `f(h)` in an earlier draft and both were wrong**; a six-line
known-answer proof refuted them on its first two runs, which is the argument
for the Phase-A gate over a design argument.

*Why `applied(h)`.* A CLOSER's operand lives inside the frame it discharges —
that is what the rule is for. `forall_intro _c` takes `_c` from within `fix A`
and lands outside it, so checking at `f(h)` rejects every closer in the corpus.

*Why `refs(h)`.* A step naming an eigenvariable cannot sit above its binder,
and the binder is not an operand: `_a = forall_elim _r, A` has its only operand
at the root and must still sit inside `fix A`. This is why `Script::earliest`
scans the WHOLE right-hand side rather than the handles in it — `cost::placement`
computes the same thing a second way, and the disagreement between them is
exactly the kind of gap one object removes.

**Congruence is sound WITHOUT formulas**, because rules are functions of their
operands: `rule`, `args` and congruent `ops` determine the derived formula. Only
leaves need their text as a key — which is why the volume path never needed
`proof_builder::Held`.

> **AN OPENER OR CLOSER IS NEVER QUOTIENTED.** Two sibling `assume φ` are two
> DIFFERENT hypotheses. The congruence is defined on interior nodes only.

### 15.2 The interface

```rust
  pub enum Rule {                       // LEAF PAYLOADS ARE RENDERED TEXT, not
      Use(String),                      // `Formula`: the Phase-A gate is byte-
      Assume(String),      // OPENS     // identity, so text is what is compared,
      Let(String),                      // and `Formula` would force a rewrite of
      SchemaInst(String),               // every `format!("assume …")` site for no
      Fix(String),         // OPENS     // gain until E wants to anti-unify leaves.
      ForallElim(String),               // the String is a TERM, not an operand —
      ExistsElim(String),  // OPENS     // which the text parsers cannot tell apart
      ExistsIntro(Option<String>),      // CLOSES iff None
      ImpliesElim, ImpliesIntro,        // CLOSES
      IffElimL, IffElimR, IffIntro, AndElimL, AndElimR, AndIntro,
      OrIntroL, OrIntroR, OrElim, NotElim,
      NotIntro, ForallIntro,            // CLOSE
      Qed,
  }
  pub struct Node  { rule: Rule, ops: Vec<NodeId>, frame: FrameId, label: Option<String> }
  pub struct Frame { parent: Option<FrameId>, items: Vec<Item>, depth: usize }
  enum Item { Node(NodeId), Frame(FrameId) }   // a closed child SPLICES here

  fn push(&mut self, Rule, &[NodeId]) -> NodeId              // at PLACEMENT
  fn push_at(&mut self, Rule, &[NodeId], FrameId) -> NodeId  // PHASE A ONLY
  fn push_named(&mut self, &str, Rule, &[NodeId]) -> NodeId  // `raw`'s analogue
  fn placement(&self, &[NodeId]) -> FrameId    // max{ f(g) }
  fn legal(&self) -> Result<(), Illegal>       // ∀ edges f(g) ⊑ f(h); one pass
  fn misplaced(&self) -> Vec<NodeId>           // = cost::placement.excess
  fn live(&self) -> Vec<bool>                  // = class::live
  fn qed(&mut self, NodeId)                    // pushes `Qed`, then closes all
  fn emit(&self) -> String                     // THE ONLY producer of proof text
```

`Item` is why emission is not a frame DFS: `Script::close` appends a child's
lines to the parent **at close time**, so a line hoisted into an open ancestor
precedes the child's lines even when emitted after them. `emit` reproduces that
or Phase A cannot reach byte-identity.

`push_at` exists because PLACEMENT is an **assertable property, not an
invariant**. `Script::earliest` is syntactic and "can only err too DEEP";
`cost::placement` reports a small percentage of derivations sitting deeper than
their operands require. Deriving placement would hoist those and change the output, so
the object must be able to represent a suboptimal placement. `misplaced()` is
that instrument, converted from a text parser into a check on the object.

`Rule` mirrors the kernel's rule set, so adding a variant is a kernel change and
not a pass change. `emit` is the SINGLE linearizer: `class::Script` and
`proof_builder::Script` should both build a `Derivation` and share it, neither
keeping its own text writer.

**NO FORMULAS ON INTERIOR NODES, and that is a soundness choice, not an
optimization.** §7 refuses a `recheck` that re-derives every step because
modelling the kernel's rules is where divergence hides — `exists_intro`
generalising *every* occurrence of a two-argument witness is the standing
example, and `proof_builder` got it wrong in exactly that way: it recorded the
named target while emitting the two-argument form, so `Held.formula` and the
kernel's stack disagreed with nothing to catch it. A witness still occurring in the
target is now REFUSED rather than encoded
(`exists_intro_takes_a_witness_only_when_the_target_does_not_hold_it`); such a proof is
restated over distinct binders. `proof_builder` models the rules already, which is affordable on
synthesis units of a few thousand lines and would extend the divergence surface
across the whole artifact. `legal()` checks scope only, models nothing, and the kernel stays
sole arbiter (N1).

> **A pass may rewrite a `Derivation`. Nothing may rewrite emitted text.**
> **`legal()` IS NOT A PROOF** — it catches a pass bug near its cause and says
> nothing about whether the derivation proves anything.

> **⚠ THAT IS PERMISSION, NOT DESCRIPTION: NOTHING REWRITES A DERIVATION.**
> The only optimisation that runs anywhere is `class::Script::step`'s memo, inside
> the EMITTER, and C measured it as saturated. Scope fusion and E do not exist.
>
> **⚠ DO NOT CHECK THAT WITH `grep 'mut Derivation'` — IT CANNOT SEE A PASS.** A
> pass is `Derivation -> Derivation` BY VALUE, so it never writes `mut Derivation`
> in a signature and the grep reads 0 whether or not one exists. That grep was
> offered here as the check and it was wrong. The real question is whether any
> pass other than `identity` has a production caller: `grep -rn 'derivation::apply'
> src/ --include=*.rs | grep -v _tests`.

It retires three fragmented versions of the same graph: `class::live`,
`cost::{steps,sharing,families,placement}` (which re-PARSE emitted text into a
DAG to count what could have been shared), and `class::Script`'s
`{memo, earliest, frames}`. The instruments reconstructing the graph is the
tell that it exists and is being discarded. `unit::needed_deps` and
`gate::claims` are the *claim* graph — a different object, Phase D.

### 15.5 Phases, each with a gate that can fail

**A — the object, and a round-trip. ✓ LANDED.** `parse` reads emitted text back
in; `emit` must reproduce it byte-for-byte over every proof the class compiler
produces, all of them `legal()`. A round-trip rather than
instrumenting `Script`, because it needs no change to the emitter, so a bug in
the object cannot corrupt the artifact. It proves REPRESENTATION and EMISSION;
it says nothing about construction, which is B. Required-to-reject: unknown
rule, unknown handle, no `qed`; and a hand-built node above its operand must
fail `legal()`. *§15.2 is frozen from here.*

**B — retire the string path. ✓ LANDED.** `Script` holds no line buffers and
parses no proof text: every call site passes a `Rule` and an operand list, and
`body()` is `emit`. **Gate met:** artifact and worst unit unchanged to the byte,
both configurations green, construction order preserved exactly so no `_h{n}`
moved.

`Rule::rhs` is THE ONE RENDERER — `emit` and the memo key both use it, so
keying the memo on `(rule, ops)` is the same relation the RHS string was.
**`parse` STAYS**, contrary to what this section first said: it is the reader
for CHECKED-IN proofs, which `base/tiers/*` needs and C wants. What B retires is
the emitter's DEPENDENCE on it.

> **⚠ CONSTRUCTION ORDER IS OBSERVABLE, AND B IS WHERE IT BITES.** An `_h{n}`
> label numbers by CREATION, not by text position — a hoisted line is created
> early and printed late (`_h5` at text line 19 of `sing_rel`). So a B that
> builds the same DAG in a different ORDER renames every auto label and fails
> byte-identity on a proof that is semantically identical. Either preserve the
> order exactly, or make the gate compare modulo consistent renaming — and say
> which, because the two are not the same claim.

Phase A must also keep the CURRENT memo policy — per-frame and text-keyed,
which is *weaker* than global hash-consing. Relaxing it is C's job, not B's.

**C — the instruments move onto it. ◐ ITS GATE IS ANSWERED; `cost::*` HAVE NOT
MOVED.** Both measurements now exist on the object, and both say there is
nothing to buy — so retiring `cost::{steps,sharing,families}` is now cleanup
with no lever behind it, not a prerequisite for anything. Its PLACEMENT
half is already answered and the answer is **real**: the object reports the same
count of steps deeper than PLACEMENT requires that `cost::placement` gets from
text. **Two independent implementations agreeing is what rules out the instrument
artifact that earlier levers turned out to be.**

**Gate: MEASURED, and the answer is negligible.** `Derivation::congruence`, exact
congruence per proof block over every interior node
(`the_frame_restricted_congruence_quotient_measured`):

| policy | removable |
|---|---|
| no frame constraint | the gross bound |
| members pinned to ONE frame | negligible |
| members hoisted to their LCA, PLACEMENT permitting | **negligible — this is the answer** |

> **⚠ IN-PROOF CSE IS WORTH NOTHING *UNDER THE EMITTED SCOPE TREE*, BECAUSE IT
> IS ALREADY DONE.** `class::Script::step` memoises on `Rule::rhs(ops)`, looks
> the key up across the WHOLE open frame stack, and stores it at
> `earliest(&key)` — the hoist-to-the-shallowest-legal-frame policy, already
> implemented. What a *recursive* congruence finds beyond that syntactic one is a
> rounding error. **Do not build in-proof CSE. It exists.**

> **⚠ THAT NEGLIGIBLE FIGURE DOES NOT CLOSE GRAPH OPTIMISATION, AND AN EARLIER
> DRAFT OF THIS SECTION READ AS THOUGH IT DID.** Every measurement above holds the scope tree
> FIXED. It is proved, under that assumption, that moving non-opener lines gains
> nothing: a shared input is already outside the deepest common enclosing scope
> (the language's visibility rule forces it), and the only remaining blocker is
> an eigenvariable, which a move cannot reach.
>
> **SCOPE FUSION BREAKS THE ASSUMPTION AND IS UNEXPLORED.** Two sibling `fix u`
> derived separately can be merged into one, deriving `∀u. P(u) ∧ Q(u)` and
> discharging per use with `forall_elim` + `and_elim_{l,r}`. The two `u` then
> ARE one variable, and everything the bodies share collapses. This is the whole
> reason the sibling-binder case blocks, so it is the transformation aimed at it.
>
> Gross bound is the no-frame-constraint row — folds available if scope were no
> constraint at all. Fusion cannot reach all of it: it applies only to siblings
> over the same binder, and each fusion pays an `and_intro` inside plus
> `forall_elim`/`and_elim` at every discharge site, so `net = saved − overhead` is
> the §15.6 shape again and is plausibly NEGATIVE for small scopes. ~~Nobody has
> measured it.~~ — **MEASURED at §16 O1: net NEGATIVE, and CLOSED.** The reason is
> **not the price, it is the supply**: barely any fusable group exists in the whole
> artifact. **⚠ DO NOT QUOTE THAT BOUND AS A LEVER** — it is a ceiling, and this
> document has been wrong about ceilings repeatedly.

**BOTH STATED BRACKETS WERE WRONG, and this section stated them.** The answer is
*below* the claimed floor, because `placement.foldable` never required the fold to
be LEGAL — it is not a lower bound, it is an incomparable measure. And `sharing`'s
figures inflate three separate ways, each measured:

- `sharing(Shape)` strips digits from leaf tokens, so it counts what a parametric
  *lemma* could abstract. That is E's question, not C's.
- `sharing(Exact)` quotients `assume` OPENERS. §15.1 forbids it: two sibling
  `assume φ` are two different hypotheses, and this is the largest of the three.
- `sharing` runs across `proof <name>:` boundaries on one label map, and labels
  repeat per block (`_h1` in every one), so operands resolve into the WRONG block.
  **That is a bug in the instrument, not a property of the artifact** — per-block
  it reports a smaller figure.

So this is the SIXTH time an instrument overstated its own lever, and the first
where the plan's own floor was the thing that was wrong.

**D — the claim graph. ✓ LANDED.** `gate::claims`. `cites` is lifted to per-claim
by splitting a unit's proof at its `proof <name>:` boundaries, and the emission
order is checked to be a TOPOLOGICAL SORT of the resulting graph. Acyclicity is
then a corollary and so is `constant::g3`, which is DELETED rather than kept
beside it. **Gate met:** the order over `base/` + `replace_stack` + the walk is a
topological sort (`the_emission_order_is_a_topological_sort_of_the_claim_graph`),
and a circular pair, a within-unit forward citation, a cross-unit forward
citation and a proof of an undeclared name are each required-to-reject.

> **⚠ THE GAP THIS SECTION CLAIMED IS NOT THE GAP, AND THE REAL ONE IS NARROWER.**
> It said nothing would catch `prepend_raw3` citing `prepend_block3` inside
> `base/tiers/seeds`. **The kernel catches exactly that**: it runs a unit's proofs
> in FILE ORDER, so a forward citation dies at lowering with `use('…'): unknown
> axiom/theorem in ctx` — which is also §15.7's open question, answered.
> What the kernel is blind to is the case `g3` was written for: a DEP's proofs run
> BEFORE the main unit's whatever order was intended, so `early` citing `late`
> checks green — exit 0, empty stderr — with `late` handed over as a dep. That one
> case is what makes this gate load-bearing; do not retire it on the strength of
> the kernel catching the other three.

**E — library learning. ◐ MEASURED by §16's O2, NOT BUILT.** `gate::learn` is
the census; §16's "O2's answer" owns the numbers and the four corrections to
what this section says below. Anti-unification over the DAG, ranked by the §15.6
cost model, filtered by citability. **Gate:** one lemma extracted by hand from
the top family, proved, checked, and measured on one unit BEFORE any pipeline
exists. If `net ≤ 0` there, E does not pay and that is worth one lemma to learn.

### 15.6 The mathematics E rests on, and what bounds it

Given instances `D₁,…,Dₙ` with least general generalization `P`, so `Dᵢ = θᵢ(P)`:
because rules are functions, `P` with its abstracted leaves turned into
hypotheses is *already a derivation* of `⋀ⱼ hyp(ℓⱼ) → concl(P)`.

**The learned lemma arrives with its proof.** No search, no admission. R2 falls
out: abstracting a formula position into a schema variable yields a derivation
that never inspected it, which is exactly R2's criterion for a legitimate
schema. Construction-based library learning cannot produce an R2 violation.

*One rigidity rule.* `use X` leaves are **RIGID** — a cited concrete theorem
cannot be generalized. `assume φ` and `schema_inst L { A: φ }` positions are
abstractable. Anti-unifying through a `use` is the one way to get an unsound
proposal, and it is the thing to assert against.

*Cost model.* For a pattern of size `s`, `p` parameters, `n` occurrences, with
instantiation costing ~`2p` steps (one `forall_elim` + one `implies_elim` per
guarded binder):

```
  net = n·(s − 2p) − s        so only s ≫ 2p pays
```

*Two bounds.* E is **not** capped by C's in-proof ceiling — a learned lemma is
stated at top level, absorbing the scope-depth difference into quantified
parameters, which is exactly what in-place folding cannot do. Against that, an
instrument reported several times as many families as building actually gave.

*The regression suite already exists.* `sing_rel` and `upair_rel` ARE learned
lemmas, found by hand, each worth a double-digit percentage of total lines. **A miner that does
not rediscover them is not working — and one that ranks the THIRD `upair`
highly is worse:** its instances anti-unify perfectly and it is uncitable, its
slots running `(2,3,1)` (R5). Nothing in the SHAPE says so; it is in the
placement structure. That is the argument for A–C preceding E.

### 15.7 Unverified

- Memory and time of holding the DAG for the worst unit are unmeasured, as is the
  whole-artifact figure.
- ~~Whether the kernel rejects a forward citation WITHIN one def/proof pair.~~ —
  **MEASURED, and it REJECTS** (D). So a cycle inside one pair never reaches the
  gate, and the gate's live case is the cross-unit one instead.
- `parse` is a SECOND reader of the proof language and now permanent. A rule the
  emitter gains but it does not learn shows up as a round-trip failure rather
  than as anything about the new rule.
- ~~The congruence-under-frames figure of Phase C.~~ — **MEASURED**, and it kills
  in-proof CSE rather than sizing it. E is now the ONLY size lever left, and its
  own bound — instrumented families far exceeding built ones — is the same kind of
  figure that has been wrong repeatedly.

---

## 16. The optimiser, phased

> **⚠ THE INSTRUMENTS ARE DELETED AND NOTHING IN `src/` REPRODUCES THEM.**
> `Derivation::{congruence,fusable,fusion,apply,identity}`, `Frames`, and
> `gate::learn` were measurement scaffolding for O1–O3 and were removed once they
> had answered. Resurrect any of them from **`a97f2300`** — that commit carries all
> three phases, their required-to-reject tests, and the figures they produced.
> Every test name cited in this section lives there and NOT at HEAD; do not read a
> missing test as a regression.
>
> **VERIFIED AT HEAD, 2026-08-19:** `fusable`, `fusion`, `Frames`, `gate::learn`
> and `identity` have **zero** occurrences in `src/`. There is NO optimiser code
> to isolate — nothing to move to a folder of its own, and an empty one would be
> a lie about the state. The nearest live thing is `gate::cost`, a size
> INSTRUMENT (§5's open question) that `class/tests.rs` still calls; it is not a
> pass. **The surviving contract is `derivation::Derivation`, and it is now
> marked FROZEN in the file itself** so a future session cannot reshape it and
> silently void every number below.


> **⚠ EVERY CLOSURE BELOW WAS MEASURED ON A CORPUS THAT IS NOT THE PRODUCT, AND
> THREE OF THE FOUR DEPEND ON THAT CORPUS.** The artifact measured is
> `constant::walk`'s output: a fraction of the 197 constants, overwhelmingly
> `_class` units, and **ZERO theorem proofs** — §14's E and LOWER do not exist, so
> the Isabelle proofs the project exists to emit are not in it. Stratum A alone
> owes the `set(t)` discharges that are exactly the regular structure library
> learning consumes, and none of it was weighed.
>
> **The bias has a direction, and it is downward.** A learned lemma costs `s` ONCE
> and is recovered `n` times: `net = n·(deletable − 1 − p) − (s + 1)`. The artifact
> grows roughly linearly in constants while the saving grows in `n`, so a
> percentage taken at today's coverage **understates** the percentage at R6's
> ceiling.
>
> What survives the corpus: hoisting-is-worth-≈0 is a STRUCTURAL proof (§15.5 C's
> second ⚠), not a count; and `compose_class` being kernel-accepted confirms
> §15.6's mechanism wherever it is applied. What does NOT survive: scope fusion's
> negative net and library learning's percentage are facts about THIS corpus, and
> in-proof CSE's saturation is a fact about `class::Script`'s memo — LOWER need
> not use `Script` at all.
>
> **So "the optimiser is measured out" is FALSE and this section said it.** The
> true statement is: *nothing pays on the artifact as it stands today.* Re-run
> every O-phase after E and LOWER exist. This is the SEVENTH time this document
> has quoted a lever from the wrong object, and the first where the rule against
> it was quoted in the same section.


**WHAT "FINISHED" MEANS HERE, because an open-ended set cannot be finished.**
The optimiser is a set of CANDIDATE transformations. It is done when every
candidate is either **BUILT** with a measured saving, or **CLOSED** with a
measured reason. A candidate left unmeasured is the only failure state.

**Why it is worth doing before the rest of P4.** The artifact costs thousands of
lines per constant, and R6's ceiling is 195, so a per-line lever compounds with
coverage and applying one late means paying to re-derive it. `every_refusal_carries
_a_verdict` prints the current line total and the worst unit.

**Why that argument does not license building on faith.** Scope fusion measured
NEGATIVE (O1), in-proof CSE measured saturated, and this document has been wrong
about size ceilings repeatedly. Each phase below therefore gates on a MEASUREMENT
first, and each may end at CLOSED-worth-nothing — which is a FINISHED phase, not a
failed one.

**ALREADY DECIDED — not phases, and not to be re-opened without a new number.**

| candidate | verdict |
|---|---|
| hoist every step to PLACEMENT | ✅ **CLOSED, worth ≈0.** A small fraction of steps sit deeper than needed, but hoisting MOVES lines rather than deleting them, and its only indirect gain — enabling folds — is already bounded by in-proof CSE below. Proof in §15.5 C's second ⚠ |
| in-proof CSE | ✅ **CLOSED — ALREADY BUILT and saturated.** `Script::step` memoises on `Rule::rhs(ops)` across the whole open frame stack; the residual is negligible, `the_frame_restricted_congruence_quotient_measured` |

### The phases, IN EXECUTION ORDER

**The two measurements come first, and neither needs a pass.** That is not a
scheduling preference — a measurement can CLOSE its candidate, and O3 exists only
to serve a candidate that survived.

| | step | gate — the thing that can fail | status |
|---|---|---|---|
| **O1** | **measure scope fusion** — rewrites nothing | | ✅ **DONE — net NEGATIVE, CLOSED** |
| O1.1 | find the fusable groups | sibling frames under ONE parent opened by the SAME binder. **Required-to-reject:** 0 on a proof with no sibling binders | ✅ `Derivation::fusable` |
| O1.2 | count what fusing unlocks | a FOURTH policy beside `Ignore`/`Share`/`Hoist`: fused siblings count as one frame. `fuse − hoist` is the gain | ✅ `Frames::Fuse` |
| O1.3 | price it | per group one `and_intro` inside, plus `forall_elim` + `and_elim` per discharge site: `net = unlocked − (groups + 2·sites)` | ✅ `Derivation::fusion` |
| O1.4 | verdict | `net > 0` feeds O4; `net ≤ 0` CLOSES the candidate, which is a FINISHED phase | ✅ **CLOSED** |
| **O2** | **measure library learning** — rewrites nothing | | ✅ **MEASURED — a low single-digit percentage** |
| O2.1 | family census over the DAG | `gate::learn`, ranked by `n·(s − 2p) − s`; `use X` rigid | ✅ |
| O2.2 | citability filter | `Cite::{Theorem,Schema,Unstatable}`. The filter that bites is STATABILITY, not permutation — see below | ✅ |
| O2.3 | one lemma BY HAND | `compose_class [F(3), G(2)]`, kernel-accepted | ✅ |
| **O3** | **a pass can exist**: `Derivation -> Derivation` | | ✅ **DONE — the boundary only; see its limit below** |
| O3.1 | the type and an identity pass | identity reproduces the artifact BYTE-FOR-BYTE | ✅ `the_identity_pass_reproduces_the_artifact_byte_for_byte` |
| O3.2 | legality after every pass | every output satisfies `legal()`; **required-to-reject:** a pass lifting a node above its operand fails BEFORE emission | ✅ `a_pass_that_lifts_a_node_above_its_operand_fails_before_emission` |
| O3.3 | the kernel re-accepts | whole artifact, exit 0 AND empty stderr AND clean buckets | ✅ |
| **O4** | **build scope fusion** | needs O1.4 `net > 0` and O3. Artifact shrinks by the predicted amount, kernel accepts, worst unit does not grow | ✅ **CLOSED by O1.4** — never to be built |
| **O5** | **build library learning** | needs O2.3 `net > 0` and O3. The reachable net is small; the much larger figure behind it needs formulas on interior nodes — a §15.2 reversal, not a pass | ⚠ **the reachable net is the whole prize** |

### O2's answer, and the four places §15.6 was wrong

**Library learning is worth a low single-digit percentage of the artifact.** That
is the greedy, non-overlapping total over every family for which a lemma can be
STATED, priced at `n·(deletable − 1 − p) − (s+1)`: `s` is what the lemma costs to
prove once, `deletable` is what an occurrence can really delete (the rest of `s`
has consumers outside it), and the site pays one citation line plus one
`forall_elim`/`implies_elim` per parameter. Under §15.1 read literally — never let
an opener into a pattern — it is an order of magnitude smaller again. Reproduce
with `gate::learn::tests::o2_1_the_family_census_over_the_artifact`, at `a97f2300`.

**O2.3 is done and the kernel took it.** The largest statable family is
`ZF_Base_2eUn_class` against `List_2elist_2eCons_class`: the SAME class
construction of `∃v. F(a,b,v) ∧ G(v,r)`, differing only in which two constants
fill `F` and `G`. Abstracting exactly those two gives
`schema compose_class [F(3), G(2)]`, and §15.6's central claim holds empirically —
**the body checks unchanged**, exit 0 and empty stderr, no search and no
admission. **⚠ ONE LEMMA IS ABOUT HALF OF EVERYTHING LIBRARY LEARNING HAS TO
OFFER**, and the tail is small families: the distribution, not the total, is what
makes O5 a poor bet.

**1. The regression suite cannot be run against the artifact, and §15.6 does not
say so.** `sing_rel` and `upair_rel` are already factored out: the artifact CITES
each and contains neither body. A miner over it cannot rediscover them, and
reading the miner's silence as failure would be wrong. Run against INLINED copies
it recovers nearly all of both, as `Cite::Theorem` families with positive net.

**2. Ranking by `n·(s − 2p) − s` does not find the known answer even then.** On
the inlined corpus the top-ranked family is a FRAGMENT of `sing_rel`, not
`sing_rel`: the fragment occurs twice per copy, so `n` doubles and beats the whole
body. The lemma is second. **Ranking is not selection.**

**3. The third `upair` is not a Derivation-level phenomenon, and O2.2 asked the
wrong instrument for it.** §15.6 is right that nothing in the SHAPE says so —
but nothing in the OBJECT does either. The refusal lives in
`class::read`, where `upair_slots` returns `None` for a permuted triple so the
seed is never taken and the site is unfolded; the obstruction is that a
class-existence seed must land on ascending contiguous COORDINATES of the
ambient tuple. A derivation-level lemma is `hyps → concl` cited with
`implies_elim` and has no coordinate to permute, so it has no analogue of that
failure. What plays the same role on this object is **statability**, and it is
just as brutal: a family can anti-unify perfectly and still be uncitable.

**4. `net = n·(s − 2p) − s` overstates, and the gap is where the difference went.**
Every family the census can SEE is worth many times the statable total — but the
overwhelming majority of those need a hypothesis that is a DERIVED node. §15.2
puts no formula on an interior node, deliberately, so nothing holding only a
`Derivation` can write the `schema_inst` that would instantiate such a lemma.
**O5 as scoped is blocked on a §15.2 decision, not on effort**: reaching past the
statable total means putting formulas back on interior nodes and re-opening the
soundness argument §15.5 settled. **⚠ THE SEEABLE TOTAL IS A CEILING, NEVER A
LEVER** — this document has been wrong about ceilings repeatedly.

*One caveat that is not measured.* For a statable family `bytes` compares the
deleted line text against the text the instantiation must write, and every
statable family in the top ten is positive. For an unstatable one the cost side
is unknown BY CONSTRUCTION: the formulas the `schema_inst` would name are not in
the object. A fold that turns 40 short lines into one `schema_inst` naming 40
large formulas can shorten the proof in lines and lengthen it in bytes.

> **⚠ WHY A MEASUREMENT PRECEDES THE INFRASTRUCTURE, since the numbering has been
> asked about.** O1 and O2 rewrite NOTHING — O1 is the existing read-only walk
> under a different equivalence on frames, exactly as `share` and `hoist` already
> differ. O3 is real machinery with no customer until one of them returns a
> positive net, and no lever measured so far has returned one worth having.
> Building O3 first is affordable and self-contained; it is simply not yet known
> to be needed.

**O1's ceiling, and it is a ceiling not a forecast.** The no-frame-constraint row
counts the folds available if scope were no constraint at all. Fusion reaches only
same-binder siblings, so expect well under it. **Do not quote that ceiling as a
saving.**

**O1 MEASURED, and scope fusion is worth LESS THAN NOTHING**
(`the_scope_fusion_measurement`). The priced quantities are: fusable groups,
discharge sites, folds unlocked (`hoist − fuse`), and overhead
(`groups + 2·sites`); the net came out negative.

The ceiling was never the binding constraint: **the artifact almost never emits
two sibling scopes over one binder.** A handful of groups across the whole
artifact, all `fix`/`forall_intro`, in three proof blocks (`Sum_2ePart_bridge`,
`Sum_2ePart_class`, `ZF_Base_2eSigma__C1_nested` ×2). Even at zero cost fusion
would delete almost nothing. Two corrections this section owed:

- **The per-group `and_intro` price is wrong for a group of 3** — a group of `k`
  members needs `k−1` of them, so the overhead formula understates by one per
  oversized group. It changes no verdict here, and it would matter to any future
  re-measurement.
- **The cascade — fusing an outer pair makes its inner binders siblings — was
  never mentioned and does not arise:** every child frame of a fused member
  binds nothing, so there is no second round to run.


---

## 17. E and LOWER, designed

§14 is the specification and is frozen. This section is the *implementation*
design against it, and unlike §14 it is meant to be edited as the passes land.

### The finding that forces the shape

Compiler A renders `ZF.pair/3442` (`Pair_iff`) as the **∃-form**:

```
∀a.set(a)→∀b.set(b)→∀c.set(c)→∀d.set(d)→
  ( (∃v₁. set(v₁) ∧ kpair(c,d,v₁) ∧ (∃v₀. set(v₀) ∧ kpair(a,b,v₀) ∧ eq(v₀,v₁)))
    ↔ (eq(a,c) ∧ eq(b,d)) )
```

`docs/phase2_probes/zf_pair_e2e.fol.def:55` carries the **∀-form** — witnesses as
extra guarded binders, constraints as hypotheses — and its own comment at `:44`
calls that "the S1 rendering". The two are not syntactically equal, and the
materialisation sits in POSITIVE position on the left of that `↔`, so they are
interchangeable only through `kpair`'s UNIQ.

> **⚠ THE ∀-FORM IS FORCED, NOT PREFERRED.** §14 gives LOWER **no provider
> calls**. Under the ∃-form every citation of a theorem needs UNIQ to align
> witnesses, which is a provider call, so the ∃-form makes §14's pipeline
> unimplementable as written. Under the ∀-form a citation is `forall_elim` +
> `implies_elim` and nothing else — which is exactly `zf_pair_e2e.fol.proof`
> `:1140-1153`.

Two more, both measured the same way:

| | |
|---|---|
| `constant::env()` is built from `PRIMITIVES` alone — **5** constants | `Pair` is absent, so Compiler A refuses every ZF theorem statement with `CompoundTerm` until the env is fed from `constant::walk` |
| `from_meta_tests.rs` contains **zero** `render` calls | the two halves of Compiler A's input path have never been composed |
| `ZF.pair/3448` has **no tag-`7` node** (`PAxm`) | **E is the identity on the target proof.** LOWER can be built and validated first |

### Free-variable sorts are READ from the export's own type env

`from_meta::prop` needs a `SortEnv` for the statement's free variables. The
`Free` nodes in the PROPOSITION carry no type child and `export::lower::obj`'s
`"1"` arm keeps only the name — but the export states the types in a **section of
its own**, which `proof_term::type_env` already reads and `export::read` already
puts on `Entry::env`. Measured: `ZF.pair/3450` and `/3442` both give
`a,b,c,d ↦ Ok(I)` through `lower::sort`.

> **⚠ AN EARLIER VERSION OF THIS SUBSECTION SAID THE SORTS MUST BE INFERRED BY A
> TYPING PASS OVER `Obj::Const`. THAT WAS WRONG** — it was written from the
> proposition alone, without reading `export/mod.rs:17` or the doc comment at
> `proof_term.rs:126`, which states the fact outright: *"They are not in the
> proposition — it uses `Free` nodes — so a statement cannot be given sorts
> without this."* The data was already there and already parsed. Inference is not
> merely unnecessary, it would be a SECOND source of truth for something the
> export states, and the two could disagree silently.

So P6b is a bridge, not an inference engine: `Entry::env` → `lower::sort` →
`from_meta::SortEnv`, with a refusal when a free variable of the statement has no
entry or its type does not lower.

> **⚠ `convert.rs` LOOKS LIKE IT SOLVES THIS AND DOES NOT.** `ConvertCtx::
> free_var_types` is declared, initialised empty, read at `convert.rs:130,287`
> and **written nowhere**, so `classify_type` yields `Unknown` and the tag is
> then defaulted by position — term in `value`, schema parameter in `prop`.
> `from_meta`'s refusal ("the environment decides, never a default") is the
> correct behaviour and `convert.rs` is the one that is wrong. The fix is to feed
> it the same `type_env`, not to add a defaulting rule.

### IR4 is IR3's type, plus one variant

The tree's own rule is that a new IR type appears only when the SHAPE changes:
IR2 is IR1's type with an invariant decided by `meta::Proof::redex`, and IR3 is
new only because it gained `Mat`. E adds no node former; it removes `Prop::Eq`
and the seven equational `Axiom`s. So

```
  IR4 = ir::elim::Proof + Cite(String),  invariant decided by eq_residue()
  E : elim::Proof -> elim::Proof         exactly as H : meta::Proof -> meta::Proof
```

`Cite` is required because E replaces `Ax(Reflexive)` with a citation of a
foundation lemma BY NAME, and `Thm(ThmId)` only indexes Isabelle theorems.

### E — equational elimination

Consumes IR3, produces IR4. Calls `cong`, and nothing else.

| source | at `o` / `prop` | at `i` | at function sort |
|---|---|---|---|
| `Ax(Reflexive)` | `Cite(iff_refl)` | `Cite(eq_refl)` | `c == c` at a fixed constant → that constant's CONG; 43,042 uses are almost all this |
| `Ax(Symmetric)` | `Cite(iff_symm)` ⚠ | `Cite(eq_symm)` | ↑ |
| `Ax(Transitive)` | `Cite(iff_trans)` ⚠ | `Cite(eq_trans)` | ↑ |
| `Ax(EqualIntr)` | `Cite(iff_both)` — a schema, NOT the kernel rule | — | — |
| `Ax(EqualElim)` | `Cite(iff_mp)` — a schema, NOT the kernel rule | — | — |
| `Ax(Combination)` | the connective family: `cong_{not,and,or,imp,iff,exists,forall}` | **`cong(head)`** — E's ONLY provider call | — |
| `Ax(AbstractRule)` | at `i⇒o`: `∀z.(set(z) → (φ ↔ ψ))`, which is `cong_forall`'s own antecedent — no class. 1,091 of 1,381 | — | otherwise S5: refuse, S has already run |
| `Ax(Def(n))` | unfold the constant's `@def` | ↑ | ↑ |
| `Prop::Eq(l,r,O\|Prop)` | becomes `Iff` | — | — |
| `Prop::Eq(l,r,I)` | — | relational `eq(l,r)` | — |

> **⚠ FOUR SCHEMAS THE `o` COLUMN NEEDS DID NOT EXIST IN `base/`.** `iff_refl`
> was there (in `tiers/cong`); `iff_symm`, `iff_trans`, and — for `equal_elim` /
> `equal_intr` — `iff_mp` and `iff_both` were not. All four are now PROVED into
> `base/tiers/logic`, never declared. **⚠ EACH PAIR OF NEW BASE DECLARATIONS MOVES
> THE THREE CENSUS PINS**, whose current totals live in the tests, not here.

> **⚠ `equal_elim` AND `equal_intr` ARE KERNEL RULES ON THE ISABELLE SIDE AND IR4
> HAS NO NODE FOR APPLYING ONE.** Rather than add a node former, E cites them as
> the schemas `iff_mp : (A↔B)→(A→B)` and `iff_both : (A→B)→((B→A)→(A↔B))`, and
> the source proof's own `ImpE`s are left untouched. This keeps E a pure
> head-replacement, which is why it needs no new spine variant beyond `Cite`.

> **⚠ THE `i` ARM IS REACHABLE ONLY THROUGH A `SortEnv`, AND E's FIRST DRAFT HAD
> NO ACCESS TO ONE.** After S every `i`-object is a VARIABLE, and a variable
> carries no sort — so `elim::sort_of` can never settle `Reflexive` at `i`, and E
> refused every such site. E therefore takes the statement's `SortEnv`, exactly
> as `from_meta` does, and `sort_of` now only ever settles the non-`i` arms. The
> corpus census still runs on an EMPTY env, so it does not exercise this.

> **⚠ `eq_refl`/`eq_symm`/`eq_trans` ARE DECLARED IN `base/axioms`, WHICH
> `base::TIERS` DOES NOT LIST.** A registry built from `TIERS` alone resolves
> none of them and E's output is unlowerable. Use `base::chain()`, which is
> `axioms` + the tiers. Caught by `every_name_pass_e_can_cite_is_declared_in_base`
> on its first run — that test exists because nothing else would have.

> **⚠ E's LEVER IS SMALL AND EACH ARM REVEALS THE NEXT.** Landing
> `equal_elim`/`equal_intr` cleared their refusals but moved barely any proofs,
> because `combination` sits underneath them and surfaced as fresh refusals in
> almost the same number. The remaining obstructions, in descending order:
> `Reflexive` at a function sort, `combination`, a `==` hypothesis, `Transitive`
> at a function sort, an undetermined sort. `combination` is the CONG citation —
> E's only provider call — and it is the gate on the largest block.

### LOWER — homomorphism plus R3 guards

Consumes IR4, produces `ir::nd::Proof`. No provider calls.
`zf_pair_e2e.fol.proof:1123-1174` is the specification by example.

| IR4 | emitted |
|---|---|
| `AllI(x, I, p)` | **open** `fix x`, `assume set(x)` · **close** `implies_intro` discharging the guard, then `forall_intro` |
| `ImpI(A, p)` | **open** `assume ⟦A⟧` · **close** `implies_intro` |
| `Hyp(i)` | the handle of the i-th enclosing `assume` — de Bruijn resolved to a handle |
| `ImpE(p,q)` | `implies_elim ⟨p⟩, ⟨q⟩` |
| `AllE(p,t)` | `forall_elim ⟨p⟩, t` **then** `implies_elim` against `set(t)` — stratum A's dominant |
| `Mat{var,constant,cite,args}` | **two arms — see the ⚠ below.** Statement-level: `fix` + `assume` the constraint, `cite` UNUSED. Proof-internal: `forall_elim`×n on `cite` with guards, then `exists_elim` opening `var` |
| `Thm(id)` | `use n` **or** `schema_inst n {…}`, from the citation's `ForallForm` |
| `Cite(n)` | resolved against `base/` via `decl::DeclEnv`; a base lemma has NO `ForallForm`, so its shape is read off the FORMULA and a guard discharges only for the term just supplied |

**The dispatch is a property of the CITED THEOREM, not of the argument.** This is
§11.2's `ZAppt` term-vs-proposition problem and §10 P3 records it UNBUILT. The
probe shows both arms — `use Pair_iff` against
`schema_inst iffD1 { P: …, Q: … }`. The rule: if the citation's rendering
returned non-empty `schema_params`, it is `schema_inst` and the trailing `AllE`s
become BINDINGS; otherwise `use`, and they become `forall_elim`. `Cite` needs the
identical test — `iff_refl` is a schema, `eq_refl` is a claim — so this is ONE
mechanism used twice, resolvable from `decl::DeclEnv`.

**The arity mismatch, and the map that fixes it.** The source applies `Pair_iff`
to FOUR arguments; the rendered claim binds SIX. The extra two are the S1
witnesses. LOWER therefore needs, per cited theorem, the map *which ∀-slot is a
source binder and which is an S1 witness*, and fills the witness slots from the
caller's own materialisations. That map is the Compiler A ↔ LOWER interface, and
P6c built it: `forall_form::{Slot, Witness, ForallForm, Materialised}`, one
`Vec<Slot>` positionally parallel to the ∀ prefix, with `Witness::args` indices
into that vector rather than names — names are gone once LOWER substitutes the
caller's terms. `ForallForm::instantiate` is the operation, and is what refuses.

> **⚠ `Mat::cite` IS THE EX-LEMMA NAME, NOT THE CONSTANT — AND STRIPPING `_EX` IS
> NOT ITS INVERSE.** `theorem/elim.rs` builds `cite` as
> `rel_name(sanitize_name(c)) + "_EX"`, and `rel_name` renames the five
> primitives: `ZF_Base.Pow` gives `Pow_EX`, whose strip is `Pow`, not
> `ZF_Base_2ePow`. Right for every constant EXCEPT the five primitives, and
> silently wrong for those.
> `ir::elim::Mat` therefore carries an explicit `constant` field, in the same
> alphabet as `Witness::constant` (the sanitized Isabelle name), and IR3 retains
> no `Obj` from which LOWER could re-derive it. Pinned by
> `a_primitives_constant_is_not_recoverable_by_stripping_ex_from_cite`.

> **⚠ A `Mat` FOR A TERM IN THE THEOREM'S OWN STATEMENT MUST NOT BE LOWERED WITH
> `exists_elim`, AND AN EARLIER VERSION OF THE ROW ABOVE SAID IT SHOULD.** IR3 for
> `ZF.pair/3448` is
>
> ```
> Mat _s0 = ZF_Base_2ePair(a,b)     Mat _s1 = ZF_Base_2ePair(c,d)
>   ImpI [eq(_s0,_s1)] …
> ```
>
> — both witnesses hoisted outside the `ImpI`, because S places a materialisation
> at the scope binding its free variables and `a`..`d` are free throughout. But
> `exists_elim` makes `_s0` an EIGENVARIABLE, and the hypothesis it must then
> discharge, `eq(_s0,_s1) → eq(a,c)`, MENTIONS that eigenvariable. The side
> condition fails and no amount of reordering saves it.
>
> The ∀-form is what resolves this, and this is the second argument for it: the
> witnesses of statement-level terms are **∀-bound by the claim** with their
> constraints as hypotheses, so LOWER emits `fix _s0` and
> `assume kpair(a,b,_s0)` and **never cites `Pair_EX` at all**. The probe confirms
> it — `proof Pair_inject1` cites `Pair_iff`, `iffD1`, `conjunct1` and no EX lemma.
>
> **How LOWER tells the two apart:** run `ForallForm::instantiate` against the
> GOAL, not only against citations. A `Mat` whose `(constant, args)` matches a
> `Witness` slot of the goal is statement-level; any other `Mat` is proof-internal
> and takes the `exists_elim` arm. One map, both directions.

### What must change outside E and LOWER

1. ~~**A ∀-form S1 entry point in `statement/`**~~ — **landed** as
   `statement::forall_form`, a sibling of `render_in`; the byte-identity pins on
   the ∃-form path all still hold.
2. ~~**`ConstEnv` fed from `constant::walk`**~~ — **done on the census path**
   (`lower_tests::corpus::walk_cenv`), and measured: EVERY walked constant reaches
   the env. It is NOT what P6d needs next, and family C is the reason — those goals
   refuse at a constant `ConstEnv` lacks, and **not one of them is a walked
   constant**. Feeding the env harder cannot move them; only P4 emitting the
   constants can. Unit tests that render a real ZF statement still extend a copy by
   hand. **§18 lowers that bar rather than removing it:** `walk_cenv` reads
   `w.constants`, never `w.graphs`, so a constant needs only L1 — EX/UNIQ, no
   graph — to reach the env and unblock the goals that name it.
3. ~~**The sort-inference pass**~~ — **landed** as `statement::sorts::bridge`, and
   it is a bridge, not inference: the export states the types.

4. **Arity-n schema instantiation in LOWER** — `theorem/lower.rs:210` refuses any
   schema parameter of arity > 0, and P6d's refusal table records the reason it was
   never needed: `conjunct1` and `iffD1` are both arity 0. Every induction
   principle in the corpus is arity ≥ 1, so this is ORDINARY P6 COVERAGE and the
   largest single class of it. **UNBUILT.**

   **⚠ IT IS NOT A §18 REQUIREMENT, THOUGH §18's FIRST INSTANCE NEEDS IT.** `nat`'s
   characterisation runs through `nat_induct` at `P(x) := x ∈ s`, arity 1 — so
   `nat` cannot complete without this. §18's architecture is independent of it: a
   constant characterised without a schema would land regardless. Do not file this
   under the stratification, and do not let the stratification's status depend on
   it.

### The phases

All five deliver §10's **P6**, so they are numbered under it. The names are
load-bearing: each appears in its own test names and in the commit that lands it,
which is what makes a phase traceable rather than merely listed.

**STATUS IS PART OF THE TABLE AND EVERY CELL CARRIES A HANDLE** — §10's rule
applies here. A status with no way to check it is not a status. If a row disagrees
with the code, the code wins and the row is stale.

| | needs | build | criterion — the thing that can fail | required to REJECT | status · handle |
|---|---|---|---|---|---|
| **P6a** | — | `iff_symm`, `iff_trans` proved into `base/tiers/logic` | both kernel-accepted with **empty stderr**; `base_names()` contains both; `gate::admission` still green — they are R1 admissions and must be PROVED, never declared | a declared-but-unproved `iff_symm` must fail `gate::admission` | ✅ **DONE** · `base::tests::iff_symmetry_and_transitivity_are_proved_not_admitted`; reject case `an_admitted_iff_symm_is_rejected` |
| **P6b** | — | the `SortEnv` bridge: `Entry::env` → `lower::sort` → `from_meta::SortEnv` | every `ZF.pair` statement either bridges AND renders, or refuses BY NAME — **every outcome pinned, so nothing is silently dropped** | a statement with a free variable missing from `type_env` must refuse, not default to `Sort::I` | ✅ **DONE** · `statement::sorts::tests::corpus::every_zf_pair_statement_bridges_and_renders_or_refuses_by_name` |
| **P6c** | — | the ∀-form S1 entry in `statement/`, and the witness-slot map | reproduces the probe's `Pair_iff` and `Pair_inject1` **claims**, up to witness naming; **`render_in`'s own output is byte-unchanged** | a witness slot filled from the wrong `Mat` fails `instantiate`'s own test | ✅ **DONE** · `statement::forall_form` (12 tests); reject case `a_witness_slot_filled_from_the_wrong_materialisation_is_refused` |
| **P6d** | P6b, P6c | LOWER `elim::Proof -> nd::Proof`, `use`/`schema_inst` dispatch included | regenerates `Pair_inject1`'s **proof**; kernel accepts, empty stderr, clean buckets | an `AllE` whose `set(t)` is not dischargeable must refuse, not emit an unguarded citation | ✅ **DONE** · `theorem::lower` (6 tests) · `the_kernel_accepts_the_generated_pair_inject1`, guarded against vacuity by `the_kernel_test_is_not_vacuous` |
| **P6e** | P6a | E `elim::Proof -> elim::Proof`, plus `eq_residue` | identity on `ZF.pair/3448`; `eq_residue` empty over everything E accepts, and every refusal named — **measured 8,892 accepted of 9,231, of which only 18 are actually REWRITTEN; 339 refused** | a function-sorted `Reflexive`, and one whose sort the application does not fix, must both refuse rather than take the `eq_refl` arm | ◐ **PARTIAL** · `theorem::eq` (12 tests) · `every_pass_s_output_is_eliminated_or_refused_by_name` |

**P6d is P6's criterion, and it is MET.** `ZF.pair/3448` now goes in and a
kernel-accepted `Pair_inject1` comes out of `src/`, not by hand — the first time
§10's P6 row has had a machine-generated artifact behind it. What that does NOT
mean is that P6 is closed: §10's row asks for **both** e2e probes regenerated as
Units, and `zf_fst_conv_e2e` is untouched.

**What LOWER refuses, and these are the bounds of the increment.** Each is a
named `Refusal`, never a fallback:

| refused | why |
|---|---|
| a `Mat` the goal does not bind | proof-internal, owes the `exists_elim` arm — unbuilt |
| a nested (non-prefix) `Mat` | placement inside the spine is unbuilt |
| `Ax(_)` | that is PASS E, which does not exist (P6e) |
| `AllI` — a `Pure.all` binder inside a proof | 3448 has none; the statement's binders come from Compiler A's closure, not from IR3 |
| a schema parameter of arity > 0 | `conjunct1`/`iffD1` are both arity 0 |
| a citation argument S left compound | asserts IR3's invariant |
| an antecedent nothing in scope proves | the guard/constraint discharge is one mechanism and it must find its operand |

> **⚠ THE GUARD AND THE CONSTRAINT ARE ONE MECHANISM.** A cited claim's rendered
> statement carries `set(·)` per slot AND one constraint per witness — both
> inserted by the rendering, neither present in the source proof. LOWER discharges
> exactly `slots.len()` guards and `witnesses` constraints from the ambient scope,
> after which what remains is the source statement and the source proof's own
> `ImpE`s line up. Discharging "while the antecedent matches" would eat into the
> body; the counts come from the `ForallForm`, not from the formula.

> **⚠ A NEW `base/` DECLARATION MOVES THREE COUNT PINS, AND THE P6a ROW DID NOT
> SAY SO.** `decl_tests::base_round_trips_through_render`,
> `gate::tests::no_new_base_declaration_groups_its_guards` and
> `gate::claims_tests::a_node_is_a_claim_or_a_schema_and_never_an_axiom` each hold
> a hard-coded total. They exist to be updated, but they are not discoverable from
> the phase row — only by running the suite. Any later phase that touches `base/` pays this too.

> **⚠ THE `↔` EQUIVALENCE FAMILY IS SPLIT ACROSS TWO TIERS.** `iff_refl` is
> declared in `base/tiers/cong`, `iff_symm`/`iff_trans` in `base/tiers/logic`,
> because this section sent them there. Nothing breaks — `logic` precedes `cong`
> in `base::TIERS` and none of the three cites anything — but E's `o` column cites
> all three together, so a reader looking for the family will find two thirds of
> it. Moving them to `cong` is safe if it ever matters.

> **⚠ P6c MUST NOT TOUCH `render_in`.** `constant/` consumes its ∃-form output and
> `the_{diagonal,seed_tier}_is_what_compiler_b_regenerates` pins it byte-for-byte.
> The ∀-form is a SIBLING entry point. A "small refactor" of the shared path is how
> this phase silently moves 31 constant units.

> **⚠ BYTE-IDENTITY WITH THE PROBE IS NOT ACHIEVABLE AND MUST NOT BE THE TEST.**
> The generator names witnesses `_v0`/`_v1` where the hand-written probe says
> `p`/`q`.
>
> **DECIDED: the criterion is "the same claim up to a DECLARED witness renaming,
> kernel-accepted"** — not re-threading the probe. Re-threading would edit
> kernel-checked evidence to match generator output that is not yet trusted, which
> inverts which artifact is the authority. `constants_s2s3` was re-threaded only
> after its generator was already believed. The renaming is declared as data
> (`forall_form_tests::WITNESS_RENAMING`) and the test `include_str!`s the probe,
> so the **probe file itself is the pin** and moving it breaks the test.

### LOWER's reach, measured — and the bottleneck is NOT LOWER

`the_lower_reach_census` runs the whole pipeline over the export with a real
`ConstEnv` (the 5 primitives PLUS whatever P4 has emitted) and real `Facts`.
**The census accounts for every proof rather than leaking**, in six buckets that
sum to the whole export: **no proof term · refused by PASS S · GOAL never
renders · refused by PASS E at a goal that DID render · lowered · refused by
LOWER.**

**⚠ THE COUNTS ARE NOT REPRODUCED HERE, DELIBERATELY.** They move with every
phase, and a copy in prose is stale one commit later while still reading as
authoritative — which is what happened to this section. `the_lower_reach_census`
asserts every one of them; run it.

**The gate is P6c's ∀-form fragment, not LOWER's spine** — but note the ceiling S
sets above it: clearing the entire no-goal bucket cannot lift `lowered` past what
S admits, because S refuses before a goal is ever consulted.

**⚠ "THE GOAL DOES NOT RENDER" WAS ONE BUCKET HIDING FIVE STAGES AND FOUR GAPS,
AND NAMING `render_in` AS THE LEVER WAS A READING OF IT RATHER THAN A
MEASUREMENT.** `render_all` ran five stages behind `let Ok(..) else { continue }`
and discarded every `Refusal`. It now records the FIRST failing stage, pinned by
`both == 0` — a goal is rendered or blocked, never both, so a stage-N refusal
cannot be attributed to a later one. The five stages a goal can die at, in
order: `export::read` · `statement::sorts::bridge` · `export::lower::prop` ·
`from_meta::prop` · **`forall_form::render_in`**, which carries the
overwhelming majority.

The hypothesis survived — but the families underneath it do not have one owner,
and the census names each:

| | |
|---|---|
| **C** | constant absent from `ConstEnv` — **the largest, and it is P4's** |
| **F** | everything else, a `Pair` under a binder prominent among it |
| B | `Pure.eq` — the statement IS a definition |
| D | a class argument (S5) |
| **A** | a constant at PROPOSITION position — **the predicate gap is CLOSED** |
| E | a type variable — the generic FOL/IFOL layer |

**A IS CLOSED AND C IS NOW THE WHOLE STORY.** Family A had two parts: goals at
`Ex1`/`Ball`/`Bex`/`Subset`, closed by porting the ∃ path's table to the ∀-form;
and goals at **defined predicates**, closed by unfolding their `_def` between
`from_meta::prop` and `render_in`. S4 says a predicate carries no EX/UNIQ/CONG —
it denotes nothing — so the route is a definitional `P(x⃗) ↔ body`, which §10's G1
admits with content ZERO, and here it is not even declared: the body is
substituted in and nothing enters the signature. What remains sits at predicates
whose `_def` LHS is not an application of variables.

**A did not vanish so much as convert into C**, which GREW as a result: an
unfolded predicate body reaches term constants P4 has not emitted. C is not
reachable from the fragment at all, and the census proves that rather than
assuming it — every walked constant is in the env and **no** family-C head is
walked. The theorem side is now gated almost entirely on the constant table,
which is where it always had to end up.

What reaches LOWER and still refuses, **and an earlier version of this list read as
exhaustive while omitting `NoFactFor` entirely**: a proof-internal proposition
`open_in` will not render, a schema cited at the wrong arity (§17's arity-0
bound), the named `NotInThisIncrement` bounds, **proofs LOWER BUILT AND
`nd::Proof::new` REJECTED** — a bug in LOWER's own bookkeeping, not a bound, and
unexplained — and **`NoFactFor`, a citation whose own statement fell out of
`render_all`**. That last one is the same gap as the no-goal bucket, seen at a
citation instead of at a goal, so it moves with A/C rather than needing work of
its own. The census prints each by name.

> **⚠ `lowered` IS NOT `kernel-accepted`.** It means `nd::Proof::new` took a
> well-formed object CLAIMING the goal — LOWER's own formula bookkeeping. Only
> `the_kernel_accepts_the_generated_pair_inject1` consults the checker, and it
> does so for ONE proof. **⚠ WHETHER THE REST SURVIVE THE KERNEL IS UNMEASURED**,
> and the `nd::Proof::new` rejections above are a reason not to assume it.

### What P6c found that this section had not said

**1. A repeated term must materialise ONCE in the ∀-form, and this is mandatory
rather than an optimisation.** `⟨a,b⟩ = ⟨a,b⟩` rendered with two witnesses becomes
`∀p q. kpair(a,b,p) → kpair(a,b,q) → eq(p,q)` — which is `kpair`'s UNIQ, derived
from a triviality. The ∃-form deliberately does NOT dedup
(`repeated_terms_get_distinct_generated_names` pins that), so the two siblings
genuinely differ here. `theorem/elim.rs`'s S memoises the same way, for the same
reason.

**2. UNIQ is needed only where the materialisation is POSITIVE.** This section
said the ∀-form and the source agree "only through UNIQ" without qualifying it.
Correct for `Pair_iff`, where the materialisation sits left of an `↔`. In a purely
negative position — `Pair_inject1`'s antecedent — the ∃- and ∀-forms are
classically equivalent outright and no UNIQ is involved. The obligation is real
where it applies; it is not uniform, and `constant/`'s S2/S3 already discharge it
for every emitted constant, which is why P6c records no new `Obligation`.

**3. The ∀-form entry point bounds its fragment, and the P6c row did not.** It
covers first-order constant applications under the propositional connectives and
guarded quantifiers — which is what `Pair_iff`/`Pair_inject1` need — **plus the
∃ path's `logical_constant` table, `Ex1`/`Ball`/`Bex`/`Subset`, ported to the
∀-form as its sibling carries it** — and refuses BY NAME: `Pure.eq`; every OTHER
`is_constant: true` at proposition position, which is 48 defined predicates and
the largest fragment gap left; λ and meta-function application at term position;
quantifiers over non-`i`; a class-sorted argument; and any materialisation whose
arguments mention a quantifier-bound variable, since hoisting it to the prefix
would capture. Nested materialisation IS supported.

### Deleted, 2026-08-19 — and one impossible state left standing

Four `pub` items had **zero** references anywhere, tests included, and are gone.
Removing them did not move a single test, which is what makes the claim that they
were dead a measurement rather than a reading:

| deleted | why it was dead |
|---|---|
| `ConvertCtx::free_var_types` | declared, initialised empty, read at two sites, **written nowhere** — so `classify_type` fell to `Unknown` and the tag was defaulted BY POSITION. `from_meta`'s refusal is the correct behaviour; this was the thing that looked like it solved sorts and did not |
| `linearize::{ProofFile, parse_proof_structure}` | a second, unused (statement, proof) splitter — `export::proof_term::statement_and_proof` is the one canonical path |
| `class::seed_characterisation` | superseded by the seed the compiler synthesises |
| `ir::fol::FolTerm::from_text` | the ONLY constructor of `FolTerm::HandleRef` |
| `ir::isa::Expr::is_propositional` | never consulted |

> **⚠ `FolTerm::HandleRef` IS NOW UNCONSTRUCTIBLE AND ITS 20 MATCH ARMS ARE DEAD.**
> Deleting `from_text` removed the only site that ever built one, so the variant is
> an impossible state that `ir/fol.rs`, `class/`, `constant/` and `gate/` all still
> pattern-match on — 20 arms across 7 files, several in emit-critical paths
> (`to_text`, `substitute_term`, `free_term_vars`). It was left standing ON PURPOSE:
> a 20-site change to a core type is its own unit of work, not a cleanup-pass
> change made on the way to a handoff. Removing it is a real simplification and
> should be one commit.

### Unverified

- `type_env`'s COVERAGE is checked on `ZF.pair/3442` and `/3450` only. Whether
  every theorem in the corpus has an entry for every free variable of its
  statement — and whether every such type lowers through `lower::sort` — is
  unmeasured. P6b's criterion measures it for one theory.
- That `Ax(Combination)` at a connective is always discharged by the `cong_*`
  family is read off §14's stratum-B census, not from the nodes themselves.
- ~~Whether the ∀-form changes any already-emitted constant unit.~~ — **checked**:
  both `..._is_what_compiler_b_regenerates` pins hold and
  `every_refusal_carries_a_verdict` still reports the same line total and worst
  unit, so the artifact is byte-unchanged.
- ~~The ∀-form is exercised on TWO statements … its coverage over the corpus is
  unmeasured.~~ — **measured**, and it is `the_lower_reach_census` that measures
  it: the goals that refuse inside `render_in` split into the families above. Its per-construct behaviour is still pinned on a handful of
  statements; what is now known is the SHAPE of what it refuses, not that every
  accepting path is right.

---

## 18. The constant/theorem stratification

§10's phase table draws **P4 → P6** as a one-way arrow, and §17's "what must
change" item 2 reads it the same way: constants first, theorems after, `ConstEnv`
the only channel between them. That arrow encodes an assumption, and this section
retires it.

**The assumption.** Everything a constant owes — `_def`, `_EX`, `_UNIQ`, `_CONG`,
`_GRAPH` — is derivable from its `@def` body together with constants already
emitted. It holds for every constant whose body *describes* its value: `Pow`,
`Upair`, `Union`. It fails for a constant whose body *constructs* one.

**Where it fails.** `nat`'s graph must compile a class over `@def(nat)`'s body,
and that body meets the atom `Inf(·)`. §11.5 shows the atom can never carry a
rule — the one `Intro::Skolem` primitive, the only one with no `_CONG`, admissible
only, and R1 forbids that. §11.5's route is therefore a proved-equivalent
`Inf`-free ψ. But ψ's proof is `nat_0I` / `nat_succI` / `nat_induct`, whose
statements mention `nat`, so rendering them needs `nat` in `ConstEnv` — which the
one-way arrow grants only after `nat` has fully emitted, graph included.

That is a cycle against the arrow, and it is not a `nat` quirk. It is the shape of
every constant introduced by a fixpoint or a recursion.

### The distinction the arrow collapses

Rendering a *statement* mentioning `C` needs `C` to **denote**: its signature, and
that it exists and is unique. Compiling a *class* over `C` needs `C`'s **graph**,
because Compiler B turns `C(x⃗,r)` into a membership atom. Two different
obligations, and bundling them into one "emitted" flag is what creates the
deadlock.

The code already half-knows this. `walk_cenv` (`theorem/lower_tests.rs:278`)
builds `ConstEnv` from `w.constants` and **never reads `w.graphs`** — the channel
P6 needs was never the graph. And `constant/mod.rs:2067` already asserts that each
emitted constant *either* carries a `_GRAPH` unit *or* sits in `w.no_graph` with a
reason. The distinction exists; what does not exist is a pipeline that uses it.

### Three levels, one fixpoint

| level | artifacts | promotion needs |
|---|---|---|
| **L0 DECLARED** | signature, `C_def` | the export |
| **L1 DENOTING** | `C_EX`, `C_UNIQ`, `C_CONG` | the body, plus **L2** of earlier constants |
| **L2 GRAPHED** | `C_GRAPH` | the body — *or* a translated theorem about `C` |

A theorem translates when every constant in its statement is at **L1**. L2 of
none. The driver is then a fixpoint over both layers rather than a single pass:
promote what can be promoted, translate what can be translated, repeat until a
round changes nothing.

### Why this is a stratification and not a loophole

The cycle lives in the coarse *layer* graph. At *artifact* granularity the order
is still a DAG:

```
lfp_GRAPH → nat_def → nat_EX / nat_UNIQ → nat_0I, nat_succI, nat_induct
          → nat_CHAR (body ↔ ψ) → nat_GRAPH
```

Every node cites strictly earlier nodes. `nat_EX` and `nat_UNIQ` cite no theorem
about `nat`; the theorems cite them; the graph cites the theorems. **That is the
whole soundness argument**, and it yields a checkable gate:

> **G6 — `C_GRAPH` may cite a theorem, provided no cited theorem's own closure
> reaches `C_GRAPH`.**

**G3 is untouched.** G3 closes `EX`/`UNIQ`/`CONG` over definitional order, and
those stay at L1, where no theorem is ever cited. What moves is `GRAPH`, which was
never part of the definitional closure — the implementation bundled it there.

### G1's third introduction route

§10's G1 table has two rows. The stratification adds the one the fixpoint family
needs:

| route | `EX`/`UNIQ` from | `GRAPH` from |
|---|---|---|
| definitional | body | body |
| **characterised** | body | **a translated theorem about the constant** |
| Skolem | a proved `∃r. φ(r)` | its characterisation, or never |

Content is still zero: a characterisation is a *theorem*, proved from earlier
material, not an admission. `@def(C)` stays Isabelle's — §11.5's warning against
substituting a different constant under the same name governs the characterised
route exactly as §10's `Upair` argument governs the definitional one.

**⚠ THE REFUSAL ROOTS ARE ONE PROBLEM, NOT SEVEN.** The roots no peel reaches are
constants introduced by a fixpoint or recursion: body a construction, usable facts
theorems. Peeling them one at a time is the failure mode this section exists to
prevent — the characterised route retires the class.

### Termination

A fixpoint over two mutually-feeding layers can spin. It does not, because the
rule is: **a round that promotes nothing, with a non-empty waiting set, produces a
refusal set — never another round.** §1a's refusal-totality requirement for
`build/` already forces that shape.

**⚠ ONE CYCLE STAGING CANNOT BREAK.** A constant whose *`EX`/`UNIQ`* needs a
theorem about itself is an artifact-level cycle, not a layer-level one, and no
interleaving fixes it. Those take the Skolem route or refuse by name. Which
constants land there is **open**, and the answer sizes what the characterised
route is worth. `the_recfun` is the candidate to settle first.

### What must change

| | change | status |
|---|---|---|
| **1** | this section, plus pointers from §10's G1 table, §10's phase table, §11.5 and §17 | ✅ landed with this edit |
| **2** | `no_graph` becomes a resting state rather than an invariant violation (`constant/mod.rs:2079`) | ✅ **LANDED** · the retired `is_empty()` is replaced by a pinned `no_graph` key set, so a graph-less constant is legitimate but an *unlisted* one still fails. `:2067`'s "a `_GRAPH` unit OR a reason" now runs BOTH branches |
| **3** | the driver becomes a fixpoint over **both** layers | ❌ **LAST OF FOUR, NOT BLOCKED** — ordinary work, ordered behind the edge it would traverse. See below |

**Row 2 landed, and the premise it tests held.** With `nat` resting at L1 the
census moved: the reason `compound term `Nat_2enat` needs P4`, previously the
largest single no-goal bucket, left the table entirely, family C fell, and
`CLOSURE` gained a theorem. The numbers live in the tests, not here (§10's rule).

### Why row 3 comes last — an ordering, NOT a blockage

**⚠ AN EARLIER VERSION OF THIS SUBSECTION SAID ROW 3 WAS "BLOCKED, AND NOT ON
EFFORT". BOTH HALVES WERE WRONG.** Nothing outside this repository gates it, and
it is entirely a matter of effort — the effort simply sits upstream of it. Calling
work "blocked" when it is merely ordered invites a future session to wait for
something that is never coming. The chain is four links and every one is ordinary:

| | | gated by |
|---|---|---|
| 1 | arity-n schema instantiation (`theorem/lower.rs:210`) | **nothing** |
| 2 | `nat_induct` lowers; the three ω theorems become proof objects | 1 |
| 3 | a consumer in `constant/` composes them and passes the result to `graph_unit`'s `equiv` — **the missing cross-layer edge** | 2 |
| 4 | the fixpoint loop | 3 |

**⚠ ROW 3's REAL GATE IS LINK 3, NOT LINK 1.** The loop needs SOME constant to
reach L2 through a theorem, not `nat` specifically. Whether any constant can be
characterised without a schema — and so reach link 3 without link 1 — is
**UNMEASURED**. An earlier draft asserted one could; that was an argument, not a
finding, and it is demoted here rather than deleted because it is worth checking:
if such a constant exists it exercises the edge sooner and more cheaply than `nat`.

**⚠ DO NOT BUILD THE OUTER LOOP BEFORE ITS EDGE EXISTS.** The theorem-layer
fixpoint is already correct and already terminates by this section's own rule —
`build/mod.rs`'s `loop` breaks on `gained == 0`, and the leftovers become
`Blocked::Waiting`, with `is_total()` asserted. What is missing is not the loop.

The cross-layer edge does not exist, in three places at once:

- `translate(w: &Walk)` takes the walk **immutably**, and computes `const_env(w)`
  and renders every goal **once, before** the loop — so the constant layer is
  frozen by construction.
- `theorem::foundation::Foundation<'a>` borrows `&'a Walk`. Read-only.
- `constant/` and `class/` contain **zero** references to `crate::theorem`.

So a fixpoint spanning both layers would iterate over an edge with no
implementation, and would provably run exactly one round until something can turn
a proved theorem into a characterisation. That is dead code, and coding rule 8
forbids it — which is a reason to build it LAST, and not a reason to call it
blocked.

Row 3 is not "more architecture". It is waiting on the first constant that
actually reaches L2 through a theorem, and that is link 3 above.

**The criterion, and it is about rendering, not lowering.** A constant held at L1
with no graph must reach `ConstEnv` and unblock the statements that name it. For
`nat`: apply the graph-less emission and check whether `nat_0I` / `nat_succI` /
`nat_induct` still refuse with `compound term `Nat_2enat` needs P4`. If they do,
the premise above is false and this section is wrong. That check touches
`statement/` only — no part of E or LOWER is involved in it.

### What this section does NOT require

**⚠ P6 COVERAGE IS AN ORTHOGONAL AXIS, AND CONFLATING IT WITH THE STRATIFICATION
OVERSTATES BOTH.** The three levels and the fixpoint are complete without any
change to what E and LOWER accept. Which theorems translate is P6's own problem,
and it is the same problem whether or not this section lands.

What the FIRST INSTANCE additionally needs is therefore listed here rather than
above: `nat`'s characterisation runs through `nat_induct`, whose schema parameter
`P` has arity 1, and `theorem/lower.rs:210` refuses any arity > 0 (§17 item 4).
So `nat` cannot complete until that lands — but it is a coverage item on `nat`'s
critical path, **not a requirement of this design**. A constant whose
characterisation needs no schema would land without it.

There is a pattern worth recording and not over-reading: the characterised route
tends to run through induction principles, because minimality is what it proves,
and induction principles are schemas. That is a property of the fixpoint family,
not of the architecture.

---

## Sources

- `FOUNDATION.md` — the authoritative document. This one is subordinate to it;
  where they disagree, either this is wrong or §0's correction was not applied.
- fol-zfc checker, branch `comb-verifier` @ `c59e9b1`. Read this session:
  `proof/runner.cpp`, `proof/nd/stack.cpp`, `proof/schema_resolve.{h,cpp}`,
  `core/formula.h`, `runtime/runtime.cpp`, `tools/proof_checker.cpp`,
  `parser/formula.y`, `zfc/basics/axioms.fol.def`.
- Class Existence Theorem, Tuple Lemma, Expansion Lemma, predicativity:
  <https://en.wikipedia.org/wiki/Von_Neumann–Bernays–Gödel_set_theory>, and
  **the second independent source, now obtained**: Taras Banakh, *Classical Set
  Theory: Theory of Sets and Classes*, <https://arxiv.org/abs/2006.01613>,
  §8 (Gödel's Theorem 8.2) with Lemmas 8.3–8.5.

  **The T4 disagreement is resolved and was never mathematical.** Banakh takes
  `Inversion` — `X⁻¹ = {⟨y,x⟩ : ⟨x,y⟩ ∈ X}` — as an *axiom*, where Gödel derives
  it; so both derivations are correct and the two presentations simply
  axiomatise differently. FOUNDATION §3's note that T4 "needs Empty" applies to
  the derived form, which is the one `base/tiers/tuples` carries.

  **What Banakh settles that Wikipedia only implied.** Theorem 8.2's atomic
  cases are enumerated exhaustively — `xᵢ ∈ xⱼ`, `xᵢ ∈ Yⱼ`, `Yᵢ ∈ xⱼ`,
  `Yᵢ ∈ Yⱼ` — so there is **no tuple-membership atom** in the fragment. That is
  the fact FOUNDATION §1 R5 now records, and it is why a graph atom is unfolded
  rather than placed.

  Worth knowing for a later increment: Banakh's Lemma 8.3 places an atom by
  *pullback along projections* (`{z ∈ Uⁿ : ⟨Prᵢ(z),Prⱼ(z)⟩ ∈ E}`), not by moving
  the seed. That is arity- and permutation-generic by construction and subsumes
  Expansion as its k=2 case — the alternative to the unfold, priced out for now
  by the unfold's measured cost, not ruled out.

### Conservativity — which theorem row 5 actually rests on

Row 5 of §10's chain (`NBG ⊢ (σ°)^set ⟹ ZFC ⊢ σ°`) is the one step carried by a
citation rather than by a probe, so the citation has to be right.

**We depend on exactly one result: NBG (with *set*-AC) is a conservative
extension of ZFC — Novak and Mostowski, 1950.** Checked against sources.

**We do *not* depend on the global-choice result**, and that is a consequence of
the axiom-19 decision rather than luck. Isabelle/ZF's Choice is `AC.AC`, read off
the export:

```
a ∈ A ⟹ (⋀x. x ∈ A ⟹ ∃y. y ∈ B(x)) ⟹ ∃z. z ∈ Pi(A,B)
```

— the **set** form, and necessarily so, since Isabelle/ZF has no class type and
therefore cannot *state* global choice. Had we written global choice into the
base, row 5's warrant would move from Novak–Mostowski to the much deeper result
that NBG + Global Choice is conservative over ZFC — established independently by
Kripke, Cohen and Solovay in the 1960s and first published by **Felgner (1971)**,
*Comparison of the axioms of local and universal choice*, Fund. Math. 71(1)
43–62. Same for Regularity: `ZF_Base.foundation` is the **set** form, weaker than
the class-form NBG usually takes.

*That the base should take the form the source uses is therefore not a
preference: it keeps row 5 on the elementary theorem.*

**Two corrections to what this document previously implied.** Earlier drafts and
commit messages attributed the conservativity result to "Novak, Mostowski,
Shoenfield" — **the Shoenfield attribution is unverified** and is dropped.
And the Wikipedia page cited above *asserts* NBG's conservativity but supplies
neither the precise relativised statement nor any attribution, so it was never an
adequate source for a load-bearing step; it is no longer cited for that claim.

**Still unsourced, and marked as such:** the precise relativised form
`NBG ⊢ σ^set ⟺ ZFC ⊢ σ` — we have the theorem's existence and attribution, not
its exact statement from a primary source. And the claim that Morse–Kelley is
*not* conservative (it proves `Con(ZFC)`) is standard but likewise unverified
here.

**One sharpening worth keeping.** Global choice is conservative over *ZF*, but
[not over Zermelo set theory](https://arxiv.org/abs/2312.11902) — so the result
is sensitive to the base theory having Replacement. That is a concrete reason not
to treat "choice is conservative" as a fact one can wave at, and a second reason
to prefer the weakest sufficient form.
