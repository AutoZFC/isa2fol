# Foundation

Translate Isabelle/ZF theorems into pure FOL derivations that a kernel checks, so
that checking one witnesses `ZFC ⊢ σ`.

Two commitments, never traded:

- **N1 Soundness** — if the checker says Proved, it is a theorem of the base
  below. The kernel is the sole arbiter.
- **N2 Faithfulness** — the emitted statement is equivalent, *in this
  foundation*, to the honest rendering of the Isabelle theorem. A weaker
  statement labelled "we proved T" is a false claim about what was proved.
  **Nothing checks N2 but us.**

> **⚠ TUPLES ARE FUNCTIONS (§1a), AND EVERY NESTED-TUPLE VOCABULARY IN THIS
> DOCUMENT IS WRONG — NOT SUPERSEDED, WRONG.** An n-tuple is a function with
> domain `n`, as Isabelle/ZF's own `n → A` is; a meta function of arity `n` is a
> class function on n-tuples. R7's left-nested form, S5's `tmem`, §2's
> factorisation through Kuratowski pairs, R5's Tuple-Lemma paragraphs and all of
> §3a reason in nested pairs, and each carries a warning where it stands. **The base
> stays standard NBG** — Gödel's group B as Mendelson states it — and everything
> we use of it is PROVED from it, never admitted (§1a).
>
> **⚠ A CONSTANT IS A CLASS (§1a), APPLIED BY MEMBERSHIP: `f(x⃗) = r` IS
> `⟨t, r⟩ ∈ F`, `t` THE TUPLE OF `x⃗`.** Wherever §1 and §2 write a relation
> `F(x⃗, r)`, read that atom. Of the four obligations the relation form owed per
> constant, GRAPH is the class itself, CONG is membership's congruence — one
> theorem for every class (`base/tiers/classes`) — and EX with UNIQ is the class
> being a function (`base/tiers/metafun`). What each constant owes is that its
> class exists and is a function (decided 2026-09-29).

---

## 1. The base — the only things admitted

Single-sorted NBG. Variables range over **classes**; a **set** is a class
satisfying `set(·)`. Signature: `elem`, `eq`, `set` — three predicates, **no
function symbols**. Pairs: `⟨x,y⟩∈C := ∃p.(Pair(x,y,p) ∧ p∈C)`.

`set` must stay **undefined**. Defining `set(x) := ∃C. x∈C` makes B3 quantify over
all classes — Morse–Kelley, which is *not* conservative over ZFC.

**Encoding hygiene** (free in two-sorted textbooks, explicit here)
1. `members_are_sets` — `∀x y. elem(x,y) → set(x)`
2. `elem_first_subst` — `∀x y S. eq(x,y) → elem(x,S) → elem(y,S)`

**I — Extensionality**
3. `∀A B. (eq(A,B) ↔ ∀u. (set(u) → (elem(u,A) ↔ elem(u,B))))`

Stated as `↔`, and the `←` direction is load-bearing, not decoration. It is the
only route from `eq(A,B)` back to membership agreement: axiom 2 substitutes on the
*left* of `∈` only, so without it `eq(A,B) → (u∈A → u∈B)` is underivable, and §3's
normalisation — which rewrites every equality atom `Δ = Γ` to `∀z.(z∈Δ ↔ z∈Γ)` —
cannot run at all. `eq` remains a primitive predicate; nothing is defined away.

**The inner quantifier is guarded, and the guard is free.** This document
previously wrote it bare. The two forms are interderivable *given axiom 1*:
`members_are_sets` falsifies `u∈A` for every non-set `u`, so at such a `u` both
sides of the inner `↔` are false and it holds vacuously. So the bare form is not
weaker — but it is not the shape anything else uses, and the guarded one is what
`base/axioms.fol.def` carries and what §3's normalisation emits. Discharging the
guard costs nothing where it is consumed: `elem_second` gets `set(z)` from `z∈A`
by axiom 1, with no case split.

**II — Class existence, Gödel B1–B7.** The finite replacement for comprehension.
4. B1 `∃E. ∀u v. ⟨u,v⟩∈E ↔ elem(u,v)`
5. B2 `∀A B. ∃C. ∀u. u∈C ↔ (u∈A ∧ u∈B)`
6. B3 `∀A. ∃C. ∀u. u∈C ↔ ¬u∈A`
7. B4 `∀A. ∃C. ∀u. u∈C ↔ ∃v. ⟨u,v⟩∈A`
8. B5 `∀A. ∃C. ∀u v. ⟨u,v⟩∈C ↔ u∈A`
9. B6 `∀A. ∃C. ∀u v w. ⟨⟨u,v⟩,w⟩∈C ↔ ⟨⟨v,w⟩,u⟩∈A`
10. B7 `∀A. ∃C. ∀u v w. ⟨⟨u,v⟩,w⟩∈C ↔ ⟨⟨u,w⟩,v⟩∈A`

**III — Set existence.** Each asserts `set(·)` of what it builds.
11. Empty · 12. Pairing · 13. Union · 14. Power · 15. Infinity
16. Replacement `∀F. Fun(F) → ∀x. set(x) → ∃z. set(z) ∧ ∀v.(v∈z ↔ ∃u.(u∈x ∧ ⟨u,v⟩∈F))`
17. Separation `∀A B. set(B) → ∃z. set(z) ∧ ∀u.(u∈z ↔ (u∈B ∧ u∈A))`

**IV** — 18. Regularity · 19. Choice

`set(·)` guards are written explicitly. They are mandatory on B3: unguarded, the
complement of `∅` is the class of all objects → collapse.

### The rules

> **R1 — Nothing is admitted that is not one of the 19 above.**
>
> **R2 — Every schema is proved.** No allowlist, no debt, no grace period.
>
> **R3 — Every quantifier translating an Isabelle `i`-variable is `set(·)`-guarded,
> interleaved.** No exceptions; the shape is part of the rule.
>
> **R4 — A context holds only sets, so a class-taking constant has no graph.**
> Its graph is built per USE SITE, where the class argument is concrete.
> **Under §3's assignment foundation this reads: every value in an assignment's
> RANGE is a set, and the index set is a set.** The older reading — "a tuple slot
> is always a set" — is the same rule stated against the superseded position-
> indexed context (§3a), and is what most of this document's prose still says.
>
> **R5 — A constant's graph is compiled from its `@def` body's CLASS-FREE CORE,
> with every class a parameter** — earlier constants' graphs, and the constant's
> own internal class — **never by unfolding those bodies inline.** A class
> binder is *opened* before the compiler sees the formula, never compiled.
> A meta-level constant (S1, "named only at the object level") has no graph: it is
> unfolded where it stands, which is not the inlining forbidden here.
>
> **R6 — The ceiling is 195 of 197.** Two constants violate S5 in their own
> definition and are permanent refusals, not gaps.
>
> **R7 — Every emitted constant is UNARY on ONE tuple, and a tuple is a
> function (§1a).** A constant of `n` set arguments is emitted as a CLASS of
> pairs `⟨t, r⟩`, applied by membership, with `t` the n-tuple
> `{⟨0,a₁⟩,…,⟨n−1,aₙ⟩}` — at every arity, 1 included; class arguments stay
> outside it (R4). **The one primitive is the Kuratowski pair** — a function
> is a set of pairs, so the pair cannot itself be a tuple.

R2 is a mathematical criterion, not housekeeping. A legitimate schema is proved
**parametrically**, with `P` uninterpreted — so it is legitimate exactly when its
truth for arbitrary `P` follows by pure logic *without* the class `{x : P(x)}`.
A schema that cannot be proved parametrically is an attempted class over an
uninterpreted predicate: Morse–Kelley. Delete it and instantiate its uses at
concrete formulas.

R7 costs nothing in faithfulness and buys one pattern instead of an
arity-indexed family. Writing `tup(a₁,…,aₙ, t)` for "`t` is the function with
domain `n` and `t(k−1) = a_k`", the emitted biconditional

```
  C(t,r)  ⟺  ∃a⃗. (set(a⃗) ∧ tup(a⃗, t) ∧ φ_C(a⃗, r))
```

is a **definition**, so the n-ary statement is recoverable from the unary one:
given sets `a⃗`, the tuple exists and is unique (§1a), so `C(t,r) ⟺ φ_C(a⃗,r)`.
Isabelle's constants stay n-ary; what we emit is the *proof*, and there the unary
reading is the one S3's induction runs on. **R7 admits no subset.** A class
parameter, a definition-internal class and `n ≥ 3` are all in scope; scoping it to
whichever constants happen to emit today is the corpus deciding the
specification, which §5's method rule forbids.

R7 has a consequence that is not optional: tupling `C` changes its arity, so
**every body applying `C` must be rewritten** `C(a⃗,r) ⟿ ∃t. (set(t) ∧ tup(a⃗,t)
∧ C(t,r))`. That rewrite is definitional by the tuple's EX and UNIQ, and it is a
prerequisite of R7, not a follow-on.

> **⚠ R7 SAID "THE LEFT-NESTED TUPLE", `C(p,r)` WITH `kpair(a,b,p)`, AND CITED
> `pair_fn_{ex,uniq,cong}` AS WHAT CONSUMES TWO INTERMEDIATES.** That made an
> n-tuple a Kuratowski pair of pairs — positions again, and at arity 3 the triple
> `tmem` put into S5. The tuple is a function; the pair is only what functions are
> made of.

R3 is §2 S6 stated as an enforceable rule. It is not hygiene. Conservativity is
`NBG ⊢ σ^set ⟺ ZFC ⊢ σ`, stated for the **relativized** sentence, so an
unguarded `∀x. φ` is a *different theorem* — one about classes. Nothing
mechanical catches the substitution: an unrelativized claim checks green, which
puts R3 on the N2 side, where we are the only arbiter.

| | |
|---|---|
| **what R3 binds** | a claim that **asserts an Isabelle theorem** — one that names which theorem, and whose name resolves in the export |
| scope inside one | every `i`-binder, **including the ones S1 invents**. `p` in `kpair(a,b,p)` has no Isabelle counterpart and is still a set |
| shape | `forall a. (set(a) -> (forall b. (set(b) -> φ)))` — never `forall a. forall b. (set(a) -> (set(b) -> φ))` |
| outside it | the 19, and every base lemma. A **class** existential stays bare: `set(C)` is *false*, not redundant |

**Why the base is outside, and it is not an exemption.** *NBG is a larger world
than Isabelle's, and the base works in it.* `upair_uniq` is single-valuedness for
**classes** — it is extensionality, and it is true of classes that are not sets.
Nothing about it claims to be a theorem of Isabelle/ZF, so there is no `σ` for
`σ^set` to have to equal, and R3 has no purchase.

This is forced, not chosen: **tier 2 is where sethood is *derived*, so it cannot
presuppose it.** `upair_set` proves `set(w)` by taking `w0` from `upair_ex` (which
carries `set(w0)`), using `upair_uniq` to get `eq(w0,w)`, then `set_cong`. Guard
`upair_uniq`'s `w` and that proof needs `set(w)` to prove `set(w)`. A rule whose
enforcement makes the base circular is being applied where it does not belong.

So R3 is not "relativize the tree"; it is **relativize the claims that say they
are Isabelle's**. Those are exactly the ones N2 is about, and the base beneath
them is free to be NBG.

**The shape is load-bearing.** The two forms are logically equivalent and the
kernel compares syntactically. Grouped guards are rejected at `qed`
(`derived formula doesn't match goal`) and at every `implies_elim` joining
the compiled class claim to `PrimReplace_EX`'s antecedent — both
interleave.

**UNIFORM-INTERLEAVED — the shape is the same in `base/`, and that is a HOUSE
RULE, not R3.** R3 exempts base lemmas and the paragraphs above say why; the
exemption is about *relativization*, which base does not owe. It is not about
*shape*. A guarded hypothesis in one shape cannot be fed to a kernel stated in
the other, so a base lemma whose guards are grouped is unreachable from the
claims that would use it — and the failure is a syntactic mismatch far from its
cause. Every generator already emits interleaved, because they all fold the one
brick `forall_guarded`, which puts the guard *inside* its binder. So this rule
costs nothing to keep and only ever removes an adapter.

**But it is an aspiration in `base/`, not a fact, and this paragraph used to
read as though it were one.** Measured: **25 of 114** base declarations bind a
`set(·)`-mentioned variable without the guard immediately following. Not all are
debt — `upair_def`
conjoins sethood deliberately (a conditional guard would leave `upair`
unconstrained off-domain and break R4), `members_are_sets` has `set(x)` as its
*conclusion*, and `set_cong` consumes `set(A)` as a *premise*, where
relativizing would state a different theorem. Telling those apart is not
syntactic, so the sweep reports the superset and **pins it**: nothing new may
join the list silently. That is the enforcement this rule never had — it is why
`the_UNIQ` sat grouped, in a file whose own header said everything was
interleaved, for as long as nothing instantiated it.

**⚠ THAT PIN DOES NOT EXIST AND THIS PARAGRAPH READS AS THOUGH IT RUNS.**
Nothing sweeps `base/` for grouped guards, so nothing is being pinned. An
instrument that cannot run is not weaker evidence than one that fails — it is
NONE, and it looks identical to a pass in a red suite.

Two consequences worth stating, because both look like losses and are not:

- **`compose_uniq` and `compose_cong` were grouped once**, while `compose_ex`
  and `replace_fun` were not. Nothing caught it, because nothing instantiated
  them. `base/tiers/s2s3` carries the re-threaded forms; the probe
  `constants_s2s3` keeps the grouped ones, and the two deliberately diverge.
- **Under uniform guards, Pure's `abstract_rule` has NO relational content.**
  `f ≡ g` and `⋀x. f x ≡ g x` become the *same formula*, so the rule is
  `A → A`. That is correct under S1: a function is a relation, so function
  equality *is* pointwise equality — there is no function object left to be
  extensional about. Grouping was the only thing making the two look different.
  `subst_rel` is already `A → A` for the same kind of reason: `subst` reduces to
  exactly CONG(P) and asks for nothing else.

`docs/phase2_probes/proof_layer` and `eq_reflection_kernel` still carry grouped
shapes. They are probes, so they are correct as evidence; they get re-threaded
when they are promoted into `base/`, the way `constants_s2s3` was.

**R3 costs proof length and nothing else.** Measured by relativizing `Pair_iff`
(ZThm 3442) and `Pair_inject1` (ZThm 3450) over all six binders: the derivations
survive verbatim — `OK: 33 claim(s)`, empty stderr — at +12 and +18 steps, all of
them `assume set(v)`, `implies_intro`, and feeding the guards to a now-guarded
citation. **⚠ THE ARTIFACT IS GONE: this was measured on `zf_fst_conv_e2e`, since
deleted as a relic of the superseded `The` route (S3). The finding stands; it is
no longer REPRODUCIBLE, and `zf_pair_e2e` would have to carry it again.** There is no soundness-against-coverage trade to
weigh, so an unguarded claim is never one that *had* to be.

An unguarded scaffolding lemma is a strictly **stronger** claim, so a guarded
consumer may cite one. That is admissible only where its truth over classes is
*proved*, never presumed: dropping a guard strengthens the claim, and the
stronger claim may simply be false.

---

**R4.** *Claim:* `pmem(u,v,X) → set(u) ∧ set(v)`.

*Proof.* `pmem(u,v,X)` needs `kpair(u,v,p)`, which needs `upair(u,u,a)`, which by
`upair_def` is `∀t.(t∈a ↔ t=u)`. At `t := u`, `eq_refl` gives `u∈a`, hence
`set(u)` by `members_are_sets`. Symmetrically for `v` through `upair(u,v,b)`. ∎

So for `C(x⃗,F,r)` with `F` a class, `⟨x⃗,F,r⟩ ∈ G` is not merely *unavailable* —
it is **false**. There is no graph to build.

*Consequence.* The graph is built **per use site**, where the class argument is
concrete and `{⟨x⃗,r⟩ : C(x⃗,C_ψ,r)}` is a single legitimate class. That is R2's
template pattern at a new site: not provable parametrically, so instantiate per
occurrence. **138 of 197 bodies carry a λ** (§10), so this is the main line and
not an exception — and exactly **1** constant is transitively class-free.

**R5.** §3's compiler reads exactly three atoms: `elem`, `eq`, `pmem`. A raw
relation atom `C(x,r)` has no rule, so a φ that mentions a constant does not
compile. Unfolding `C_def` is what puts it in the fragment, because every body
reaches `elem`/`eq` through earlier constants.

*Why parameters and not recursion.* Substituting an earlier constant's body
inline is exponential in definitional depth. Handing its graph over as a
**parameter** and writing `pmem(x,v,G_C)` is linear, and class-existence is
already stated with parameters — `∀A⃗ ∃C ∀x⃗.(⟨x⃗⟩∈C ↔ φ(x⃗,A⃗))`.

*Why the body itself is not the input.* A constant with an internal class has
`@def` body `∃C.(χ_φ(C) ∧ A(x⃗,C,r))` — writing `χ_φ(C)` for
`∀t⃗.(⟨t⃗⟩∈C ↔ φ(t⃗))`, and `A` for the chain atom that takes the class. `∃C` is a
**class quantifier**: outside §3's fragment, and admitting it is Morse–Kelley.
Both halves are forced and neither moves — the body must bind `C`, because R4
forbids `F` a class argument, and the fragment must refuse `∃C`. So the input is
`A(x⃗,C,r)` with `C` **free**, which is predicative, and the equivalence back to
the body is *proved*:

1. `χ_φ(C) → χ_φ(D) → ∀t⃗.(⟨t⃗⟩∈C ↔ ⟨t⃗⟩∈D)` — immediate, both sides being `φ(t⃗)`.
   No class extensionality is needed, and none is available.
2. `A`'s own `_class_cong` — R4's fourth obligation — transports `A(x⃗,D,r)` to
   `A(x⃗,C,r)` along that agreement.

Hence `F(x⃗,r) ↔ A(x⃗,C,r)` for **any** `C` with `χ_φ(C)`: left to right by opening
the body's existential at some `D` and transporting, right to left by witnessing
it with `C`. And `∃C. χ_φ(C)` is exactly what the constant's own class unit
asserts, which is §3 at φ. Nothing new is admitted.

*Consequence.* GRAPH is a fourth obligation discharged in definitional order,
alongside EX/UNIQ/CONG, and it inherits G3's ordering constraint.

> **⚠ FROM HERE TO R6, THIS SECTION REASONS IN NESTED PAIRS** — seeds, blocks,
> coordinate 1, T1–T4 — and is wrong under §1a. What survives is R5 above: a graph
> is a parameter, never an inlined body.

*How the atom enters, and why not a wider Tuple Lemma.* **The Class Existence
Theorem's fragment has no atom `⟨x⃗⟩ ∈ Y`** — its atoms are `xᵢ ∈ xⱼ`, `xᵢ ∈ Yⱼ`,
`Yᵢ ∈ xⱼ`, `Yᵢ ∈ Yⱼ` and nothing else, which is why both sources state the Tuple
Lemma for a class *of ordered pairs*. So `pmem(x,v,G_C)` is notation, and a graph
atom of arity ≥ 2 is **unfolded** to what it abbreviates rather than placed: the
nesting witnesses bind inside φ, where they are context slots, and the seed
Expansion sees stays a pair. Only Kuratowski pairing is unfolded — fixed depth 3,
independent of the constant — so this is not the inlining R5 forbids.

Widening the seed does not work *with the four Tuple lemmas as stated*, and the
reason is structural. Write the seed as a block `b`; left-nesting flattens
`⟨b,x,y⟩ = ⟨b₁,…,b_k,x,y⟩` only when `b` is in **coordinate 1**. B5 (append) and
T2 (insert) keep it there and are block-generic; **T1 (prepend), T4 (swap) and
Gödel's B6 put it in coordinate 2 or 3 and are not**. Measured: of the 13
constants blocked on this, 7 need exactly T1 or T4. Both are kernel-checked, and
a width-3 seed is unplaceable at the third `upair` of every pair — which is why a
prepend may be handed only a single context slot.

**This paragraph used to continue "since a class is opaque … the permutations a
real body needs are unreachable". THAT IS FALSE, and the reason it is false
matters.** A prepend never takes the seed apart. It *assembles* `⟨b⃗,y⟩` from the
lemma's own free set variables and tests membership, so opacity — true as stated
— has no purchase. The prepend of a width-3 block is an ordinary instance of §3
at

```
φ(z,b₁,b₂,y) := ∃p.(set(p) ∧ kpair(b₁,b₂,p) ∧ pmem(p,y,A))
```

with `A` a parameter: every atom is `elem`/`eq`/`pmem`, the pairing witnesses are
guarded set existentials B4 eliminates, and `z` never occurs. **Kernel-checked** —
34 classes, 1532 lines, paid ONCE and parametrically in `A`. T1 is the `k=1` case
of the same schema.

So the ceiling is a **missing lemma family**, indexed by block width, not an
impossibility. What is NOT yet established: the derivation cost as `k` grows, and
whether the emitter can be taught to cite such a family.

**R6.** Two constants refuse *on their own account*, and each is a violation of
the specification rather than a gap in it. **The handle is STRUCTURAL, not a
generator's output**: a constant whose value is a meta-function is one whose
`@def` body is a top-level `λ`, and exactly two of the 197 are —
`OrdQuant.setclass` and `ZF_Base.split`. The former handle went with the encoder;
this one survives it.

| | |
|---|---|
| `split`, `setclass` | the constant's **value** is a meta-function — S5: a reified graph used as a *value* is a member, hence outside the theorem |

> **⚠ THIS ROW USED TO READ FOUR, ADDING `cond`/`update` AS "a proposition in
> term position — S4". THAT WAS FALSE, and the way it was false is the lesson.**
> Both reduce through `ZF_Base.If`, whose exported signature is
> `args:[Pred(0),Term,Term]` — its first parameter **is declared a proposition**,
> so the proposition sits in *proposition* position. What reported S4 was
> `render_expr`'s argument loop calling `value()` on every non-λ argument while
> ignoring the declared sort. Relationally
> `If(P,a,b) = r  ⟺  (P ∧ r=a) ∨ (¬P ∧ r=b)`
> is first-order and single-valued: nothing is reified, and UNIQ holds. What `If`
> lacks is a **graph**, because a relation atom has no formula slot — which is
> exactly R4's situation with a class argument, and takes R4's route: build the
> graph per USE SITE, where the proposition is concrete. So these are `Omitted`,
> not `Refused`. Measured, **seven** constants carry a propositional parameter.
> *A refusal attributed to mathematics stops enquiry; that is why this one cost
> two constants of ceiling for a session.*

> **⚠ `split` IS NO LONGER ONE OF THE TWO** (2026-10-11). Its value is a meta-function
> because its declared value type is a type variable: it is a meta-level definition,
> unfolded (S1, "named only at the object level"), and refuses nothing. The ceiling
> below is this section's original count.

*Consequence.* Report **195** as the ceiling. Translating either of the two would
be translating a *different* constant, which is §4's failure mode.

---

## 1a. Functions and tuples — Isabelle's own, in class form

**Isabelle/ZF builds functions from pairs; the meta level is built the same way.**
Only the domain changes: a set there, every set here — so a class, not a set.
From `ZF_Base` and `func`:

| Isabelle/ZF, over a set `A` | its definition | class form, for the meta level |
|---|---|---|
| `Pair(a,b)` | `{{a,a},{a,b}}` | `kpair` — the one primitive, unchanged |
| `function(r)` | `∀x y. ⟨x,y⟩ ∈ r ⟶ (∀y'. ⟨x,y'⟩ ∈ r ⟶ y = y')` | the same, of a class |
| `f`a` | `⋃(f``{a})` — for a function, the `b` with `⟨a,b⟩ ∈ f` | `⟨a, r⟩ ∈ F`: application is membership; a function variable's reads `⋃(f``{a})` itself, `∅` where `F` has no value (S5) |
| `Lambda(A,b)` | `{⟨x, b(x)⟩. x ∈ A}` | a λ over every set: the class `{⟨x,r⟩ : φ_b(x,r)}`, by §3 |
| `beta`, `eta`, `fun_extension` | theorems of `func` | Pure's β, η, `abstract_rule` — theorems about such classes |
| `n → A`, i.e. `Pi(n, λ_. A)` | the n-tuples over `A` | **an n-tuple is a function with domain `n`** — a set, so it can stand in a pair |

**So: pairs → functions → tuples → meta functions of arity `n`.**

- **A meta function of arity `n`**, `[i,…,i] ⇒ i`, is a class function on
  n-tuples: `f(x⃗) = r` iff `⟨t, r⟩ ∈ F`, `t` the tuple `{⟨0,x₁⟩,…,⟨n−1,xₙ⟩}`.
  Isabelle's currying, `i ⇒ (i ⇒ i)`, is not available — its value would be a
  class, and a class is no member — so arity `n` is always ONE tuple.
- **One atom at every arity**, `pmem` on a tuple. No arity-indexed predicate, no
  position, nothing to permute.
- **A constant is a closed meta function** (R7), its graph a class function on
  tuples; a λ is a wrapper, its class its body's, stated where it stands (S1); a
  meta-function variable is a class parameter that owes being single-valued, its
  application read as Isabelle/ZF's `f`a` (S5).
- **Isabelle's own `⟨x,y,z⟩ = ⟨x,⟨y,z⟩⟩` is the OBJECT language's pair** — a value,
  translated like any constant — never the meta level's tuple (§3).

**The base is standard NBG, and what we use of it is PROVED.** §1's axioms are
Gödel's group B as Mendelson states it (*Introduction to Mathematical Logic*,
ch. 4); B6/B7 speak of Gödel's ordered triples, and those triples appear in those
two statements and inside the base proofs that consume them — NOWHERE above.
`function`, application, the tuple's EX, UNIQ, congruence and injectivity, the
table's lemmas, and §3's class existence over tuples are all THEOREMS of that
base. Nothing is admitted, so NBG's conservativity over ZFC (Novák 1950,
Shoenfield 1954) carries every one of them, and S6 needs no argument of ours.

**The tuple is PROVED** (`base/tiers/tuples`): a tuple grows by one entry at its
top index, `s = t ∪ {⟨n,v⟩}` — Isabelle's `cons(⟨c,b⟩, f)` at `c = n` — and
`fun_extend` holds in class form: a tuple on `n` so extended is a tuple on
`succ(n)`, with the new value at `n` and the old ones unchanged; the extension
exists, is unique, respects `eq`, and determines its prefix and its last value.
Isabelle discharges `c ∉ A` by Foundation; the base does not state Regularity, so
`n ∉ n` is carried instead as an INVARIANT of every index — `n` transitive and
`n ∉ n` — which the empty set has and `succ` preserves. No induction, no `ω`.

**The meta function is PROVED** (`base/tiers/metafun`), and with it the table's last
two rows. A class function on a domain `D` — the tuples on `n`, or every set — is
total and single-valued there. A λ is read at one scope layout, context `c` on
`p`, argument at `p`, result at `succ(p)`, and its class is class existence at
that layout (β); extracting the application atom gives back the function (η);
pointwise-equal class functions agree on `D` (`fun_extension`); and `f ≡ g` with
`t = t′` gives `f(t) ≡ g(t′)` (`combination`).

**Deleted from `base/` (2026-09-29)**, because each built or used the nested
tuple: `witness`'s `tmem_at`; `s2s3`'s `tuple_*` and `pair_fn_*`; `pairs`'
`tuple_chain`; the tiers `steps` and `diagonal` (§3a's construction — `diagonal`
cited T1/T2/T4); the probes `tuple_lemma`, `expansion`, `compiler_b`,
`pair_flattening`. `tmem` itself survives only as the notation of B6/B7's own
statement.

---

## 2. The specification

Forced by §1. Not a preference.

**S1 — Terms become variables plus constraints.** The signature has no function
symbols, so the only terms are variables. `φ(f(x))` renders as
`∃v.(F(x,v) ∧ φ(v))`. Writing `ι v. F(x,v)` *extends* the target language with a
term-former; that extension is conservative only where the described object
provably exists and is unique — i.e. only where S2 is discharged.

**S1 IS PAID WHERE THE TERM STANDS, NEVER WIDER.** `θ(f(x))` is stated with
`∃r.(F(x,r) ∧ …)` AT THE ATOM where `f(x)` stood. A variable Isabelle binds
locally stays local, and no statement names a compound term or a λ globally,
which would close it over its locals and need a fresh name. Isabelle's
proof treats `f(x)` as opaque and this one treats `r` as opaque, so the
interiors correspond step for step. Where two forms of one term meet — a
hypothesis's and a conclusion's, a λ's body unfolded at its argument — EX and
UNIQ convert between them, and every function has both (S2). Where Isabelle
instantiates at a COMPOUND term — `ZAppt` at `⟨a,b⟩`, which the signature cannot
name — the recipe is `pair_ex`, `exists_elim` to a variable, instantiate at
that. It also DELIVERS the R3 guard, the existential carrying `set(·)`.

> **⚠ THIS PARAGRAPH SAID S1 IS PAID AT THE STATEMENT: `θ(f(x))` STATED AS
> `∀x r. F(x,r) → θ*(r)`, WITH `r` BOUND UP AT `x`'S BINDER.** That moves a
> variable out of the scope Isabelle gave it, and a λ's body unfolded at its
> argument puts `r` back at the atom — two formulas for one statement, to be
> reconciled at every such site.

**A λ IS A WRAPPER** (decided 2026-10-13; its class closed over its free variables,
2026-10-14). `λx⃗. φ` names nothing: its class is its body's, `{⟨x⃗⟩ : φ}` — a
function's `{⟨⟨x⃗⟩, r⟩ : r = b}` — stated by that definition where the λ stands, as
the class argument of the constant holding it; S1 names φ's own terms where they
stand inside it. That the class exists is §3 over the λ closed over its free
variables, `∀v⃗. ∃K. def(K)`: one statement per closed λ, proved once, and cited at
the variables the λ mentions — variables wherever it stands, so the citation
concludes the λ's own definition at its site. β is that definition at the
arguments: Isabelle stores `φ(t⃗)`, and the class is `φ`'s. Nothing is added to the
language; every class is §3's.

> **⚠ THE REFERENCE MADE A λ AN ANONYMOUS CONSTANT `L` THAT STATEMENTS NAMED**
> (2026-10-12). Isabelle stores the body at every application, so one statement
> held the λ in two forms — `L` in a class slot, the body where it was applied —
> joined at every atom. A wrapper has one form, its body's.

**AN EQUATION BETWEEN FUNCTIONS IS POINTWISE** (2026-10-17). At a function type
whose arguments are objects, `f ≡ g` is `⋀x⃗. f x⃗ ≡ g x⃗`: both sides applied, their
λs wrappers, no class named for the equation — so `abstract_rule` concludes its own
premise, and `reflexive`, `symmetric` and `transitive` are `↔`'s and `=`'s under the
binders. A λ is a class only where an object must stand: a constant's argument, a
class variable's instance. A function of classes, `λP. Ball(A, P)`, has no class —
its argument is no member — yet its equation is first-order, `∀K. F(K) ↔ G(K)`, `K`
a class. `combination` is the premise at the argument, then the argument's equation
substituted into the function: the formula recursion, and at each atom where the
argument stands membership's congruence — at a class argument, the equation at the
atom's arguments.

**⚠ THE GRAPH IS PER CONSTANT; THE VARIABLE INTRODUCTION IS PER SITE, AND AN
EARLIER WORDING HERE SAID "PER CONSTANT, NOT PER PROOF STEP" OF BOTH.**
Measured: **676,001 of 797,924** `AppT` instantiate at a
Const, Abs or App rather than a variable — **85%** of ⋀-eliminations carry the
expansion. What the boundary buys is not a shorter proof but a MECHANICAL one:
a fixed template, no search, and the guard arrives with it. The exception is a
proof that unfolds a definition and reasons about the described object itself;
no boundary work reaches that one (§4).

**AND IT IS WHY `eq_subst` HAS NOTHING TO DO.** Leibniz substitution earns a
kernel slot only for term DEPTH — rebuilding `f(g(a,c))` under `eq(a,b)`, which
no finite lemma set covers. With every term a variable an occurrence is always a
direct argument of an atom, so that recursion is EMPTY. What remains is the
formula recursion, which is the kernel's own `iff` and quantifier rules, and the
atom base case, which is S2's CONG — bounded by R7 at two positions per
constant, with the fixed part proved in `base/tiers/cong`. Retiring `eq_subst`
therefore shrinks the trusted base without relocating the work.

**A constant is named only at the object level** (decided 2026-10-11). Isabelle/ZF
has two levels. The object level is ZF's: its types are built from `i` and `o`
with `⇒`. The meta level is Pure's: `prop`, and a type variable of the empty sort,
which ranges over every type, `prop` included. Nothing leads back from `prop` to
`o` — `Trueprop :: o ⇒ prop` is the only crossing. A ZF constant whose declared
type stays at the object level denotes something in NBG: a set, a function or a
predicate on sets, given its class arguments (R4). It is NAMED — its graph, S2's
obligations, its body stated once and cited. A ZF constant whose declared type
mentions `prop` or a type variable is a META-LEVEL DEFINITION and is UNFOLDED from
its own definition at the use's type, as the logic's constants are. Two facts make
this the border rather than a choice:

- **No class position can hold one.** A class is owed where a predicate or a
  proposition is an argument, and no object-level constant has a `prop` domain. A
  type variable's constant is ONE constant at several types — `split` at `i`, at
  `o`, at `i ⇒ o` — which one name cannot denote.
- **Unfolding is sound for any definition; naming also needs the constant to
  denote a class, and a meta-level one need not.** `AC18 :: prop` closes its claim
  over class functions `B`, `X` with Pure's `⋀`; a class standing for it would be
  given by a comprehension quantifying over classes, which §3 does not compile.
  Unfolded, the claim is a plain statement: `∀A. set(A) → ∀B. … ∀X. …`, a class
  binder the target already has.

In the corpus the meta-level ZF constants are five: `split`, `qsplit` (declared
"for pattern-matching"), `MetaExists.ex` ("yields a proposition rather than a FOL
formula"), `L_Reflects` and the locale predicate `AC18` ("cannot be expressed
within the object-logic"). The export carries no sorts, so the declared type is
the evidence; within ZF a type variable is always of the empty sort, since ZF
writes `i` for its objects. The logic's constants (Pure, IFOL, FOL) are unfolded
by family whatever their type.

> **⚠ "UNFOLD WHAT TAKES A PREDICATE" IS NOT THIS BORDER, AND IT IS EXPONENTIAL.**
> A constant taking a class passes it on to others that take it again —
> ZF-Constructible's relativized `is_X(M, …)` pass `M` several times per level,
> the recursion combinators their `H` — so unfolding them multiplies copies along
> the definitional depth: one definition of five nodes became 260 million in a
> scan of the export's definitions (2026-10-11, no live handle). A name is what
> R5 buys; it is owed wherever a constant can be named.

> **⚠ UNFOLDING `ex` IN A PREMISE BINDS A PROPOSITION THERE.** `ex(P) ≡
> ⋀Q. (⋀x. P(x) ⟹ Q) ⟹ Q`, so a premise `REFLECTS[P,Q]` unfolds to a `⋀Q::prop`
> inside a premise — a truth-set variable, not a schema (§2 S4). That is Pure's `⋀`
> over `prop`, not this border: in a conclusion the same unfolding is a schema.

**S2 — Every constant carries EX, UNIQ, and — when it takes arguments — CONG.**
The three are claims about an `F` **that encodes a function** `f`, `F(x⃗,r)`
reading `f(x⃗) = r`. They say nothing about a predicate that encodes no
function, and are not instantiable at one: `elem` is not in scope here.

| EX | `∀x⃗. ∃r. F(x⃗,r)` | `f` is total |
|---|---|---|
| UNIQ | `∀x⃗ r s. F(x⃗,r) → F(x⃗,s) → eq(r,s)` | `f` is single-valued |
| CONG | `∀x⃗ y⃗ r. eq(x₁,y₁) → ⋯ → eq(xₙ,yₙ) → F(x⃗,r) → F(y⃗,r)` | `f` respects `eq` in its ARGUMENTS |

**Every quantifier above is `set(·)`-guarded and interleaved** (R3); the guards
are elided only to keep the shapes readable. They are emitted in that shape and
the kernel compares syntactically, so a consumer that drops one does not match.

Three properties of the shapes, each of which a reader has otherwise had to
recover from the generator:

- **CONG is SIMULTANEOUS in all `n` arguments**, not one slot at a time.
  Single-slot congruence is the specialisation, discharging the other equations
  with `eq_refl`; the converse composes `n` single-slot instances in a chain.
- **CONG is an IMPLICATION and the result slot `r` is FIXED.** It is not a
  biconditional — that is its symmetrisation, via `eq_symm`.
- **CONG is CONDITIONAL on arity.** A nullary constant has no argument to
  transport and owes none: `zero` owes exactly `zero_EX` and `zero_UNIQ`
  Read it off CONG's own shape above: at `n = 0` there are no equations to state,
  so the row degenerates. **16 of the 197 are nullary.** The claim needs no
  generator-side check — it reads off the shape. Ask the unit for the name; a
  templated `{rel}_CONG` cites a lemma that is not there.

Not audit findings — this is what "encodes a function" means. EX and UNIQ are the
price of S1's relational encoding; CONG is the price of `eq` being a *defined
predicate* rather than the logic's identity, which in FOL-with-equality would
make it a free logical axiom for every symbol.

**Why the list is three and not two: UNIQ at a composite CONSUMES CONG.** For
`G(x,r) := ∃t.(F(x,t) ∧ H(t,r))`, two derivations of `G(x,·)` pass through
*different* intermediates `t`, `t'`. UNIQ(F) gives `eq(t,t')`, but UNIQ(H) is
stated at a single `t` and cannot fire until CONG(H) transports `H(t',r')` to
`H(t,r')`. Kernel-checked: `compose_uniq` in `base/tiers/s2s3` takes exactly
`UNIQ(F) → UNIQ(H) → CONG(H) → UNIQ(G)`. This is a **dependency, not an
entailment** — CONG does not by itself yield UNIQ, and an earlier wording here
("CONG implies UNIQ") read as though it did.

**Multi-argument application factors through ONE TUPLE, so the induction never
needs an n-ary composition.** A function is **unary**: `h(a,b)` denotes `h(t)` with
`t` the tuple of `a`, `b` (R7), and the relation S1 emits is that unary one. So a
body `f(x) = h(g₁(x), g₂(x))` — which reads as a **tree** over two independent
intermediates, and which no single-intermediate fold reaches — is **linear** the
moment the tupling step is written down:

```
  P(x,t)    ↔  ∃t₁ t₂. (G₁(x,t₁) ∧ G₂(x,t₂) ∧ tup(t₁,t₂,t))
  F(x,r)    =  ∃t. (P(x,t) ∧ H(t,r))
```

and that last line is exactly `compose_*`'s shape at `[F(2), H(2)]`. The
introduction is **definitional**, so §10's G1 admits it always with content zero,
and every obligation lands on the TUPLE's lemmas — proved from the base (§1a):

| | |
|---|---|
| EX(P) | EX(G₁), EX(G₂), the tuple's EX |
| UNIQ(P) | UNIQ(G₁), UNIQ(G₂), the tuple's UNIQ |
| CONG(P) | CONG(G₁), CONG(G₂), the tuple's congruence in its entries |
| `H` | already unary on the tuple (R7); reading `H(t,r)` back as `φ_H(a⃗,r)` is the tuple's injectivity — a function determines its values |
| arity `n` | the same step with one tuple of `n` entries — no iteration, no nesting |

> **⚠ THIS PARAGRAPH FACTORED THROUGH KURATOWSKI PAIRS** — `kpair(t₁,t₂,p)`, a
> helper `H_t` to take the pair apart again, and "iterated pairing" with
> `tuple_chain` beyond arity 2. That is the nested tuple §1a rules out. The
> pairs lemmas of `base/tiers/pairs` are what the tuple's lemmas are proved FROM,
> not the tuple's lemmas themselves.

> **⚠ AN EARLIER READING OF THIS ASKED FOR A COMPOSITION FAMILY INDEXED BY
> ARITY** — `compose_{ex,uniq,cong}₂` at `[G₁(2), G₂(2), H(3)]`, with wider
> instances beyond it. **Nothing of the sort is needed, and asking for it would
> have added a primitive the mathematics does not use.** The error was reading
> the *encoding*, where `H` occupies three argument slots, instead of the
> *mathematics*, where `H` is a unary function on a pair. Arity in the encoding
> is a presentation detail; the induction runs on the unary reading, and pairing
> is already primitive with EX/UNIQ/injectivity proved.

**A CONSTANT FUNCTION IS ITS VALUE, and that is what collapses the remaining
branches.** S5 sends a meta-function argument to a class, so `Sigma(A, λx. b)`
emits a class argument `C` even when `b` does not depend on `x`. But then

```
  φ_C(x,y)  ⟺  eq(y, b)          the domain slot never occurs
  C         =  { ⟨x,y⟩ : y = b }  the graph of λ_. b, determined by b ALONE
```

so `F(A, C, r)` is a function of the two **sets** `A` and `b`, not of a class.
Building its graph at that use site is R4's own prescription — the class argument
is concrete — and by the paragraph above a binary set operation is unary on
the tuple of `A` and `b`. `Sigma(A, λ_. b)` is `A × b`, and nothing about it needs a class.

The test is an **occurrence check, not a name**: the domain slot of the tuple does
not occur free in φ. Isabelle happens to name such a binder `uu_`, and that is
corroboration only — matching on the name would be a list of names pretending to
be a rule.

*Consequence, measured* (**the figures below are UNEVIDENCED — the measurement
went with the encoder and has no live handle.** A structural
proxy counts every vacuous `λ` in a body at **75 across 58 constants**, which is a
strict SUPERSET: §2 counts only those in a class-ARGUMENT position, and telling
them apart needs the S5 analysis, not an occurrence check alone): the refusal is **TWO**
constants, not eight — `Sum.sum` and `QPair.qsum` — and both block at
**`cons(_v0,_v1,_v2)`**, not at `Un(_v4,_v10,_v11)`, which this section named
until the refusal was printed and read. Fifteen constant-function classes sit
across ten constants, and **`Sum.sum` and `QPair.qsum` carry NOTHING ELSE.** Collapsing those classes to their values makes
each blocking step a binary set operation, which one tuple makes unary, which the
existing `compose_*` at `[F(2), H(2)]` composes. So the eight are **one**
treatment: recognise the degenerate class, collapse it, tuple, compose. No new
schema, no new admission, and no arity index anywhere.

> **⚠ THIS PARAGRAPH HAS BEEN WRONG FOUR TIMES AND EACH ERROR HAD ONE CAUSE:
> READING THE ENCODING INSTEAD OF MEASURING THE BODIES.** The fourth: it named
> `Un` as the blocking step and "eight" as the count; printing the refusal gives
> `cons` and two. **Print the refusal. Do not describe it.** It said the obstruction
> was chain DEPTH — it is not, none of the eight is merely long. It then asked
> for a composition family `compose_{ex,uniq,cong}₂ [G₁(2), G₂(2), H(3)]` indexed
> by arity — not needed, because a function is unary and multi-argument
> application factors through pairing. It then said six of the eight were a
> *different* shape because their second intermediate feeds a class rather than
> the step — also wrong, because that class is the graph of a constant function
> and is really a set. Three readings of argument SLOTS; one measurement of the
> φ's would have settled it each time.

**S3 — The obligations reduce by definitional order.** Isabelle introduces
constants in order, so EX/UNIQ/CONG propagate by induction. Three base cases:

- **primitive constants** are NBG's own notions, *defined*, each with EX and
  UNIQ proved. `Inf` is axiomatised in Isabelle by a property many sets have,
  `0 ∈ Inf ∧ ∀y∈Inf. succ(y) ∈ Inf`, so it is defined as the LEAST such set:
  unique by Extensionality, existing by Infinity and Separation over the class of
  sets in every inductive set (`base/tiers/inf`). Every Isabelle proof about
  `Inf` uses only the axiom, which the least set satisfies. Emitting `∃r. C(r)`
  without UNIQ is strictly weaker and does not name a constant at all.

  > **⚠ THIS SAID A PRIMITIVE IS *INTRODUCED*, `∃!r. C(r)` ADMITTED BECAUSE
  > `⊢ ∃x. φ(x)`.** Existence does not license uniqueness, and `base/` admitted
  > `Inf` by Skolemisation: an axiom outside the 19, against R1.
- **definite descriptions** are total and single-valued *provided* the
  `∅`-default is present; a bare Hilbert `ι` loses totality. **`The` is not one
  of these**, and an earlier version of this list said it was. Isabelle *defines*
  `The(P) ≡ ⋃{y . x∈{0}, P(y)}`, so it reduces through `zero`/`cons`/`Replace`/
  `Union` by the induction step like any composite, and the `∅`-default is
  *delivered* rather than assumed — `Replace` filters to the single-valued case
  and `⋃∅ = ∅`. §11's measured table bottoms out in five primitives and `The` is
  not among them. **Now evidenced:** `ZF_Base.the_def` is serial 1928, and `The`
  is one of the 197 with arity 1 and dependencies exactly
  `{Replace, Union, cons, zero}`.
  **`docs/phase2_probes/zf_fst_conv_e2e` TOOK THE OTHER ROUTE** — "tier 6's `The`,
  with the empty-set default" — and has been DELETED as a relic. Under S3 `fst`
  needs no bespoke `qfst`/`ufst`/`fstrel` chain: it reduces through `The`, whose
  four dependencies are already in the induction.
- **recursion** needs the recursion theorem, which routes back to `The`.

**S4 — A proposition is an object only as its truth set, `{t : t = ∅ ∧ φ}`** (decided
2026-10-15, the user; the rest of S4 is read through it).
`o` is not `i`, and a set standing for a proposition's truth by being nonempty is
necessarily non-unique: such a reification can never satisfy UNIQ, and
`ι v. Prop(args,v)` denotes nothing. That stays refused.

A predicate of `n` arguments is the class of its argument tuples (R7). At `n = 0` the
only tuple is the empty one, `⟨⟩ = ∅`, so a proposition `φ` is its **truth set**
`E(φ) = {t : t = ∅ ∧ φ}`, and `φ` holds iff `∅ ∈ E(φ)`.
- It is a set: `E(φ) ⊆ {∅}`. It is unique by extensionality, two truth sets with the
  same truth having the same members. It is not a chosen representative: it is the
  arity-0 case of the class of argument tuples every predicate already is.
- It exists for every `φ`, by cases: `{∅}` if `φ`, `∅` if not. That is excluded
  middle, not comprehension, so predicativity never arises at arity 0.
- β is a proof step, `∅ ∈ E(φ) ↔ φ`, from its defining property and `∅`'s.
- It is read only through `∅ ∈ E`, which is equivalent to `φ`. Its guard `E ⊆ {∅}` and
  its place in an argument tuple say what it is; nothing is stated of a truth set beyond
  its truth.

**Two kinds of proposition variable, two renderings** (decided 2026-10-15, the user,
over one rendering for both). A proposition variable is at `o` or at `prop`: the target
writes both as formulas, `Trueprop` the crossing, so both kinds hold at either type —
`OFCLASS`, `&&&`, `TERM` and `ex` bind theirs at `prop`.
- **A schematic variable** — a `⋀P` a statement binds at its top, which Isabelle
  instantiates by substitution — is a **schema letter** `A(0)`, as the arity-0
  paragraph below has it.
- **A bound variable** — a `⋀P` inside a proof or a formula — is a **truth-set
  variable**: `⋀P. θ(P)` renders `∀E. E ⊆ {∅} → θ*(E)`, `P` renders `∅ ∈ E`, and an
  instance at `φ` is the instance at `E(φ)`, then β.
- Why two: substitution is what a schema letter's instance costs the kernel, one
  `schema_inst`. Read as a truth set, each instance proves its substitution — the
  class named, its instance, β over the instantiated statement, about twenty steps.

**Its consequences, each a rendering where S4 had none.**
- A proposition as a constant's argument (`If(φ, a, b)`) or a constant's value
  (`AC1 :: o`) is its truth set, a set entry of the argument tuple (R7).
- A function of propositions, `o ⇒ …`, is a class of tuples of truth sets; an equation
  between two, `f ≡ g` at `o ⇒ o`, renders `∀E. E ⊆ {∅} → (f*(E) ↔ g*(E))`. Applied to
  truth sets, a function of propositions is its body with each argument read `∅ ∈ Eᵢ`,
  `(λP⃗. φ)*(E⃗) = φ[∅ ∈ E⃗]`: a λ is a wrapper (S1), and no class is named for an equation.
  At `o⃗ ⇒ o` the equation is pointwise in every argument, `∀E⃗. E⃗ ⊆ {∅} → (f*(E⃗) ↔ g*(E⃗))`.
  `combination` instantiates it at its argument's truth set, then β: `f*(E(a)) ↔ f(a)`,
  `∅ ∈ E(a)` replaced by `a` under `f`'s connectives — the replacement an instance's
  twenty steps already count.
- `OFCLASS(T, c) ≡ ⋀P :: prop. P ⟹ P` binds a proposition inside a formula and
  renders `∀E. E ⊆ {∅} → (∅ ∈ E → ∅ ∈ E)`: true, and stated.
- **The logic's primitive rules are the kernel's own**: an application of one of
  IFOL's or FOL's inference rules (`conjI`, `mp`, `spec`, `exE`, …) is the kernel's
  step at its premises, never a substitution into a translated rule.

> **⚠ THIS SECTION SAID "PROPOSITIONS ARE NEVER REIFIED … NOT REPAIRABLE BY CHOOSING
> A CANONICAL TRUTH-VALUE SET — THAT MANUFACTURES STRUCTURE THE MATHEMATICS DOES NOT
> HAVE".** The truth set is not chosen; it is every predicate's own reading at arity 0,
> unique, and read only by `∅ ∈ E`. Without it, a proposition bound below a
> statement's top had no rendering, and the translation substituted, consumed or
> dropped each one where it was used — three rules reading a neighbouring node
> instead of their own piece. A concrete `i⇒o` argument is a class (S4's arity ≥ 1
> paragraph, below), never β-substituted.

**⚠ THIS SECTION IS ABOUT ARITY ZERO, AND USED TO SAY `?P` STAYS A SCHEMA AT
EVERY ARITY.** At arity ≥ 1 a schematic `?P` is a CLASS VARIABLE: `P x` renders
`t ∈ A`, `t` the tuple of its arguments — a 1-tuple at arity 1, as R7 reads every
arity (decided 2026-09-29; `elem(x,A)`, the value itself, is a later size
optimisation) — and `⋀P. θ(P)` renders `∀A. θ*(A)`. The class is allocated
lazily at the first application, so the body renders BEFORE the binder is
written, and the binder is **UNGUARDED** — guarding a class would make the claim
false, not redundant — a quantifier the target
already uses, `axioms.fol.def`'s B2 being `forall A. forall B. …`. Nothing is
admitted (R1), no class `{x : P(x)}` is ever formed, and this IS R2's "proved
parametrically" stated in the object logic instead of in schema machinery, so
the kernel checks it rather than discipline. Instantiation is then §3 compiling
the concrete φ to a class — and §3 has no case for a class quantifier, which is
where predicativity is enforced.

**At arity 0 a schematic `P :: o` is a SCHEMA LETTER `A(0)`** (decided
2026-10-01). A statement binding propositions — `conj_cong`, `imp_cong`,
`iff_cong` — is a schema, proved ONCE from its own proof with its letters
uninterpreted, and each use instantiates it. Nothing is reified: a letter stands
for a formula, never for an object, so this is not the truth-value set refused
above, and R2 holds because a proof over uninterpreted letters is parametric by
construction. The `⋀P::o` of IFOL's primitive rules (`disjE`, `exE`) stay the
kernel's own ND rules. A variable of a type built over `o` — a function of
propositions, `o ⇒ o` — takes no letter: no letter takes a proposition as its
argument. Bound, at a statement's top or below it, it is a class of tuples of truth
sets (S4's first paragraphs), a class variable as at arity ≥ 1.

> **⚠ THIS SAID "THE CORPUS BINDS NONE AT A STATEMENT'S TOP".** It held of the named
> theorems. An unnamed theorem a proof cites is a statement too when it binds a
> proposition, and seven of those bind a function of propositions besides — each
> deriving a defined connective's applied definition, the constant a variable.

> **⚠ THIS SECTION SAID "AT ARITY 0 THERE IS NO SUCH RENDERING AND NONE IS
> WANTED", AND THAT "A SCHEMA FORCES A PROOF PER INSTANTIATION".** The second is
> false of the target — a schema is proved once and instantiated — and the first
> left every proposition-binding lemma to be re-proved inside each of its uses.

**S5 — Set-valued meta-function arguments compile to classes**, then to sets by
Replacement where the domain is a set. No graph is ever passed as an argument.
`f(x⃗) = r` becomes a lookup in a class parameter — `apply(t, r, C)`, `t` the n-tuple
of `x⃗` (R7) — and `C` owes being single-valued. **One atom at every arity**: there
is no arity family, and no arity refuses.

**A function variable owes single-valuedness, and its application reads as
Isabelle/ZF reads `f`a`** (decided 2026-10-14). `apply(t, r, C)` holds when
`⟨t, r⟩ ∈ C`, and when `C` has no value at `t` and `r = ∅`: `⋃(f``{a})`,
Isabelle/ZF's own application, in class form. A quantifier over `f` is relativized
to `function(C)`, `C` single-valued — Isabelle/ZF's `function`, of a class — which
carries no arity, since a function is its pairs. Faithful: every single-valued `C`
read through `apply` is a total function on sets, and every Isabelle function is
such a `C`, so `∀C. function(C) → θ*(C)` holds iff `⋀f. θ(f)` does. Every
application has a value with no guard (`apply_EX`), and only one under it
(`apply_UNIQ`), both proved once in `base/tiers/metafun`. A constant's application
stays plain membership, `pmem(t, r, C)`: a constant is total on its tuples by its
definition, and so is a λ's class (S1).

> **⚠ THIS SAID `C` OWES BEING A FUNCTION ON n-TUPLES** — total there, which needs
> the domain at every binder: a class of the n-tuples, or the numeral `n` (the
> reference's `Func(F, n)`, and its two clauses written out). Totality moved into
> the application's default, as Isabelle/ZF's own `f`a` has it.

> **⚠ THIS SAID `pmem(x,r,C)` AT ARITY 1, `tmem(a,b,r,C)` AT ARITY 2, "`elem`/
> `pmem`/`tmem` ARE THE WHOLE VOCABULARY" AND "ARITY ≥ 3 REFUSES".** `tmem` put the
> arguments in a nested triple, so each arity needed its own membership predicate
> and the list had to stop somewhere. With the arguments in one tuple, `pmem` is
> the only lookup there is.
*Side condition:* class parameters may never occur to the **left** of `∈`. A
reified graph used as a **value** is a member, hence outside the theorem — those
sites must be eliminated, not derived.

**S6 — Quantifiers are relativized to `set(·)`,** descriptions included.
Conservativity is `NBG ⊢ σ* ⟺ ZFC ⊢ σ`, stated for the *relativized* `σ*`; an
unrelativized `∀x. φ` quantifies over classes and is not the Isabelle theorem.
Harmless only while the class apparatus is inert — and §3 is what ends that, so
relativization is a precondition of §3, not later cleanup. **§1 R3 is S6's
enforceable form**, and fixes the guard *shape*, which S6 alone leaves open.

---

## 3. Class existence, mechanised

**A class context is an ASSIGNMENT — a function from an index set to V — not a
tuple of positions.** This section states that foundation. It is a change, and
§3a records what it supersedes.

### Why position-indexing is not available here

For `∈` to apply, a tuple must be one set, so a foundation must inject
n-sequences of sets into sets. Iterated Kuratowski pairing is the classical
choice, and under it a coordinate is a *position in a nesting*. Eliminating the
**last** coordinate is one operation; eliminating or introducing an **interior**
one is not — it needs permutation, and permuting an n-nesting is generated by
transpositions whose statements differ with depth. There is no single
permutation operation.

Gödel's construction escapes that by **controlling the coordinate order**: build
over the variables canonically, always eliminate the last, always introduce at
the front as one opaque block. Interior access then never arises.

**That escape has a precondition this project cannot meet.** Our formulas come
from Isabelle terms: a constant's free variables are its arguments *in
Isabelle's order*, and reordering them names a different constant (R7); the
quantifier structure is the term's own. **The source owns the coordinate order.**
With the order imposed from outside, the canonical discipline is unavailable,
interior access is unavoidable, and position-indexing then forces a placement
law per (arity, position) — new mathematics at every width.

So the encoding must index by a **set**, not by a position. Not for elegance:
because we do not own the order.

### Assignments

An **assignment** is a set `a` with `function(a)` — single-valued, so `a(i)` is
well defined — together with an index set `dom(a)`. Application is relational:

    app(a,i,v)  :≡  ⟨i,v⟩ ∈ a

`function`, `dom`, restriction `a↾S` and `app` are **definitional predicates**
over `∈` and pairing — `P(x⃗) ↔ body`, content ZERO. Nothing is admitted.

**Variables are NAMED, not positioned.** There is no order on an assignment, so
**no permutation operation exists** — the permutation problem is not solved, it
ceases to arise. That is the substantive gain, larger than uniformity of laws.

### Indices, and why they are not a family

Indices are provably-distinct sets. **Distinctness is the only property
required** — no order, no arithmetic, no finiteness, no `ω`.

Take the von Neumann naturals as *terms*, and eliminate quantifiers in REVERSE
index order. Removal is then structural — no disequalities arise at all:

    I = n = {0,…,n−1}        succ(m) \ {m} = m        ONE lemma, needing m ∉ m

So index management costs **O(n) steps and O(1) lemmas**. It does not reintroduce
the family this section exists to remove.

**⚠ AN EARLIER DRAFT SAID O(n²), ASSUMING PAIRWISE DISTINCTNESS.** That is only
needed if removal must know the removed index differs from every survivor, and
under reverse-order elimination it does not. Indexing to make elimination
reverse-ordinal is always possible: φ's quantifier nesting is a total elimination
order, so the innermost-eliminated variable takes the highest index and a
constant's k-th argument takes index k.

**This is why the change is more than uniformity.** §3a's "B4 drops the last
component" was a NECESSITY — the discipline that made position-indexing
survivable, and it constrained where an atom could touch. Here the same
discipline survives as a CONVENIENCE for `∃`, and constrains nothing about which
indices an atom reads. Cheap elimination for quantifiers, free access for atoms.

### Why this costs anything at all — it is SHIFTING, moved into proof

The first question anyone asks is why a bookkeeping fact needs proving when
Isabelle proves nothing of the kind. The answer is not that Isabelle gets a free
lunch.

Isabelle stores bound variables as **de Bruijn indices** — `λx. λy. f x y` is
`λ. λ. f 1 0`, with no names. So "these two variables differ" is integer
inequality: **decided, not proved**. The invariant is maintained by
capture-avoiding substitution, which does index **shifting** on every
instantiation — O(term size), as COMPUTATION, inside the trusted kernel.

We cannot copy that, because a class's members must be sets for `∈` to apply, so
the variable context must be **reified into the domain of discourse**. Once a
context is a set, variable identity is *set* identity — a proposition, and
propositions need proofs. **Reification is what turns decided facts into proof
obligations.**

But the position-indexed construction (§3a) reifies too, and pays nothing for
distinctness. That is not an advantage it has; it is the same trade struck the
other way:

| | nested pairs (§3a) | set indices (§3) |
|---|---|---|
| analogue | **de Bruijn** | **named variables** |
| distinctness | free — structural | a proposition |
| interior access, reordering | expensive — this IS the placement family | free |

A coordinate in `⟨⟨x,y⟩,z⟩` is a nesting depth: structural, decided by syntax,
exactly a de Bruijn index — with exactly de Bruijn's weakness, that interior
access requires shifting. **The placement family was never anything but shifting
under another name.**

So the design decision is the classical **de Bruijn versus named-variables**
tradeoff, reified into set theory. Isabelle does not escape the cost; it pays it
as computation in trusted code rather than as proof steps in the artifact. Ours
is auditable, theirs is trusted — the same work in a different currency.

**And that is why the cost is O(n) rather than O(n²).** Reverse-order elimination
keeps quantified indices under a STACK discipline, which is the condition that
makes de Bruijn cheap, while atoms read any index directly, which is what named
variables are for. By analogy with the binder literature the arrangement is
**locally nameless**: de Bruijn where it costs nothing, names where they buy
something. We reached it by pushing on cost rather than by picking it, which is
some evidence it is the right point in the space rather than a compromise.

### The construction

**A subformula's assignments range over the variables IN SCOPE at it**, numbered
`0, 1, …` in the order they come into scope — the free variables first, then each
bound variable where its quantifier is reached. The domain is then always
`{0,…,k−1}`, the natural number `k`. For `φ` with `k` variables in scope, derive

    ∃C. ∀a. ( a ∈ C  ↔  tuple(a, k) ∧ φ*(a) )

where `φ*` is `φ` with the variable of index `i` replaced by `a(i)`, relationally.
The map `φ ↦ φ*` is META-level and is specified in §2. Each row below is a claim
of `base/tiers/classes`, and each is EXACT OVER EVERY SET — the domain is imposed
once, at the top, by intersecting with the class of tuples on `k`.

| φ | operation |
|---|---|
| `x ∈ y` | `{a : a(i) ∈ a(j)}` — `i`, `j` the indices of `x`, `y` |
| `x = y` | `{a : a(i) = a(j)}` |
| `x ∈ Y`, `Y` a class parameter | `{a : a(i) ∈ Y}` — S4's `P(x)`, with `a(i)` the argument tuple |
| a graph atom `G(x⃗, y)` | `{a : ⟨a(i), a(j)⟩ ∈ G}`, `a(i)` the ARGUMENT TUPLE — a variable the formula binds by its own tuple formation, `∃t. t = ⟨x⃗⟩ ∧ ⟨t,y⟩ ∈ G` (R7, §1a); ONE row at every arity |
| `φ ∧ ψ` | intersection — B2 |
| `¬φ` | complement — B3 |
| `∃y. φ` | `y` came into scope last, so its index is `k`: `{a : ∃v. a ∪ {⟨k,v⟩} ∈ C_φ}`. It removes the LARGEST index, always — one fact, `(k+1) ∖ {k} = k`, covers every removal |
| the domain | `{a : tuple(a,k)}`, intersected once |

> **⚠ THIS TABLE PUT `dom(a) = k` IN EVERY ROW AND BUILT THE GRAPH ATOM AS
> `⟨a∘ι, a(j)⟩ ∈ G`**, the assignment composed with an index map. A row exact over
> every set is simpler and loses nothing — the invariant is claimed only for tuples
> on `k` — and composition needs its own class; binding the argument tuple as a
> variable makes the graph atom a class atom on two indices.

No row aligns, widens or permutes. That is what replaces T1/T2/T3/T4,
B5/B6/B7-as-composed, and every arity-indexed placement law.

**An atom is read as membership of its entries in its WITNESS class**
(decided 2026-10-15). `x ∈ y` is `⟨x, y⟩ ∈ E`, E B1's class; `x = y` is membership
in the diagonal; the tuple formation's atoms — `t` empty, `n` the successor of
`m`, `s` the tuple `t` with index `n` set to `v` — are membership of one, two and
four entries in their classes, each built once from B1–B7 (`base/tiers/classes`).
A class parameter `Y` is its own witness. So the table's atom rows become one per
WIDTH, a record's one, two or four entries read into ANY class, and membership's
congruence, proved once inside those three, is the only congruence the
construction uses: no atom carries its own.

> **⚠ THIS TABLE HAD A WIDENING ROW, `{a : dom(a) = J ∧ a↾I ∈ A}`**, with each
> subformula over only the variables it MENTIONS — so `x ∈ y` and `y ∈ z` had
> domains `{0,2}` and `{1,2}`, `∧` had to widen both first, and removing an
> index from an arbitrary finite set needed indices proved distinct. Over the
> variables in SCOPE none of that arises. Widening would only let a subformula
> under two different scopes share one class — an optimisation, never a need.

**Every row is a THEOREM, proved from §1's axioms — never an axiom.** Each is an
instance of NBG's class existence theorem (its right side quantifies over sets
only), so NBG proves it and nothing is added to what NBG says; that is why the
base stays standard (§1a). Gödel's triples appear in B6/B7 and inside these
proofs, and nowhere above them.

The rows are the operations of a **cylindric set algebra** (Henkin, Monk, Tarski,
*Cylindric Algebras* I 1971, II 1985) — a formula as the set of assignments that
satisfy it, `∃y` as cylindrification in `y`, the atom as a diagonal element with
`∈` for `=`. The algebra is textbook; using it as NBG's class existence is ours.

**Decided (2026-09-29): the variables in scope, not one dimension.** A cylindric
set algebra fixes ONE index set for every assignment, typically `ω`; that also
needs no widening, but makes every assignment infinite — Infinity in every class
construction — and its `∃` rewrites an arbitrary index instead of removing the
last. The scope rule keeps every domain a natural number and every removal at
the top.

**These assignments are the META level's, and serve only the encoding.**
Isabelle/ZF has its OWN theory of tuples and environments — `pair`, `func`'s
`n → A`, `List`'s `nth`, ZF-Constructible's `sats(A, p, env)` over
`env ∈ list(A)` — and that is object-language content, translated like any other
theory. The two are never identified, as an Isabelle pair is never an assignment.

### What this does NOT remove

**Per-formula generation stays.** Class existence is a theorem *schema*; its
proof is still built by induction on `φ`'s structure, so one proof is generated
per class. What the assignment foundation removes is the arity-indexed *lemma
family* each step used to need — every step now cites uniform lemmas. Codegen
remains; families go.

**Isabelle's own pairs stay Kuratowski.** `Pair`/`Sigma` are terms in the source
and their translation must be what Isabelle means. **An Isabelle pair is a VALUE
inside an assignment, never an assignment.** Conflating the object language's
pair with the compiler's context is what forced position-indexing in the first
place, and keeping them apart is the discipline this foundation rests on.

### Obligations, restated

| rule | under assignments |
|---|---|
| **R1** | `function`/`dom`/`app`/restriction are definitional, content zero; the 19 are untouched |
| **R3** | assignments are sets; every quantifier over one carries its guard |
| **R4** | every value in an assignment's RANGE is a set, and the index set is a set |
| **R5** | a k-ary constant's graph is a class of assignments over its argument indices plus a result index |

### The base stays 19 — and asking to shrink it was the wrong question

**⚠ AN EARLIER READING HELD THAT B6/B7 MIGHT BE UNNECESSARY UNDER ASSIGNMENTS,
"SO THE BASE IS 17 AND R1 STRENGTHENS". THAT IS WRONG IN BOTH HALVES.**

R1 forbids *admitting* beyond the 19; nothing in it rewards removal. A smaller
base is better only if it still does the job, and **the job is a named theorem:
B1–B7 exist to derive CLASS EXISTENCE.** That theorem must handle an atom
relating ARBITRARY coordinates among n variables, which needs the full symmetric
group on coordinates. B6 gives the rotations — the EVEN permutations only; B7
supplies an odd one. Drop it and the induction has cases it cannot discharge.

That reaches us through S6. Conservativity's **⟸** direction — `ZFC ⊢ σ` implies
`NBG ⊢ σ*`, the direction that lets an Isabelle theorem be translated at all — is
proved THROUGH class existence: build `{x : φ(x)}`, then NBG's single
Separation/Replacement apply to it, recovering ZFC's schema instances. Break
class existence and theorems we need become UNPROVABLE — not unsound, but failing
on some particular constant arbitrarily far from the cause.

The count is not canonical (presentations of NBG use four, seven, or eight class
axioms). **The invariant is that the set derives class existence, and any change
carries that as a proof obligation, not an observation.**

**The atom is BUILT, and every row with it** (`base/tiers/classes`, kernel-checked
from B1–B7). The question this section left open — does dropping `u` and `v` from
`a(x) ∈ a(y)` force a nested-pair intermediate? — has the answer **yes, and only
there**: B4 consumes a class of PAIRS, so the proofs build classes of triples
`⟨⟨a,u⟩,v⟩` with Gödel's own operations (B5–B7), and drop `v`, then `u`. Those
triples live in the toolkit lemmas and their proofs — the same place B6/B7's live —
and in no row's statement: every row is stated over assignments, with no
position and no arity.

Two moves keep the toolkit small, and they are the ones worth repeating:

- **B1's `E` read at a pair is application.** `⟨⟨i,y⟩,a⟩ ∈ E` says `⟨i,y⟩ ∈ a`,
  i.e. `a(i) = y`; one B6 rotation gives the class `{⟨⟨a,i⟩,y⟩ : a(i) = y}`. No
  diagonal and no pairing class is needed for it.
- **A pair in the first slot is one set.** A triple `⟨⟨b,y⟩,z⟩` whose `b` is itself
  a pair `⟨a,i⟩` lets the pair- and triple-level operations act on four variables
  with no new placement law — T1, "prepend", never arises.

What is NOT in doubt: `a ∈ C` is plain `elem`, so **`∧` is B2 and `¬` is B3
DIRECTLY** — no pair lifting. The tier that lifted them to `pmem`, §3a's, is
deleted.

### The one open cost — MEASURED, and access does not dominate

Position-indexing pays for coordinate *manipulation*; assignments pay for
coordinate *access* — every variable occurrence becomes an existential. Which
dominates is a property of the CORPUS, not of this derivation.

*Measured* over the 197 term-constant bodies:

| | |
|---|---|
| ACCESS — `i`-variable occurrences | **487** |
| atoms — 100 `elem`/`eq` + 1073 constant applications | 1173 |
| PLACE — context width summed at each atom (§3a's `n − i`) | **1712** |
| WIDEN — `i`-binders | 394 |
| max FULL context width (arity + binders) | **9** |

**Access is 0.28× placement.** Assignments win on this corpus by roughly 3.5×,
so the cost §3 could not predict falls the way §3 needed. Both figures carry
unknown constant factors — an occurrence costs `app` + `∃` + a B4 elimination, a
placement costs one T-step — so read the ratio, not the absolute numbers.

**⚠ ONLY 100 OF 1173 ATOMS ARE `elem`/`eq`.** Bodies are COMPOSITIONS of earlier
constants, not raw set theory — which is R5 working, and it is why the atom count
looks impossibly low for a set-theoretic corpus. Anything that unfolds bodies
inline destroys this and the measurement with it.

**⚠ THE PLACEMENT FAMILY WAS BOUNDED, AND THIS SECTION IMPLIED IT WAS NOT.**
"New mathematics at every width" reads as unbounded; the corpus tops out at
**width 9**, median 3–4. So §3a needed a finite family, not an infinite one. That
does not overturn the argument — a bounded family of tens of laws is still a
family against §3's one — but the case for §3 rests on interior access and on the
source owning the coordinate order, NOT on the family being infinite.

---

## 3a. The superseded construction — WHAT THE DELETED LAYER DID

**⚠ WRONG, NOT MERELY SUPERSEDED: ITS TUPLE IS A NESTED PAIR (§1a).** A variable
here is a position, which is what made T1–T4, `tmem` and every placement law
necessary. Nothing in it is to be rebuilt in any form.

**⚠ THIS SECTION USED TO BE TITLED "WHAT THE CODE STILL DOES" AND TO SAY "the
code realises the position-indexed construction below". BOTH WENT STALE WHEN THE
LAYER WAS DELETED, AND THE STALENESS ACTIVELY MISLEADS.** No code realises any of
it, and the three probes that encoded it — `tuple_lemma`, `expansion`,
`compiler_b` — are deleted too (2026-09-29): green, they answered "how is class
existence built" from here, kernel-verified, reading as current.

Read §3 for what must be true. Read this only for what the deleted encoder did.
**Do not build on T1–T4.**

Tuples left-nested, `(x₁,…,xₙ) = ((x₁,…,xₙ₋₁), xₙ)`.

**Tuple Lemma** — proved once; B5/B6/B7 then never composed directly again.

| T1 | `(z,x,y)∈B ↔ (x,y)∈A` | prepend | `circ(A×V)` |
|---|---|---|---|
| T2 | `(x,z,y)∈B ↔ (x,y)∈A` | insert before last | `transp(A×V)` |
| T3 | `(x,y,z)∈B ↔ (x,y)∈A` | append | `A×V` |
| T4 | `(y,x)∈B ↔ (x,y)∈A` | swap | `Dom(transp(circ(circ(A×V))))`, needs Empty |

A compound block substituted into **slot 1** flattens —
`((z₁…z_k),x,y) = (z₁…z_k,x,y)` — but in slot 2 or 3 it does not. So T1 fires
**exactly once**, while `A` is still a class of pairs; T2/T3 repeat with the
grown tuple in slot 1.

**Expansion** — from pairs `(xᵢ,xⱼ)` to `{(x₁,…,xₙ) : R(xᵢ,xⱼ)}`:
`1×T1 + (j−i−1)×T2 + (n−j)×T3`, with T4 first if `i>j`.

**Induction on φ:** atoms → B1 + Expansion; `∧`→B2; `¬`→B3; `∃`→B4, which drops
the **last** component. Expand `∨,→,↔,∀` first.

**⚠ THE IMPLEMENTATION ALSO ADMITS ATOMS OF ARITY > 2**, which this construction
does not specify: a class parameter applied to several context slots at once.
That is what makes a gap possible *inside* an atom, and it is the defect §3
removes — under assignments a class parameter applies to the assignment, which
is one object.

**The real risk is not permutations.** It is discharging `set(·)` through the
nested `Pair` chains the flattening builds: under
`⟨u,v⟩∈X := ∃p.(Pair(u,v,p) ∧ p∈X)` the flattening identity is syntactic, not
definitional. That is where a silent error can hide.

## 3b. The proof layer

§2 says what a STATEMENT becomes. This says what a PROOF becomes, and it is a
different axis: §2's obligations are discharged per constant, these per step.

**⚠ CITATIONS ARE NOT THE OBSTACLE, AND MEASURING THEM ANSWERS NOTHING.** `use`
translates any cited theorem whose STATEMENT is expressible, so the citation of
`fst_def` is free; what blocks is that `fst_def` SAYS `fst(p) ≡ The(…)` and
`fst(p)` is unnameable. Count statements, never citations.

### The rendering

Verbatim from tier 7's probe, which the kernel accepts:

    term  a : i        ->  unary  A(r)
    meta-fn f : i=>i   ->  binary F(x,r)
    a == b             ->  forall r. set(r) -> (A(r) <-> B(r))
    f == g             ->  forall x r. set -> (F(x,r) <-> G(x,r))
    f a                ->  exists t. (set(t) & A(t) & F(t,r))

### Pure's rules re-render — and that part is SETTLED, not open

`docs/phase2_probes/proof_layer.fol.def` states the nine as schemas and proves
them: `pure_refl`, `pure_symm`, `pure_trans`, `pure_equal_intr`,
`pure_equal_elim`, `pure_comb` (combination), `pure_abst` (abstract_rule), and
`appt_complex` / `appt_nested` — ⋀-elimination at a term the signature cannot
name. It is a CHAIN probe at tier 7 and the kernel accepts it. **`OK: 0
claim(s)` is the verified-schema case, not a vacuous run** (probes README).

`appt_complex` IS S1's boundary treatment, stated once and proved:

    EX(F)  ->  (forall y. set(y) -> Psi(y))  ->  (forall x. set(x) ->
               (exists v. set(v) & F(x,v) & Psi(v)))

So instantiating a universal fact at `f(x)` needs no new rule and no term — it
needs EX(F), which S2 already owes. `pair_ex` + `exists_elim` is its
specialisation at `kpair`.

### The proof-term mapping

| Pure | target |
|---|---|
| `AbsP` / `AppP` | `implies_intro` / `implies_elim` — one for one |
| `AbsT` / `AppT` at a VARIABLE | `forall_intro` / `forall_elim`, **plus the R3 guard step** |
| `AppT` at a compound term | `appt_complex` / `appt_nested` |
| `AppT` at a λ, a class type | `forall_elim` at the λ's class at its arguments — proved once per λ — then β: at each atom, the class's against the body's, EX and UNIQ where the argument is compound (S1); at `iⁿ ⇒ i` the guard by the class's own `function` (S5) |
| `Thm` | `use` |
| Pure's `reflexive`, `symmetric`, `transitive` at a function type whose arguments are objects | the value type's — `iff_*` at `o`, `eq_*` at `i` — under the pointwise binders |
| Pure's `abstract_rule` | its premise: `⋀x. f x ≡ g x` and `f ≡ g` are one formula |
| Pure's `combination` | the premise at the argument, then the argument's equation substituted into the function by the formula recursion, membership's congruence at its atoms |
| `Thm` of a theorem polymorphic in a type no class restricts, at a type binding no proposition on its spine | its proof at that type, in place: the target has no type |
| an application of a logical rule (`conjI`, `mp`, `spec`, `exE`, …) | the kernel's OWN step at its premises; never translated (S4) |
| `exI` at `P` and `a` | base's `ex_intro` at `P`, then `forall_elim` at `a`: an ∃-introduction given its body |
| an application of a definition whose constant is unfolded, `AppT` at its parameters | `reflexive` at its terms: the definiens at them on both sides, no binder introduced (S1) |
| `⋀P` over a proposition, `o` or `prop`, at a statement's top, `AppT` at it | a schema letter, `schema_inst` (S4) |
| `⋀P` over a proposition anywhere else, `AppT` at it | a truth-set variable; `forall_elim` at `E(φ)`, then β (S4) |
| a variable only the proof uses (`dummy_pattern`) | the witness of an `exists_elim` at the proof's top, below its letters, over its type's inhabitation |

**THE KERNEL'S ∃-INTRODUCTION FINDS ITS BODY; ISABELLE'S IS GIVEN IT.** From `φ` and a variable `a`, `exists_intro`
concludes `∃y. φ′`, where `φ′` binds every occurrence of `a` in `φ`. `exI` concludes `∃y. P(y)` from `P(a)`, its `P`
given. The two agree only when `a` occurs in `P(a)` just where `P` binds: from `x = x`, `exI` at `λy. y = x` concludes
`∃y. y = x`, `exists_intro` at `x` concludes `∃y. y = y`. So `exI` is no kernel step at its premises. It is the schema
`∀z. P(z) → ∃y. P(y)`, proved once by `exists_intro` at `z`, which occurs only where the letter binds, and instantiated
by `forall_elim` at `a`, which substitutes exactly; at a set binder `P` carries the guard, `set(y) ∧ φ(y)` (R3).
Nothing is admitted (R1).

**A VARIABLE ONLY THE PROOF USES IS SOME VALUE, NOT EVERY VALUE.** Isabelle's kernel instantiates at a free variable
its conclusion never mentions: every type is inhabited, so the proof proves the statement at any value of it. The
exporter writes each such variable as `dummy_pattern`, one per type, which is a substitution, and a proof stays a proof
under substitution. The target has no free variable: every variable a step uses is bound by a `forall_intro` or an
`exists_elim`. A `∀` over the proof concludes `∀h. φ`, not `φ`; what the proof needs is an element. So the variable is
the witness of an `exists_elim` over its type's inhabitation, at the top of its proof and below its letters, and the
conclusion, which does not mention it, stands. One witness serves every type: Empty gives `∅`, which is a set,
single-valued (it has no pairs), a class, and a truth set (`∅ ⊆ {∅}`), so each guard — R3's, S5's, S4's — is inhabited,
proved once in base from Empty, and nothing is admitted. A variable at a type beyond objects and propositions has no
reading as a variable yet, and so no binder.

**⚠ THE GUARD STEP HAS NO COUNTERPART IN THE PROOF TERM.** Isabelle gets `a : i`
from its type system — decided, never proved — so every `forall_elim` needs a
`set(a)` the proof term does not supply. Three sources, and only the third
costs: an enclosing guarded binder (in scope), a relationalized term (the
existential carries `set(·)`, so S1 DELIVERS it), or a constructor term (a
sethood lemma — `pair_set`, `upair_set`, already in `tiers/pairs`).

*Measured*: **676,001 of 797,924** `AppT`
instantiate at a Const, Abs or App rather than a variable, and 121,921 at a Free
or Bound. The expansion is per SITE. What the boundary buys is not a shorter
proof but a MECHANICAL one.

**A third category, and it costs nothing.** Two `AppT` slots hold neither — they
carry `IFOL.term` at a type variable, i.e. a SORT constraint (an OfClass
elimination), both in `IFOL/206`. R3 governs `i`-quantifiers; a sort constraint
is trivially true in ZF, where `term` holds `i` alone, so it needs no guard and no
boundary step. It is stated, never stripped: its definition, `⋀P. P ⟹ P`, is what
makes it true (S4).
**Two in 797,924 — but the census counts them SEPARATELY rather than folding them
into either side**, because a term-tag the lowering does not handle is exactly
the shape a silent mis-parse would take.

### Eligibility is a CLOSURE, not a property of one proof

**⚠ A RENDERING STATEMENT IS NOT ENOUGH AND READING IT AS ENOUGH OVERSTATES
PROGRESS BY 3.5×.** A proof replays only if every theorem it cites replays too,
so eligibility is the greatest fixed point over the citation graph, not a
per-theorem test.

*Measured*:

| | |
|---|---|
| statements | 16,798 |
| statement renders — necessary, not sufficient | **1,352** |
| …and its whole citation cone renders — ELIGIBLE | **393** |

`IFOL` 242 · `Pure` 80 · `FOL` 41 — 363 of the 393 are the logic layer, which is
what one expects while no constant has a graph. `protect` citations are excluded
(bookkeeping), and citations resolve exact-then-fallback because **760 serials
collide across theories**; keying by serial alone corrupts the graph.

Two consequences for planning, and they point opposite ways:

- **Partial progress on statements buys almost nothing.** Rendering more
  statements moves the 1,352, not the 393, until a whole cone closes.
- **Completing a cone pays superlinearly** — every theorem above it becomes
  eligible at once.

### What is still open

**393 is an UPPER bound and no proof has been replayed against it.** Eligibility
is necessary, never sufficient: the steps must also compose. But 393 > 0, so the
question is now attackable — there is a population to try it on, and §3b's
mapping table is what would be tried.

---

## 4. Why the previous encoder was deleted

Removed 2026-08-02 (recoverable from git history). It violated §2 **structurally** —
these were not bugs, but what the term layer and the proposition layer were built
to do:

| | |
|---|---|
| S1 | emitted `ι`-terms for `i`-terms without discharging the extension's cost |
| S2 | `_exists`/`_unique`/`_relmem` partial; constants got `∃` where S3 needs `∃!` |
| S4 | propositions reified as truth-value sets, a nonempty set standing for truth |
| S5 | the meta-function graph was reified and passed as an argument |
| S6 | unrelativized throughout |
| R1 | 214 Isabelle theorems emitted as `axiom`, buying 144 `Proved`; plus 113 prop-bridge axioms |
| R2 | 109 schemas with `UNPROVED` bodies |

**The finding that made a rewrite cheaper than a repair.** Parametric schemas were
proved *by* the reification: `ZFC_Separation → CollectI`, whose statement names the
reified graph of an **uninterpreted** `P` as an `ι`-term — the move R2 rules out.
So reification was not merely content asserted in place of a derivation; it was
the mechanism that made those proofs go through, and §3 cannot replace it (§3
compiles a class per *concrete* φ). Removing reification breaks that whole class
of proofs with no replacement, so the encoder could not be repaired incrementally.

**S1 and the `eq_subst` retirement are properties of the TARGET LANGUAGE, not of
any encoder's discipline.** A target term is a variable and nothing else, so the
language has no description term-former to emit and rejects a term in
parenthesised position outright; and its proof language has neither an `eq_subst`
nor an `iota_elim` step. The rejected constructs are unrepresentable rather than
discouraged.

**⚠ THIS QUESTION IS NOW HALF ANSWERED AND THIS PARAGRAPH PREDATES THE ANSWER.**
Pure's rules DO re-render: §3b's tier-7 probe states the nine as schemas, proves
them, and the kernel accepts it. What survives is narrower — whether a real
proof's steps COMPOSE once its statement renders. No whole proof has been
replayed. Answer it on one small theory before building outward.

**It is COUNTABLE, and that is the form to answer it in.** S1's boundary
treatment makes every other cost proportional to the CONSTANT count. The one
thing it cannot absorb is a proof that unfolds a description and reasons about
the described object rather than citing a lemma about it — that proof is about
something the signature cannot name, and must be regenerated. So the question is
**what fraction of proof-term nodes unfold a definition versus cite a lemma
about the constant**. The answer is a fraction, not a yes/no. **Do not infer it
from the shape of the encoding** — the four errors recorded in §2 all had that
cause.

**The citation half is settled in §3b** — `use` translates any cited theorem
whose STATEMENT is expressible, so counting citations answers nothing. What
follows is the statement half.

*Measured* over all 16,798 statements: **15,183 — 90% — refuse on a compound
term, across 258 DISTINCT heads.** Blockage broad, cause narrow. **⚠ THAT 258 IS
A WORK-LIST, NOT A SET THAT RESISTS** — the census renders with an EMPTY
vocabulary, so every constant in term position refuses by construction; it counts
heads needing an entry, not heads that would still fail with one. And it is not
258 graphs: the same population splits as **197 term constants** (the S2/S3
route) + 54 predicates (S4) + 6 connectives + 1 neither.

The 197 are a TERMINATING work list, and that is what Isabelle's own validation
buys. Its terms are total functions — `The` yields `0` when not unique — so EX
and UNIQ are consequences of well-formedness, not hypotheses that might fail.
They must still be *proved* in the target, which does not know Isabelle's
typing, but the proof cannot fail for a mathematical reason. Measured: all **197
reachable, 27 levels, no cycles, frontier 3**. S3's induction is executable, not
merely stated.

**And the 15,183 are NOT the bottleneck.** Eligibility closes over citations
(§3b), so the question is what the CLOSURE becomes, not how many statements
unblock. *Measured*:

| seed | closes to |
|---|---|
| renders today | **401** |
| + every one of the 197 constant graphs built | **2,437** |
| + the remaining gaps closed | **16,791** — §10's ceiling exactly |

**⚠ THE ENTIRE CONSTANT INDUCTION IS WORTH ~2,000 THEOREMS; THE `no-rule`
REFUSALS ARE WORTH ~14,350.** They cap the ceiling because each poisons every
cone above it.

*It was 263 gaps, 393 and 2,418.* **236 of the 263 were `meta_fn_graph` refusing
at EVERY arity**, where the 19 define `elem`/`pmem`/`tmem` and only a wider
`mem_n` is the family §3 removes. Rendering arity 1 and 2 again — S4's `P x ↦
elem(x,A)` at arity 1 — closed 228 of them. **⚠ AND THE CEILING BARELY MOVED:
393 → 401, 2,418 → 2,437.** Thirty-four gaps still cap it at 2,437 against
16,791, which is how violently the cone effect punishes a residue.

**⚠ AND MOST OF WHAT REMAINS IS NOT DEBT.** Building S4's `⋀P` half moved the
count by ONE: of the 15 `⋀`-over-non-`i` statements, **14 were arity 0** — the
`disjE`/`exE` shape S4 refuses by design, whose counterparts are the kernel's own
ND rules. The arity-≥1 `⋀P` case the design was built for is **almost absent from
this corpus**.

Of the **26** now left, **18 are CORRECT refusals** — 14 at arity 0, 4 needing
`mem4` — so only 8 are gaps. Two bugs accounted for the other 8, both found by
this count and both LOSSY rather than missing:

- a `λ` binder stripped its variable from the free-variable set **unconditionally**,
  so an outer occurrence of the same name was unbound. `bexI` is
  `⟦P(x); x ∈ A⟧ ⟹ ∃x∈A. P(x)` — `x` is free in the hypotheses AND bound by the
  `Bex`, and the binder wiped the free one.
- a schema parameter's ARGUMENT dropped its constraint. `Ra(ca(ub,y))` took the
  fresh variable for `ca(ub,y)` and discarded the graph lookup that defines it —
  S1's boundary treatment, skipped, leaving the variable free.

**`ZF.pair/3594` now renders — the first `ZF.*` statement to do so at all.**

So the leverage is not where "90% of statements are blocked" suggests. R5's graphs
are necessary and cheap to schedule; **the wide atom is what the ceiling is
actually gated on**, and it needs §3's construction to instantiate `?P` at a
compiled class. That is the dependency chain worth planning around.

---

## 5. Method

**Reason from what this document requires. Corpus measurements are tests, never
premises.** A count says what the translator happens to produce, never what it
ought to. Every plan derived from counts has been invalidated by a later count.

**⚠ EVERY CORPUS FIGURE IN THIS DOCUMENT IS UNEVIDENCED.** All of them were
measured by the deleted layer, and none can be reproduced as the tree stands. A
claim whose evidence is gone is a BELIEF, not state; the figures are kept only
because re-deriving one is cheaper than re-discovering the question it answered.
The two groups differ in what re-establishing them would cost:

- *Superseded with §3a* — R4's older reading, and §1's "missing lemma family
  indexed by block width", are claims about the position-indexed construction, so
  re-measuring them would rebuild exactly what §3 removes. **Read that passage as
  §3a's.**
- *Live but unevidenced* — the rest survive §3 and owe a new measurement. Two
  need none: R6's two refusals are STRUCTURAL, and CONG at `n = 0` reads off its
  own shape. §2's "TWO, not eight" is the one that still matters and still has
  nothing behind it — a structural proxy gives 75 vacuous `λ` across 58
  constants, a strict SUPERSET, since §2 counts only class-ARGUMENT positions.

**Nothing detects this rot automatically, and that is itself the gap.**

**Instruments must be able to fail.** A checker with no known-answer test — and
in particular no case it is *required to reject* — proves nothing. Two rounds of
wrong conclusions came from matchers that only ever passed.

The previous gate suite was deleted with the encoder: every gate measured shapes
of the encoding this document rejects. When the encoder is rebuilt, these are the
properties that need one each:

**Still open, and NOT a rule — it is unverified.** The old compiler was
arity-free and its proof size was *proved* linear in width × atom count, but the
context **width** grows with quantifier depth and §3's rule 2 costs a slot per
`eq` atom. The two readers of a context had to widen **together** — widening
either alone moves the refusal instead of removing it. This is where a
linear-size result could fail in practice. The concern is about any compiler with
this shape, so it outlives whatever computes it.

**⚠ THE WIDTH IS NOW MEASURED AND THIS PARAGRAPH ASKED FOR IT.** §3's
measurement: the max FULL context width
(arity + binders) over all 197 term-constant bodies is **9**, median 3–4. What
remains unmeasured is not the width but the *compiled* size at that width —
these are raw bodies, and R5 compiles them against earlier graphs.

| checks | against |
|---|---|
| nothing admitted but the 19 | §1 R1 |
| every schema has a non-`UNPROVED` proof | §1 R2 |
| every operation has EX/UNIQ/CONG, closed over definitional order | §2 S2, S3 |
| no term-former beyond variables; a proposition an object only as its truth set; no reified graph | §2 S1, S4, S5 |
| every quantifier and description relativized, and **interleaved** — swept over checked-in artifacts, not only generated ones | §1 R3, §2 S6 |

`docs/phase2_probes/` holds standalone `.fol.def`/`.fol.proof` pairs that the
checker verifies directly. They are artifacts, not prose — keep them.

Two rules, each with a test, because this paragraph previously asserted a
cleanup that had not happened — of 108 probes, 61 used `iota` and 70 had
`UNPROVED` bodies.

**An artifact survives only if something runs it.** Every probe must have exactly
one role — a link in §8's chain, a required-to-reject fixture, or evidence for one
documented claim — and the probe directory must be exactly the union of the three,
so a probe cannot be added and left unrun, nor deleted leaving a dangling claim.
77 that were reachable from nothing are gone. ⚠ **Nothing enforces this now.**

**No checked-in artifact may contain a banned construct, and "only there to be
rejected" is not an exemption.** 13 probes carrying `iota`/`eq_subst` were kept
once on that argument; they are deleted. The sweep must cover `base/` and the
probe directory through G4, which a check over *generated* units alone never sees.
A required-to-reject fixture is built inside the test, never stored as a file: a
banned construct sitting in the tree gets cited, copied, or wired into a chain.
