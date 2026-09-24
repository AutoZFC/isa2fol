# isa2fol — package layout and dialect types

**A SKETCH TO REACT TO.** Nothing built. Decisions I made rather than asked about
are marked **[choice]** — push back on any of them.

---

## 1. Package layout

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → node tree.   Knows no dialect.
  IR/            IRType only. §4 is built here, test-first.
  FolDialect/    types · print
  isa2fol/       CLI
Tests/
  YXMLTests/  FolDialectTests/
```

```
  YXML        IR        FolDialect
```

**Nothing connects them yet.** The reader (YXML → IR) and the emitter
(IR → FolDialect) are unbuilt, and where each lives is undecided.

### Two rules that make the guarantee real

1. **No `default:` in a switch over an IR enum.** One `default` and adding a
   variant stops breaking the build — which is the entire mechanism.
2. **IR enums stay `internal` to their module** (or `@frozen`). Across a
   library-evolution boundary Swift permits `@unknown default`, reopening what
   rule 1 closes.

Worth writing down the way the comment cap is: they are cheap, and forgetting
either is silent.

---

## 2. Reading the export  **[NOT BUILT]**

**It produces isa nodes in the unit's formula table (§4.2), and it RECOGNISES —
it never transcribes raw `ZApp`.** `ZApp(ZApp(ZConst "Pure.imp", a), b)` is read as
one `imp` node; connectives and binders are node kinds, not application spines.

**The dialect is the ZF SURFACE** — Isabelle/ZF's own vocabulary: Pure's and IFOL's
logic as named node kinds, and constants applied to their arguments (§4.3). The
reader recognises exactly that shape and **refuses anything else by name** — an
η-short binder argument (`All(P)`), a partially applied constant, a β-redex. It
never normalises.

**Normalisation is added per shape, and only on evidence.** If a non-surface shape
occurs, a pass brings it to the surface — Isabelle does the same with βη-normalisation
and its print translations, so nothing about it is impossible; it is just not built
before the data asks. The census `.claude/tasks/ISA_SHAPE_CENSUS.md` →
`docs/ISA_SHAPES.md` TESTS this shape: every export term reads into it or refuses,
and it counts which refusals occur.

**β-reduction we CREATE is ours to reduce, where we create it.** Instantiating a class
variable `P := λy. φ` makes `(λy. φ)(x)`; that happens in `forall_elim` or S4, not in
reading, and the operation that makes the redex reduces it (§4.4 `instantiate`).

**The surface it must cover is measured** — `docs/SOURCE_SURFACE.md`, which
regenerates: 3 Pure statement constants, 13 IFOL, **0 FOL**, 4 sorts, 249 ZF
constants; and on the proof side a frontier of 7 Pure axioms + 6 Pure derived +
132 IFOL/FOL + 7 ZF axioms + 207 object definitions.

### What the reader owes a NAMED refusal, never an absorbed case

These were `IsaDialect.Refusal`'s cases and they do not stop being obligations
because the enum is gone:

| refusal | why |
|---|---|
| a type variable | `IRType` has no case for `'a`. **Measured: 12 of 3,616 named ZF theorems (0.3%)**, half of them `split`/`qsplit`. IFOL/FOL/Pure are 37-48% polymorphic, and that layer is cited, never translated |
| a schematic `Var` (tag 2) | zero occurrences in 16,798 statements — a bet about the export's *preprocessing*, not about Isabelle. If one arrives, fail loudly |
| `Pure.conjunction` | **0 occurrences** in ZF statements, so refusing costs nothing |
| `Pure.term`, `Pure.sort_constraint` | Pure-internal, 0 in ZF statements |
| `Pure.prop` | 0 in ZF statements — erased, not refused |
| a `ZBound` with no enclosing binder | structural: its type, which the node must carry (§4.3), has nowhere to come from |
| a prop that is not a prop | structural |

⚠ **`groundnessIsStructural` WENT WITH THE MODULE, AND IT WAS THE ONLY TEST
PINNING THE POLYMORPHISM REFUSAL.** Re-pin it against the reader — a type
variable anywhere in a sort must refuse the whole statement, not just that slot.

## 3. FolDialect

⚠ **WHETHER THIS SURVIVES IS OPEN.** The table's fol nodes (§4.3) mirror fol-zfc's
own formula representation; a second tree of the same formulas is rule 4's
duplication unless `render` needs it. §5.

### Terms — the defining constraint

```swift
public struct Term {           // A VARIABLE. There is no other term.
    public let name: String
}
```

Not an enum, and not an oversight: **S1 says the signature has no function
symbols**, so a description former, an application, a literal — none of them have
anywhere to live. This is the type that killed `iota`.

### Formulas

```swift
public enum Binder { case setVar, classVar }

public indirect enum Formula {
    case predicate(String, args: [Term], isSchema: Bool)
    case bottom
    case not(Formula)
    case binary(BinOp, Formula, Formula)              // & | -> <->
    case quantified(Quantifier, Binder, String, body: Formula)
}
```

**[choice] the binder carries its kind.** Measured: with no kind, `gate::guards`
reports a *correct* class quantifier as an R3 violation, and nothing can check the
other direction — a class that IS guarded, which makes the claim false rather than
redundant. One field makes the rule two-sided.

### Declarations

```swift
public enum Declaration {
    case axiom(String, Formula)                        // only base/ may emit one
    case claim(String, Formula)
    case schema(String, params: [(String, Int)], Formula)
}
```

### What the dialect owns

```swift
func verify(_ d: Declaration) throws
//  G4  no term former beyond a variable   — free from the Term type
//  G5  every setVar binder guarded AND every classVar binder unguarded
//  G1  an axiom's origin is base/

func render(_ d: Declaration) -> String      // .fol.def text
```

⚠ **`render` must round-trip.** The checker's bison grammar is the only authority
on the surface syntax, so the test is `parse(render(d)) == d` against text the
checker accepts — not against our own reading of the grammar.

---

## 4. IR  **[DECIDED, NOT BUILT]**

**Only `IRType` is built.** Everything below is built from its tests first. The
previous region graph — formulas edited in place through `replaceAllUses`/`insert`/
`erase`, measured O(n²) per pass — is deleted; do not restore it from history.

### 4.1 Two layers, mirroring the checker

```
  formula table — one per unit                   proof steps — per proof
  ────────────────────────────                   ───────────────────────
  interned, immutable, isa AND fol kinds          ops in SCOPE REGIONS
  bound variables: de Bruijn                      fix / assume / exists_elim open a scope
  a statement = name → root ID                    forall_intro / implies_intro / exists_intro close it
          ▲                                       a step: rule, premise steps, → conclusion node
          └──────── steps reference table nodes ──────┘
```

This is fol-zfc's own split: `GlobalContext`'s `FormulaRegistry` and the
`ProofStack` (`~/repos/fol-zfc-comb/src/core/formula.h`, `src/proof/nd/stack.h`).

### 4.2 The formula table

- **Interned.** A node is its kind + payload + child IDs; equal content is the same
  ID. **ID equality IS formula equality** — the checker's semantics: its
  `Registry::register_item` deduplicates (`src/util/registry.h`) and
  `implies_elim` compares handles (`src/proof/nd/stack.cpp:339`).
- **Immutable.** A node is never edited. Rewriting builds new nodes; nothing is
  deleted, and a node no root reaches is simply unreferenced.
- **One table per unit** — a unit's statements and proofs, plus the signatures it
  cites, IMPORTED into the same table, as `proof_checker` loads dependency headers
  into one `GlobalContext` (`src/tools/proof_checker.cpp:39-82`). IDs are
  table-local and never compared across tables. What a unit is — a theorem or a
  theory — is open.
- **isa and fol kinds share it.** A partly lowered statement is an ordinary root
  whose DAG mixes both vocabularies.
- **Memory is not the constraint** — an ESTIMATE, from a throwaway decode that was not
  kept: ≈10M conclusion nodes across the whole export without any sharing, ~1–2 GB
  for all of ZF in one table. **Re-measure before relying on it.** The real
  exponential risk is INLINING a citation instead of linking it.

### 4.3 What a node is

> **A node's identity is exactly what its dialect's semantics distinguishes.**
> Nothing more — no cosmetic name, no translator annotation — or equal formulas
> split and ID equality stops meaning checker equality. Nothing less — its type
> and meaning must follow from the node alone, or one node means two things.

**The isa side is the ZF surface (§2).** Every node other than an abstraction is
fully applied and has a base type (`i`, `o`, `prop`):

| node | source | added | left out |
|---|---|---|---|
| `isaTrueprop(t)` · `isaImp(a, b)` · `isaAll(T, body)` · `isaEq[T](a, b)` | Pure: `Trueprop`, `⟹`, `⋀`, `≡` | | the `λ` under `⋀`: the body is de Bruijn |
| `iff` `conj` `disj` `imp` `Not` `True` `False` `All(T, body)` `Ex(T, body)` `eq[T](a, b)` | IFOL's logic | | the `λ` under a quantifier |
| `isaConst(name, typeArgs, args)` | any other constant — the 249 ZF constants, `IFOL.Ex1`, `IFOL.Let` — fully applied | | its type: the unit's constant declarations. One kind for `o`-valued atoms (`mem`) and `i`-valued terms (`QPair`) |
| `isaFree(name, T)` | free `ZVar` | the type, from the `frees` header | |
| `isaBound(k, T)` | `ZBound k` | **the type**, from the enclosing binder | |
| `isaVarApp(head, args)` | a variable applied — a class variable `P(x)`, `P : i ⇒ o` | | — the head is an `isaFree` or `isaBound`, never merged into the constant namespace (rule 3) |
| `isaAbs(T, body)` | `ZAbs`, ONLY as a function-typed argument: `Collect(A, λx. …)` | | **`x`** |

`Pure.prop` is erased; a type variable, a schematic `Var`, `Pure.conjunction`/`term`/
`type`/`sort_constraint` and `OFCLASS` are named refusals (§2). The logic gets
dedicated kinds because lowering translates it structurally; the ZF constants share
one kind because S1/S2 treat every one alike — the binders among them are told
apart by an argument's TYPE, never by name.

**The fol side mirrors fol-zfc** (`src/core/formula.h`): a term is a bound variable
(de Bruijn) or a fixed variable; a formula is a predicate over terms, a
connective, or a quantifier over a body. **The set/class binder kind is NOT
identity** — the checker cannot see it, and `∀A. (set(A) → ψ)` is valid text for
both. It is the translator's bookkeeping, known where lowering builds the binder.

### 4.4 Binders are de Bruijn

Both ends are: Isabelle's `ZBound`/`ZBoundp`, fol-zfc's `Gen(k)`, and `forall_elim`
is `instantiate_gen` (`src/proof/nd/stack.cpp:530`). Interning needs it — two
α-equivalent formulas are one node only if a bound variable is a position, not an ID.

⚠ **AN INDEX MEANS A POSITION, SO MOVING A FORMULA SILENTLY CHANGES WHAT IT SAYS.**
`mem(1, 0)` under two binders is `∀x∀y. mem(x, y)`; put unchanged under three it is
`∀x∀y∀z. mem(y, z)` — well-formed, wrong, and nothing downstream objects. Every change
of depth must adjust indices, in one place.

A variable is **loose** in a node when its binder lies outside that node; only loose
variables are ever adjusted. Depth changes in exactly three ways, and each has one
operation:

| operation | at bound `k`, at depth `d` | at named `x` | used by |
|---|---|---|---|
| `shift(φ, δ)` — a binder was added above | `k ≥ d` → `k + δ` | — | S1 wrapping `∀r` around an atom |
| `instantiate(body, t)` — a binder was removed | `k = d` → `t` shifted by `d`; `k > d` → `k − 1` | — | `forall_elim`, `exists_elim`, β-reduction (S4) |
| `abstract(φ, x)` — close over a name | `k ≥ d` → `k + 1` | `x` → `d` | closing a statement over its frees |

The guard needs none: `∀. body` → `∀. (set(0) → body)` leaves the body at its depth.

```
  S1:           ∀. mem(f(0), 0)          →  ∀. ∀. ( F(1, 0) → mem(0, 1) )      old x: 0 → 1 under the new r
  forall_elim:  ∀. ∀. (mem(1,0) → mem(0,1)) at a  →  ∀. (mem(a, 0) → mem(0, a))  x is 1 inside the inner ∀
  capture:      ∀. mem(1, 0), x := z (= 0)  →  ∀. mem(1, 0), NOT ∀. mem(0, 0)     t shifted under y
  β:            (λ. mem(0, 1)) z             →  mem(0, 0)                          1 → 0: the λ is gone
  close x:      mem(x, A) → ∀. mem(0, x)     →  ∀. ( mem(0, A) → ∀. mem(0, 1) )     ONE node x: 0 here, 1 there
```

Frees close in one pass, in the `frees` header's order: free `i` of `n` at depth `d`
↦ `d + (n − 1 − i)`, the first outermost.

**One traversal, three leaf rules.** `mapVars(node, depth, leaf)` descends, counts
binders into `depth`, asks `leaf` at every variable, and rebuilds through the intern
table (unchanged children ⇒ the same ID). Its exhaustive switch over node kinds is
**the only place that knows which kinds are binders**; shift, instantiate and
abstract are the three `leaf` rules. fol-zfc writes the walk four times
(`src/core/formula.cpp:285-470`); the isa side has many binder kinds, and every copy
must know all of them — a missed one is exactly the silent error above.

**`looseBound`** — the largest loose index + 1, 0 when closed — is computed when a
node is interned: `k + 1` at bound `k`; `max(0, body − 1)` at a binder; the max of the
children otherwise. Derived, so not identity. It lets `shift` and `instantiate` return
a node untouched, SAME ID, when nothing inside can change, so closed subformulas cost
O(1) and stay shared; it makes closedness of a statement's root one comparison, which
is where the reader's unbound-`ZBound` refusal lands (§2). `abstract` targets a name,
which `looseBound` cannot see; it walks the statement once, closing every free together.

**Types.** An isa bound variable carries its type (§4.3): `shift` keeps it, and
`instantiate` THROWS unless `type(t)` equals it. fol bound variables are untyped —
NBG is one-sorted.

**Pinned by laws over seeded random formulas**, plus boundary cases at `k = d`,
`d − 1`, `d + 1` — written first, failing first. Under interning `==` is ID equality,
so each tests the arithmetic AND deterministic building:

| law | |
|---|---|
| `instantiate(shift(φ, 1), t) == φ` | add an unused binder, fill it: no change |
| `instantiate(abstract(φ, x), x) == φ` | close over `x`, reopen at `x` |
| `abstract(instantiate(ψ, x), x) == ψ`, `x ∉ ψ` | open at a fresh `x`, close again |
| `shift(shift(φ, a), b) == shift(φ, a + b)` | shifts compose |
| `looseBound(φ) == 0` ⇒ every operation returns `φ`'s ID | closed is untouched |

### 4.5 Rewriting

- **A rewrite is a recursive function that builds the new formula.** A statement
  moves to the new root.
- **A fixpoint is a pass that returns the same root ID.** No round cap: a pass that
  does not approach its fixpoint is a bug in its rules.
- **A rewrite may take arguments beyond the node** — binder depth, the statement's
  ordered free variables. Closing a statement over its frees needs them: one
  interned free-variable node becomes `bvar 0` at one site and `bvar 1` under an
  inner binder.
- **No cache.** A shared node reached twice is rewritten twice, and interning makes
  the result identical, so this costs time, never correctness. It goes exponential
  only on nested sharing; the export is a tree, so a statement's paths are bounded
  by its export size unless a pass DUPLICATES subformulas. Add a memo when a
  measurement asks — keyed on every argument of the function, or it is silently wrong.

⚠ **`legalize` STAYS THE SEAL.** A rewrite is partial, so a new node kind breaks
nothing; one exhaustive switch over node kinds, walked from a lowered root, refusing
any isa kind, is where rule 11 lives.

### 4.6 Determinism

**The lowered statement is a signature** (§4a), and it is produced more than once: by
its own unit, by every unit that imports it, by Phase 2 re-lowering it from its proof
file, on every run. All of them must agree, or a `use` fails to match — or matches the
wrong formula.

**Determinism means the emitted TEXT is a function of the input CONTENT — not that IDs
agree.** Within one table interning makes equal content the same ID in any build
order; across tables (an importer, Phase 2) IDs cannot agree and need not. What must
never happen is something incidental — an ID, a hash order — reaching the output.

| rule | prevents |
|---|---|
| **R1.** A rewrite is a function of its node and its declared arguments (§4.5) | output depending on what else the table holds |
| **R2.** An ID is an identity — never an ORDER or a NAME in anything that reaches output. Orders come from the source: the `frees` header, child order, the proof's own order | frees sorted by ID close as `∀x∀A` in one unit and `∀A∀x` in an importer whose table interned `A` first — two signatures |
| **R3.** Never iterate a `Dictionary` or `Set` where the order can reach output or ID assignment; anything ordered is an array, a dictionary only looks up | Swift seeds `Hasher` PER PROCESS: frees kept in a `Set` close in a different order on every run |
| **R4.** Render names from structure: a bound variable is named by its LEVEL — binders above it from the formula's root, `b0`, `b1`, … — and fixed variables by a disjoint prefix, `f0`, … | capture: the checker resolves a name innermost binder first, then fixed variables (`src/parser/parser_bison.cpp:169-189`), so `∀. mem(0, a)` rendered `forall a. elem(a, a)` under `fix a` means the wrong thing |

⚠ **R3 HAS NO COMPILE-TIME GUARD.** One `for (k, v) in dict` on the path to output is
nondeterminism that a single process can never observe.

R4: along any path each binder has a distinct level, so no inner name shadows an outer
one and no bound name equals a fixed one. Index to name: `level = depth − 1 − k`.

```
  ∀. ∀. ( mem(1, 0) → ∀. mem(0, 2) )
  forall b0. forall b1. ( elem(b0, b1) -> forall b2. elem(b2, b0) )
```

Renaming is free to the checker, which compares de Bruijn handles, never names. The
cost is readability — `b0` for Isabelle's `x` — **accepted**: keeping Isabelle's names
would need one chosen per interned node, and "first seen" is exactly an order leak.

**Pinned by** a cross-table test — the same statement lowered in two tables pre-filled
with different unrelated nodes renders byte-identically (R1, R2) — and, once an emitter
exists, a cross-process diff of two runs, the only check that can see R3.

### 4.7 The proof layer

**The target is natural deduction, not Curry–Howard.** The checker's state is a set
of DERIVED formulas, each with the scopes it depends on (`formula_deps_`,
`src/proof/nd/stack.h`); a step checks its premises are derived and marks its
conclusion derived; `_x = …` names a formula (`step_env`, `src/proof/nd/verifier.cpp`).
**The proof is the graph from premise formulas to conclusion, by rule, inside scopes.**

- **A step is its own op** — rule, premise steps, conclusion node in the table. A
  formula may be derived more than once; derivedness belongs to the formula, and a
  step is one justification of it. Steps are not interned.
- **There is no proof type.** A step's value is the formula it derives.
- **A scope is a region**: its argument is the fixed variable or the hypothesis.

| Isabelle `zproof` (`zterm.ML:249`) | fol-zfc step |
|---|---|
| `ZAppt p t` | `forall_elim`, then `implies_elim` against a `set(t)` |
| `ZAppp p q` | `implies_elim` |
| `ZConstp` (a citation) | `use NAME` |
| `ZAbsp h:A. p` | `assume A` … `implies_intro` |
| `ZAbst x. p` | `fix x`, `assume set(x)` … `implies_intro`, `forall_intro` |
| `ZBoundp` | the `assume` step it names |

**It links like a compiled language.** A claim is a signature, a proof a body,
`use` a call, an `UNPROVED` stub an `extern` — and **the R3 guard is the calling
convention**: every caller's `forall_elim` at `t` owes an extra `set(t)`.

**A fol derivation may be built, never rewritten.** A rewritten one carries no
witness it is still a derivation, and re-establishing that in-process is a second
checker.

⚠ **`exists_elim` SCOPES THE REST OF THE DERIVATION**, closed by `exists_intro`
(`src/proof/nd/stack.cpp:552`). S1's recipe for a compound `ZAppt` goes through it,
so a proof pass must be able to move the steps that follow into a new scope.

### 4.8 Open

| | |
|---|---|
| S1 placement | the fresh `r` at the atom (local) or at the statement (FOUNDATION §2's wording); differs when `f(x)` occurs twice, which the proof sees |
| the unit | one theorem or one theory per table |
| the proof layer | step kinds, scope regions, emission order, symbol import |
| proof-level depth | whether a term `ZBound` inside a proof counts `ZAbst` binders — census question 6 |

## 4a. Statement lowering  **[NOT BUILT]**

**The statement is TRANSLATED, not passed through.** A declaration is not an
interface the proof reads unchanged — lowering changes the proposition's shape,
and the proof must be built against the changed one.

```
⋀x. (mem(x,y) ⟹ mem(x,y))     →     ∀x. (set(x) → (mem(x,y) → mem(x,y)))
```

Three passes, and the order is forced:

| pass | does |
|---|---|
| `lower-pure` | erase Pure's `o ⇒ prop` coercion; `⟹` → `→` |
| `lower-ifol` | `isaFree` → `folVar`, `isaAtom` → `folPred` — a pure relabel, node types unchanged |
| `guard-binders` | **R3**: `⋀x:i. φ` → `∀x. (set(x) → φ)`; a non-`i` sort refuses |

Under §4 each is a recursive rewrite building interned nodes; the guard is
construction: `∀(set(bvar 0) → body′)`.

### The guard is half of a contract

Inserting `set(x)` puts an obligation on the proof: every `forall_elim` at a term
`t` now owes a `set(t)` the Isabelle proof never supplied. So the symbol a proof
links against is a **signature**, not a name and not a formula — two theorems with
identical text but different guard placement are different symbols.

⚠ **LOWERING MUST THEREFORE BE A DETERMINISTIC FUNCTION OF THE STATEMENT ALONE.**
The emitted `.fol.def` records the guards but *not* where a materialised variable
came from, so PHASE 2 recovers that by **re-running this lowering** over the
`prop` its own proof file carries. Same content in, same text out — §4.6.

## 5. What I did not decide

| | |
|---|---|
| what monomorphise instantiates at | use-site type argument, or always `'a := i`? The second is §11.0's proposal and resolves `eq`/`All`/`Ex`/`split` in one move, but makes a generic IFOL theorem mean only its `i`-instance |
| whether the ZF primitive surface is a third dialect or a stage inside IsaDialect | parked where you left it |
| what `base/` becomes | it is `.fol.def` text today; does FolDialect *read* it, or is it opaque input to the checker? |
| whether `FolDialect.Formula` survives | §4's fol nodes already mirror fol-zfc; `render` could read them directly |
