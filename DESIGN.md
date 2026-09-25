# isa2fol — package layout and dialect types

**A SKETCH TO REACT TO.** Nothing built. Decisions I made rather than asked about
are marked **[choice]** — push back on any of them.

---

## 1. Package layout

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → node tree.   Knows no dialect.
  IR/            §4's framework: Node · Table · transform · index engine · passes · legalize.  BUILT
  FolDialect/    render · parse · Declaration — the text boundary over IR (§3)
  isa2fol/       CLI
Tests/
  YXMLTests/  FolDialectTests/  IRTests/
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

## 2. Reading the export  **[STATEMENTS BUILT; proofs NOT]**

**Measured, one build** (`swift build -c release && .build/release/isa2fol statements data/zf_export`,
36 s): every one of the 38,923 proof files reads or refuses by name, none is malformed. Of the
3,616 named theorems of session ZF, **3,602 translate**; across the eight exported sessions,
**9,382 of 9,420**. The 38 refusals are 23 type variables, 14 `Pure.all` over a function (S5),
1 `OFCLASS`.
`--show KIND` lists each refused statement.

**It produces isa nodes in the unit's formula table (§4.2), and it RECOGNISES —
it never transcribes raw `ZApp`.** `ZApp(ZApp(ZConst "Pure.imp", a), b)` is read as
one `imp` node; connectives and binders are node kinds, not application spines.

**The dialect is the ZF SURFACE, built downstream-first.** FOL's surface is the
base; from IFOL only what FOL cannot express is imported; from Pure only what IFOL
cannot. A construct the downstream surface covers is READ AS the downstream
construct — Pure's `⟹` is `folImplies`, never a kind of its own. ZF's own vocabulary —
constants applied to their arguments — is the generic term language (§4.3). The
reader recognises exactly that shape and **refuses anything else by name** — a β-redex,
a bare λ. It
never normalises — with ONE exception, below.

**η: every function-typed argument is read η-LONG.** Isabelle stores a function argument as the
source wrote it: `Ball(A, P)`, `Part(sum(A,B), Inl)`, `congruent(r, split(f))` (a partial
application). Measured (facts run, not kept): 462 of 3,616 named ZF theorems pass a
function-typed ZF argument that is not a λ, 58 a partial application; the logical binders are
all λ. The reader wraps such an argument as `λx⃗. t(x⃗)`, bound types from its function type:
`P ↦ λx. P(x)`, `Inl ↦ λx. Inl(x)`, `split(f) ↦ λp. split(f, p)`. It is η, a Pure primitive
rule, so the meaning is Isabelle's. ⚠ **IT IS REQUIRED, NOT COSMETIC:** Isabelle compares
terms up to η and the table by ID, so without ONE canonical η-form `Collect(A, P)` and
`Collect(A, λx. P(x))` are different nodes, and a step matching premises by ID fails where
Isabelle's did not. η-long is the form in which `intern`'s "a function-typed argument is an
`isaAbs`" and S4/S5 see one shape.

**Measured, statements of the 3,616 named ZF theorems** (`isa-deps --logic --named`,
`~/repos/isabelle-study/bin/isa-deps`): every logical constant is fully applied and
every binder argument is a `λ`, without exception. Bare and partial applications —
225 bare `Trueprop`, partial `eq`/`iff` — occur only inside PROOF terms, where the
proof layer meets them; across all 16,798 files of the pre-2026-09-25 export, which merged two builds, proof terms also hold 8,989
`Pure.dummy_pattern`, none in the named ZF theorems.

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

### Reading scales with the DAG, never the tree

Isabelle holds a proof as a DAG and its exporter writes the tree: every shared sub-proof is
spelled out once per path. Measured over one build (a throwaway structural-hash count):

| | tree nodes | distinct subtrees |
|---|---|---|
| the box inside `List.nth_upt`'s proof — ONE file, 3.1 GB | 312,298,646 | 11,604 |
| the other 15,945 proof files | 29.0 M | ≤ 1.94 M |

So **reading is one pass that interns as it parses.** `YXML` parses into a hash-consed forest
— equal subtrees are one `Ref`, across files too — so memory follows the DAG and time the
bytes. Decoding a `Ref` into table nodes is memoised on `(Ref, context)`: the same XML subtree
under different binders is a different term (`ZBound 0` takes its binder's type). ⚠ A reader
that builds the tree, or decodes without the memo, is exponential on real input.

**Isabelle's exporter stays the source of truth.** An exporter of our own that kept the
sharing would be a second encoder to trust; reading the tree it writes in one hash-consing
pass costs nothing extra. Its one-time build (`scripts/03-export-zf.sh`, ~8 min under a 64 GB
cap) is revisited only for a corpus larger than ZF.

### Three decisions the reader is built on

| | decided |
|---|---|
| **types** | The reader decodes `ztyp` into ITS OWN type, which has `'a` and `prop`. A `ZConst` carries only its type ARGUMENTS (`ZConst1 (a, b) => ([a], list ztyp [b])`, `zterm.ML`'s encoder), so `isaConst`'s instantiated type is the declared scheme from `theory/consts` (`IFOL.eq :: ['a, 'a] ⇒ o`) with those arguments substituted. Converting to `IRType` refuses a leftover type variable by name. `IRType` has no `prop`: **`prop` converts to `o` in EVERY type** — the coercion is the identity (§4.3). A variable of type `prop` (`elim_format`'s `W`) is a formula variable as `P :: o` is; a constant of type `prop` (`AC_Equiv.AC18`) or over `prop` (ZF-Constructible's `MetaExists.ex :: ('a ⇒ prop) ⇒ prop`) is a formula constant. ⚠ Refusing `prop` anywhere split one construct in two — 6 vs 194 theorems for variables, then 192 for constants. The Pure-internal constants (`Pure.term`, `Pure.conjunction`, …) are refused BY NAME before any type is converted; FOUNDATION S4's arity-0 question is lowering's |
| **frees** | Left as `isaFree`, typed from the `frees` header; a closing pass abstracts them (§4.4). A statement and its proof share the same interned free nodes, so ONE closing applies to both. The order is Isabelle's closure order, read from `proofterm.ML` (§4.4); the data check is a citation instantiated by its `ZAppt`s concluding what the citing proof uses, by ID — once proofs are read |
| **outcomes** | The READER owns them, never IR: in source order, `(serial, name?, translated(root) \| refused(reason))`. A refused statement never enters IR; IR's `Statement` is keyed `(serial, name?)` — unnamed proof boxes have no name — within its unit's theory. ONLY the reader's own refusal enum is caught and recorded; a `TableError` or `YXMLError` is a bug or a corrupt file and stops the run — catching it would count our bugs as refusals |

### What the reader owes a NAMED refusal, never an absorbed case

These were `IsaDialect.Refusal`'s cases and they do not stop being obligations
because the enum is gone:

| refusal | why |
|---|---|
| a type variable | `IRType` has no case for `'a`. **Measured: 12 of 3,616 named ZF theorems (0.3%)**, half of them `split`/`qsplit`. IFOL/FOL/Pure are 37-48% polymorphic, and that layer is cited, never translated |
| a schematic `Var` (tag 2) | zero occurrences in the 16,798 statements of the pre-2026-09-25 export, which merged two builds — a bet about the export's *preprocessing*, not about Isabelle. If one arrives, fail loudly |
| `Pure.conjunction` | **0 occurrences** in ZF statements, so refusing costs nothing |
| `Pure.term`, `Pure.sort_constraint` | Pure-internal, 0 in ZF statements |
| `Pure.prop` | 0 in ZF statements — erased, not refused |
| a `ZBound` with no enclosing binder | structural: its type, which the node must carry (§4.3), has nowhere to come from |
| a prop that is not a prop | structural |

⚠ **`groundnessIsStructural` WENT WITH THE MODULE, AND IT WAS THE ONLY TEST
PINNING THE POLYMORPHISM REFUSAL.** Re-pin it against the reader — a type
variable anywhere in a sort must refuse the whole statement, not just that slot.

## 3. FolDialect — the text boundary over the table  **[render BUILT; parse NOT]**

**There is no second representation of a fol formula.** The table's fol nodes (§4.3)
ARE the formulas; `FolDialect` only turns them into fol-zfc text and back.

```
  table fol nodes ──render──▶ .fol.def / .fol.proof text     names from depth (§4.6 R4)
  table fol nodes ◀──parse─── .fol.def text                  imported signatures (§4.5)
```

`FolDialect` imports `IR`. What it owns:

| | |
|---|---|
| `Declaration` | `(kind, name, root)` — kind `claim` or `definition(predicate)`, rendered `claim NAME: …` and `@def(P) axiom NAME: …`. There is NO `axiom` case: only `base/` has axioms, and `base/` is text the checker reads, never something we emit — so G1 holds by construction. `schema` waits for schemas |
| `render` | the table → text: one line per declaration, bound variables named by level `b0, b1, …`; refuses an isa node, an unclosed root, a malformed name |
| `parse` | text → table nodes, for imports — when imports are built |

⚠ **THE ROUND TRIP IS AN ID COMPARISON:** `intern(parse(render(root))) == root`.
Interning makes it exact. The checker's grammar is the only authority on the syntax,
so the text in that test must also be text the REAL checker accepts — never only our
own reading of the grammar.

**Where the dialect's invariants live now:**

| | enforced by |
|---|---|
| G4 — no term former beyond a variable | `Table.intern`: a `folPred` argument is a `folBound` |
| G5 — a set binder guarded, a class binder not | the lowering that BUILDS the binder, where the source type says which it is (§4.3) — never re-derived from the formula, which would check the guard against itself |
| G1 — an axiom's origin is `base/` | `Declaration` has no `axiom` case |

**Names: Isabelle's own, unchanged — no sanitization anywhere.** A qualified name
(`ZF_Base.mem`, `QPair.QPair_iff`) is legal in exactly two kinds of position, and never
in a variable's:

| position | example |
|---|---|
| a CLAIM NAME — declaration, proof header, `use` | `claim QPair.QPair_iff: …` · `_3 = use QPair.QPair_iff` |
| a PREDICATE NAME | `forall b0. ZF_Base.mem(b0, b1)` |

The grammar decides by position, not whitespace: a variable is never qualified, so after
`forall x` a `DOT` ends the binder, and in predicate position an identifier followed by
`DOT` can only continue a qualified name. `render` still writes `forall b0. body` with
the space. **Requires a checker change** — `qualified ::= IDENTIFIER (DOT IDENTIFIER)*`
in those positions, from existing tokens, no lexer change — in fol-zfc-comb, with its
own tests there.

Measured over the export's 4,230 theorem and constant names (`theory/thms`,
`theory/consts`): the only characters outside `[A-Za-z0-9_]` are `.` (qualification), `'`
(10, only at a segment's end) and `(N)` (627, only as a trailing fact index). So:

- `'` joins the qualified-name rule — the grammar uses it nowhere else.
- A fact index is not part of the name: the export carries `(name, index)` as two
  attributes, and `(N)` is only Isabelle's display. It is spelled `name.N` — injective
  because no segment starts with a digit, which the READER CHECKS, refusing any name
  with a digit-initial segment rather than assuming the count.
- `render` validates every name against the rule and throws on a malformed one.

Why qualified predicates and not unqualified ones, measured: `pred` names two constants
(`Arith.pred`, `Order.pred`), and ten unqualified names — `Inf`, `Pow`, `PrimReplace`,
`Replace`, `The`, `Union`, `Upair`, `eq`, `succ`, `zero` — are already predicates in
`base/`. Unqualified, `ZF_Base.Union` and `base/`'s `Union` would coincide by spelling,
silently substituting one constant for another; qualified, identifying them is an
explicit vocabulary entry in a pass.

**No schema variables yet.** If a schema is ever emitted — FOUNDATION's arity-0 `?P` —
a schema variable becomes a table node kind then: one more case in the four switches.

---

## 4. IR  **[FRAMEWORK BUILT; renderer and proof layer NOT]**

**§4.2–§4.7's framework is built** (`Sources/IR`, `Sources/FolDialect`, pinned by
`Tests/`). No concrete pass and no reader are. The previous region graph — formulas edited in place through `replaceAllUses`/`insert`/
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
- **Validated at `intern`, the only way in.** Children exist and are well-typed; a
  function-typed argument is an `isaAbs`; a `folPred` argument is a `folBound`; an
  application is full. Anything else throws — an ill-formed node cannot exist in a table.
- **Immutable.** A node is never edited. Rewriting builds new nodes; nothing is
  deleted, and a node no root reaches is simply unreferenced.
- **One table per unit** — a unit's statements and proofs, plus the signatures it
  cites, IMPORTED into the same table, as `proof_checker` loads dependency headers
  into one `GlobalContext` (`src/tools/proof_checker.cpp:39-82`). IDs are
  table-local and never compared across tables.
- **A unit is one THEORY** — Isabelle's own unit, and one fol-zfc header/proof pair.
  88.5% of a ZF proof's citations leave its theory (59.4% into Pure/IFOL/FOL, 29.1%
  into other ZF theories, 11.5% within), so a finer unit saves no linking and only
  re-parses popular signatures; and the unnamed sub-derivation boxes, 1,288 of them
  shared between theorems, have no single owning theorem. The checker still reports
  per claim.
- ⚠ **A REFUSAL IS PER STATEMENT, NEVER PER UNIT.** The unit records each statement's
  outcome — translated, or refused with its reason. A refused theorem is absent from
  the header, so whatever cites it fails to find it — loudly, never as `Conditional`.
  **NOT BUILT:** `Unit` holds statements, not yet their outcomes.
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

**The isa side is the ZF surface (§2), downstream-first.** How each logical construct
lands:

| Isabelle | covered by FOL? | read as |
|---|---|---|
| IFOL `conj` `disj` `imp` `iff` `Not` `False` | yes | `folAnd` `folOr` `folImplies` `folIff` `folNot` `folBottom` |
| Pure `⟹` | yes — the target has one implication | `folImplies` |
| `Trueprop`, `Pure.prop` | yes — the `o ⇒ prop` coercion is the identity once `prop` is `o` | erased |
| Pure `≡` at `o` or `prop` | yes | `folIff` |
| IFOL `∀x:T` / `∃x:T`, Pure `⋀x:T` | **no** — a set quantifier owes the R3 guard, a class one does not | **`ifolAll(T, body)`, `ifolEx(T, body)`** — the only dedicated imports |
| IFOL `eq[i]`, Pure `≡` at `i` | no — `folPred` takes variables, these take terms until S1 | `isaConst("IFOL.eq", …)` |
| `True`, `Ex1`, `Let`, `Uniq` | no — defined constants | `isaConst` |
| Pure `≡` at a function type — definitions `f ≡ λx. t` | not by FOL or IFOL | `isaConst("Pure.eq", …)`, consumed by S2 |
| Pure `⋀` at a function type | not by FOL or IFOL; S5 | named refusal until S5 is designed |

**The quantifier is the one dedicated import because the guard is the calling
convention (§4a).** Everything else is a relabel or data S1/S2 treat alike; as data,
`isaConst("IFOL.All", …)` would be matched by a name string, and a quantifier the
lowering missed would silently change every signature. As a kind, rule 11 covers it.

The generic term language — ZF's own vocabulary, not logic at any level:

| node | source | added | left out |
|---|---|---|---|
| `isaConst(name, T, args)` | any constant not read as logic above — the 249 ZF constants, `IFOL.eq`, `True`, `Ex1`, `Let`, `Uniq`, `Pure.eq` at a function type — fully applied | its INSTANTIATED type `T` — it determines the type arguments and back, so the identity is the same | the declared scheme: declarations stay polymorphic (`IFOL.eq :: 'a ⇒ 'a ⇒ o`) though every use is ground, so the READER instantiates once from `theory/consts` and no `'a` enters the table |
| `isaFree(name, T)` | free `ZVar` | the type, from the `frees` header | |
| `isaBound(k, T)` | `ZBound k` | **the type**, from the enclosing binder | |
| `isaVarApp(head, args)` | a variable applied — a class variable `P(x)` | | the head is an `isaFree` or `isaBound`, never merged into the constant namespace (rule 3) |
| `isaAbs(T, body)` | `ZAbs`, ONLY as a function-typed argument: `Collect(A, λx. …)` | | **`x`** |

`IRType` has no `prop` case (§2). A type variable, a schematic `Var`,
`Pure.conjunction`/`term`/`type`/`sort_constraint` and `OFCLASS` are named refusals (§2).

**The fol side mirrors fol-zfc** (`src/core/formula.h`): a term is a bound variable
(de Bruijn) — fol-zfc's FIXED variables are emission's concern, not a node kind (§4.7);
a formula is a predicate over terms, a
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

Frees close in one pass, over the PROPOSITION's frees in first-occurrence order: free `i`
of `n` at depth `d` ↦ `d + (n − 1 − i)`, the first outermost. That is Isabelle's own closure
(`forall_intr_variables_term`, `variables_of` in `proofterm.ML`), which fixes the order in
which every citation's `ZAppt`s instantiate. The `frees` header lists the same frees first
(`standard_vars`, `zterm.ML`) and then any that occur ONLY in the proof — ⚠ closing over those
too adds a `∀` no citation fills. The header EQUALS the proposition's frees — measured over all 16,798
files of the pre-2026-09-25 export, which merged two builds, and forced by the encoder: `standard_hidden_terms` (`zterm.ML`) turns every proof-only variable into
`dummy_pattern` before the header is built. The reader checks equality; a mismatch is a
malformed export, not a refusal.

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

### 4.5 The framework: traversal, index engine, passes

```
  Node        SOURCE kinds (isa*, ifol*) and TARGET kinds (fol*) — ONE FLAT enum
  Table       intern · subscript · type(of:) · looseBound(of:)          §4.2
  transform   THE traversal: descend, count binders, apply a Rule, rebuild through the table
     ├── index engine   shift · instantiate · abstract — Rules on variable leaves  §4.4
     └── passes         Rules on the kinds a pass lowers
  Unit        the table + statements [(name, root)] in source order
  legalize    no source kind reachable from a lowered root
```

**Flat, not nested source/target.** Nesting is per node, not per statement — a
`folAnd` holds `NodeID`s either way, so both represent a partly lowered statement, and
anything that walks children must handle both dialects regardless. Nesting would only
tidy `legalize`.

**One traversal serves the index engine AND every pass.** Both need "descend, count
binders, rebuild through the table"; an index operation is a rule that fires on variable
leaves, a pass is a rule that fires on the kinds it lowers.

```swift
public protocol Rule {   // nil = no match: rebuild the node from its rewritten children
    func apply(_ id: NodeID, depth: Int, in t: inout Table) throws -> NodeID?
}
public func transform(_ root: NodeID, _ rule: Rule, in t: inout Table) throws -> NodeID
public protocol Pass { var name: String { get }
                       func run(_ root: NodeID, in t: inout Table) throws -> NodeID }
```

- **A pass never writes its own recursion.** It supplies a rule for the kinds it handles;
  every other kind is rebuilt from its rewritten children.
- **A fixpoint is a pass that returns the same root ID.** No round cap: a pass that does
  not approach its fixpoint is a bug in its rules.
- **A pass may take arguments beyond the node** — binder depth from the traversal, and
  whole-statement parameters it computes from the root before transforming (the ordered
  frees that closing needs: one interned free-variable node becomes `bvar 0` at one
  site and `bvar 1` under an inner binder).
- **A pipeline** runs its passes in order over every statement root. `legalize` is a
  separate call, made where lowering is meant to be complete — a pipeline may end at a
  mixed stage.
- **A rule sees a node BEFORE its children, and a non-nil result replaces that subtree
  without descending into it.** Returning the node itself means "unchanged, do not
  descend" — how the index engine prunes a closed subtree (§4.4).
- **No cache.** A shared node reached twice is rewritten twice, and interning makes the
  result identical — time, never correctness. It goes exponential only on nested
  sharing; the export is a tree, so a statement's paths are bounded by its export size
  unless a pass DUPLICATES subformulas. Add a memo when a measurement asks — keyed on
  every argument of the function, or it is silently wrong.
- **One unit per run**; imports arrive as text or a compiled library, as `proof_checker`
  loads them. So one table per process, and an out-of-range ID is the only foreign ID.

**Four exhaustive switches — adding a kind breaks exactly these** (rule 11):

| switch | its question | derived from it |
|---|---|---|
| **structure** — `mapChildren(node, f(child, underBinder))` | children, and which sit under a binder | children (`f` records), rebuild (`f` returns new), binder body, `looseBound` = max over children of `looseBound(child) − (underBinder ? 1 : 0)` |
| **bound variable** | is this a bound variable, at which index | the `k + 1` leaf of `looseBound`; the index engine's leaves |
| **type** | the node's type, and whether its children are well-typed | `intern`'s validation |
| **legalize** | source or target | the seal |

⚠ **WHICH KINDS BIND EXISTS IN EXACTLY ONE PLACE — THE STRUCTURE SWITCH.** The traversal,
the index engine and `looseBound` all derive from it, so they cannot disagree. Separate
functions could, and the disagreement is D2's silent error: a binder one of them misses
has its body skipped by `shift`. The cost — "children" is read by rebuilding, allocating
for `isaConst`/`folPred`'s arrays — is an unmeasured constant factor.

**`render` is a FIFTH exhaustive switch** — an emitter must know every target kind's
text, so it cannot be derived; its source-kind cases throw. Adding a kind that can reach
the text costs five switches.

⚠ **`legalize` STAYS THE SEAL.** A rule is partial, so a new kind breaks no pass; the
legalize switch is where a kind nothing lowers is caught.

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

### 4.7 The proof layer  **[FRAMEWORK BUILT]**

**The target is natural deduction, not Curry–Howard.** The checker's state is a set
of DERIVED formulas (`formula_deps_`, `src/proof/nd/stack.h`); a step checks its
premises are derived and marks its conclusion derived.

**A step is a function from derived statements to a new derived statement** — a node
in the SAME table, lowered by the SAME `transform` and `RulePass` as formulas. Its
conclusion is a formula node, computed at `intern` the way a formula node's type is.
There is no separate proof tree, no builder, and no step-by-step driver.

⚠ **A STEP CONSTRAINS ONLY ITS PRINCIPAL CONNECTIVE.** An ELIMINATION rule consumes: its
major premise must have the rule's connective at the top. An INTRODUCTION rule produces:
its conclusion has it at the top. Every other part — other premises, sub-formulas —
may be isa, fol or mixed, and `intern` checks the principal connective and nothing else:

```
  and_intro A B     A = mem(a, A), B = ifolAll(i, …)   → folAnd(mem(a, A), ifolAll(i, …))   fol top, isa inside
  and_elim_l p      p ⊢ folAnd(ifolAll(i, …), X)       → ifolAll(i, …)                      an isa statement, by a fol step
  implies_elim p q  p ⊢ folImplies(A, B), q ⊢ A BY ID  → B                                  whatever dialect B is
```

An isa step is typed the same way by ITS principal connective: `isaAllElim` needs
`ifolAll` at the top of its major premise.

**The surface is read downstream-first, like formulas.** A zproof constructor whose
connective the downstream already covers IS the fol step from the moment it is read;
isa steps exist only where the connective is still isa:

| zproof (`zterm.ML:249`) | acts on | read as |
|---|---|---|
| `ZAppp` — ⟹-elim | `folImplies` (Pure `⟹` reads as it) | `folImpliesElim` |
| `ZAbsp` — ⟹-intro | produces `folImplies` | `folImpliesIntro` |
| `ZAppt` — ⋀-elim | `ifolAll`: the guard is not there yet | an isa step |
| `ZAbst` — ⋀-intro | produces `ifolAll` | an isa step |

**Lowering rewrites isa steps into fol steps, bottom-up.** A rewritten step concludes a
new statement; when it keeps its conclusion its consumers are untouched, when it changes
a connective they are rewritten in turn:

```
  p  = cite thm            ⊢ ifolAll(i, mem(0, A))
  s  = isaAllElim(p, a)    ⊢ mem(a, A)
         the citation's signature is lowered (§4a):
  p′ = cite thm            ⊢ folForall(set(0) → mem(0, A))
  s  = isaAllElim(p′, a)   ✗ an isa step on a fol ∀
  s′ = folImpliesElim(folForallElim(p′, a), ⟨set(a)⟩)   ⊢ mem(a, A)   unchanged: consumers untouched
```

**Done is: no isa step reachable, every conclusion fol-zfc, and the last one equals the
lowered claim — by ID.** `legalize` refuses a reachable isa step as it refuses an isa
connective.

What the framework gained (BUILT — `Sources/IR`, emission in `Sources/FolDialect/Render.swift`):

| | |
|---|---|
| `Rule.after(node, depth)` | the node with its REWRITTEN children, before `intern` — a step can only be rewritten once its premises have been, and `intern` would reject `isaAllElim(p′, a)`. `before` stays for pruning |
| conclusion at `intern` | the type switch computes it; a step whose principal connective is wrong cannot exist |
| D1 for steps | a hypothesis reference carries its formula, as `isaBound` carries its type; a citation carries its statement's root, imported into the table |
| two binder namespaces | term binders (`∀`, `λ`, ⋀-intro) and hypothesis binders (⟹-intro) number separately: the structure switch says which, `looseBound` is per namespace, and discharging a hypothesis is a proof-level `instantiate`. Isabelle's counting is census question 6 |
| emission | a proof tree becomes the checker's linear stack program — `folImpliesIntro(A, body)` → `assume A` … `implies_intro` — in `FolDialect`. A binder's scope is its body subtree, so `exists_elim` wraps a LOCAL subproof; nothing moves "the rest" |

**The step kinds — minimal: a checker rule is a kind only when something the source
contains needs it.** Every Isabelle proof bottoms out in Pure's constructors and in
citations; a citation is a step concluding the cited statement, so ONE kind covers every
axiom — how `use conjI` becomes `and_intro`, or `use combination` becomes CONG, is pass
detail.

| | kinds |
|---|---|
| neutral — concludes what it carries, any dialect | `use(name, root)` (`PThm`/`PAxm`; `root` imported into the table) · `hyp(k, A)` (`PBound`; carries `A`, D1) |
| fol intro | `andIntro(p, q)` · `orIntroL(p, B)` · `orIntroR(A, q)` · `impliesIntro(A, body)` ◆ · `notIntro(A, body)` ◆ · `iffIntro(p, q)` · `forallIntro(body)` ● · `existsIntro(p, v)` |
| fol elim | `andElimL(p)` · `andElimR(p)` · `orElim(p, q, r)` · `impliesElim(p, q)` — `q` concludes the antecedent BY ID · `notElim(p, q)` · `iffElimL(p, q)` · `iffElimR(p, q)` · `forallElim(p, v)` — `v` a fol variable (S1) · `existsElim(p, body)` ●◆ · `bottomElim(p, C)` |
| fol classical | `classicalAbsurd(A, body)` ◆ — with `notElim` it covers FOL's one axiom, `(¬P ⟹ P) ⟹ P` |
| isa — the typed quantifier only | `isaAllIntro(T, body)` ● (`ZAbst`, produces `ifolAll`) · `isaAllElim(p, t)` (`ZAppt`, consumes `ifolAll`; `t` any isa term of type `T`, concluding `instantiate(body, t)`). They also cover `⋀P:o` and `⋀P:i⇒o` — instantiating a proposition or class variable, as citing an IFOL rule does |

◆ binds a hypothesis, ● a term variable — exactly the checker rules that close a scope
(`src/proof/nd/stack.cpp`: `implies_intro:303`, `not_intro:351`, `forall_intro:495`,
`exists_intro:552` closing `exists_elim`, `classical_absurd:698`). Left out until a pass
needs them: `double_neg_elim`, `excluded_middle`, `peirce` (covered classically above);
`eq_subst`, `eq_sym` (`eq` is a defined predicate, FOUNDATION §2 retires `eq_subst`);
`schema_inst` (no schemas); `iota_elim` (S1).

**`fix` and `assume` are emitted from binders; the table has no fixed-variable node.** A
term binder's body proves `φ` with the bound variable as loose index 0, so `forallIntro`
concludes `folForall(conclusion(body))` — no `abstract`, no fresh-name counter, and the
eigenvariable condition holds by construction. Emission writes the checker's stack
program from the tree:

```
  forallIntro(                               fix f0
    impliesIntro(set(0),                     _0 = assume set(f0)
      impliesIntro(P(0),                     _1 = assume P(f0)
        hyp(0, P(0)))))                      _2 = implies_intro _1
                                             _3 = implies_intro _2
                                             _4 = forall_intro _3
                                             qed _4
```

A term binder becomes `fix f_k` and its loose index renders as `f_k`; a hypothesis binder
becomes `assume A`; `hyp(k, …)` renders as that `assume` step's name.

**As built, three things are the caller's to guarantee, never checked:**
- a `hyp(k, A)` carries the formula its binder introduced (for `folExistsElim`, the ∃'s
  body) — contextual, like `isaBound`'s type;
- `isaAllIntro(T, …)`'s body uses its bound variable at type `T`;
- emission unfolds a shared subproof once per use — no memo, as for rewrites (§4.5).

**It links like a compiled language.** A claim is a signature, a proof a body, `use` a
call, an `UNPROVED` stub an `extern` — and **the R3 guard is the calling convention**:
every caller's `forall_elim` at `t` owes an extra `set(t)`.

### 4.8 Open

| | |
|---|---|
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

### Pass-level questions — for the passes, not the framework

| | |
|---|---|
| S1 placement | where the fresh `r` for a term is bound. FOUNDATION §2 requires the proof's interior to correspond step for step, which needs ONE `r` per distinct term — so hoisted, not per atom. The framework already gives what the pass needs: statement-level parameters and `shift` |
| meta functions | a meta-level function (a λ of type `i ⇒ i`, e.g. `RepFun(A, λx. f(x))`) is encoded as a FUNCTION CLASS — its graph — not refused |

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
| whether the ZF primitive surface is a third dialect or a stage inside IsaDialect | parked where you left it |
| what `base/` becomes | it is `.fol.def` text today; does FolDialect *read* it, or is it opaque input to the checker? |
