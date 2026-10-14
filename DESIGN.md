# isa2fol — package layout and dialect types

**The structure, section by section.** Each heading's status says what is built.

---

## 1. Package layout

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → a hash-consed forest.  Knows no dialect.
  IR/            §4's framework: Node · Table · transform · index engine · passes · legalize
  FolDialect/    Declaration · render (formulas and proofs) — the text boundary over IR (§3)
  Reader/        the export → isa nodes, statements and proofs (§2)
  Lowering/      the plan (§4a): Expand · Logic · Reify · Fol, and Typing's registry
  isa2fol/       CLI
Tests/
  YXMLTests/  FolDialectTests/  IRTests/  ReaderTests/  LoweringTests/
```

```
  YXML  ─►  Reader  ─►  IR  ─►  Lowering  ─►  FolDialect
```

**The reader, the unit's citations and lemmas, and Fol's binders and variables at `i` are built**; Expand, Logic,
Reify, the provers (§4a) and the emission of a unit are not.

### Two rules that make the guarantee real

1. **No `default:` in a switch over an IR enum.** One `default` and adding a
   variant stops breaking the build — which is the entire mechanism.
2. **IR enums stay `internal` to their module** (or `@frozen`). Across a
   library-evolution boundary Swift permits `@unknown default`, reopening what
   rule 1 closes.

Worth writing down the way the comment cap is: they are cheap, and forgetting
either is silent.

---

## 2. Reading the export  **[BUILT]**

**Measured, one build** (`swift build -c release && .build/release/isa2fol read data/zf_export`,
59 s, 3.5 GB peak — the parse of the 3.1 GB file): of the 9,420 named theorems of the eight exported
sessions, **ALL 9,420 are PROVED** — statement and proof read AS ISABELLE STATES THEM, type
variables and class premises included (§4.3a 3, 5), and the proof's conclusion is the statement's
node, BY ID, with every step typed by the table (§4.7). The 200 named Pure/IFOL/FOL theorems their
proofs reach are all proved too. **0 refused.** A
proof whose conclusion is not its statement stops the run as `MalformedExport.unproved`.
`--show OUTCOME` lists the theorems with an outcome.

**It produces isa nodes in the unit's formula table (§4.2), and it RECOGNISES —
it never transcribes raw `ZApp`.** `ZApp(ZApp(ZConst "Pure.imp", a), b)` is read as
one `imp` node; connectives and binders are node kinds, not application spines.

**The dialect covers the WHOLE EXPORT, built downstream-first** (principle agreed 2026-09-25).
Every statement and proof of the exported sessions reads into it, the cited Pure/IFOL/FOL
layer included. FOL's surface is the base; from IFOL only what FOL cannot express is
imported; from Pure only what IFOL cannot. A construct the downstream surface covers is READ AS
the downstream construct — Pure's `⟹` is `folImplies`, never a kind of its own. ZF's own
vocabulary — constants applied to their arguments — is the generic term language (§4.3).
Every term is read in ONE canonical form: η-long (below; β-normal is proposed in §4.3a).
**The reader rejects only a MALFORMED export** — what Isabelle's encoder does not write.
Whether a construct TRANSLATES is lowering's question, decided against FOUNDATION and counted
there. ⚠ An earlier version called the dialect "the ZF surface" and REFUSED what was rare in
the 3,616 named theorems — a count justifying a specification — then reported those refusals
as the corpus's limits (98.1% of statement files).

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

**The surface it must cover is measured** — `docs/SOURCE_SURFACE.md`, generated by
`isa2fol surface data/zf_export` from the reader's own output: every pattern it emits (§4.3b 5), over the
named theorems of the ZF sessions, everything they cite and the definition of every constant that occurs.
⚠ **A CENSUS COMPUTED APART FROM THE READER DIVERGES FROM IT, SILENTLY**: a Python script walked through
class discharges and saw no `OFCLASS`; the decoder census that followed dropped every type, so `dummy` first
surfaced as reader refusals. The census is the reader's patterns, counted.

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
| **types** | The reader decodes `ztyp` into ITS OWN type, which has `'a` and `prop`. A `ZConst` carries only its type ARGUMENTS (`ZConst1 (a, b) => ([a], list ztyp [b])`, `zterm.ML`'s encoder), so `isaConst`'s instantiated type is the declared scheme from `theory/consts` (`IFOL.eq :: ['a, 'a] ⇒ o`) with those arguments substituted. A file is read AT AN INSTANCE of its `tfrees` header: a named theorem at its own variables — AS STATED, `'a` is `IRType.variable` — an unnamed box at the types its citation gives (§4.3a 3). A type variable the header does not declare is malformed; so is a sorted one — `unconstrainT` made every sort an `OFCLASS` premise. `IRType` has no `prop`: **`prop` converts to `o` in EVERY type** — the coercion is the identity (§4.3). ⚠ Refusing `prop` anywhere split one construct in two — 6 vs 194 theorems for variables, then 192 for constants. `dummy` — `standard_hidden_types` writing every type variable only a proof uses — is ONE type variable, `IRType.variable("dummy")`: the export no longer tells them apart. ⚠ Reading it as `i` chose a type in the reader, which is translation's (§4.3a 3) |
| **frees** | **Read CLOSED.** A statement is `∀x⃗. φ` over the `frees` header — Isabelle's closure (`forall_intr_variables_term`, and `prop_of_atom` for a cited axiom or theorem, `proofterm.ML`), the first free outermost — and its proof is `⋀`-intro over the same `x⃗`. A free `ZVar` reads as the bound variable of its closure binder: the frees are the outermost binders of the file's `Scope`. So a cited statement is the SAME node as the citer's `use`, and the citation's `ZAppt`s instantiate it — checked by ID across every proof. ⚠ Closing in a later pass was the plan; it rewrites the whole proof DAG once per binder depth, where reading closed costs nothing |
| **outcomes** | The READER owns them, never IR: `proved(statement, proof)` · `refused(reason)`. ONLY the reader's own refusal enum is caught and recorded; a `TableError`, `MalformedExport` or `YXMLError` is a bug or a corrupt file and stops the run, located at the innermost file — catching it would count our bugs as refusals |

### What the reader rejects

Only a malformed export (`MalformedExport`): a shape Isabelle's encoder does not write, a ZBound
with no enclosing binder, an ill-typed position, a frees header that is not the proposition's
frees. Every construct today's reader still REFUSES is listed in §4.3a with the reading that
replaces its refusal.

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

## 4. IR  **[FRAMEWORK BUILT]**

**§4.2–§4.7's framework is built** (`Sources/IR`, `Sources/FolDialect`, pinned by
`Tests/`); the reader (§2) and Fol (§4a) are built on it. The previous region graph — formulas edited in place through `replaceAllUses`/`insert`/
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
  Built: `Unit.refused` records `(name, pass, refusal)`, and a refused statement leaves
  `Unit.statements` (§4a).
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
| IFOL `conj` `disj` `imp` `False` — leaves | yes | `folAnd` `folOr` `folImplies` `folBottom` |
| IFOL `iff` `Not`, Pure `prop` — DEFINED | no — coverage is for leaves only (§4.3b) | `isaConst(.defined(…))` |
| Pure `⟹` | yes — the target has one implication | `folImplies` |
| `Trueprop` | yes — the `o ⇒ prop` coercion is the identity once `prop` is `o` | erased |
| Pure `≡` at `o` or `prop` | yes | `folIff` |
| IFOL `∀x:T` / `∃x:T`, Pure `⋀x:T` | **no** — a set quantifier owes the R3 guard, a class one does not | **`ifolAll(T, body)`, `ifolEx(T, body)`** — the only dedicated imports |
| IFOL `eq[i]`, Pure `≡` at `i` | no — `folPred` takes variables, these take terms until S1 | `isaConst(.primitive(.ifol(.eq)), …)` |
| `True`, `Ex1`, `Let`, `Uniq` | no — defined constants | `isaConst` |
| Pure `≡` at a function type — definitions `f ≡ λx. t` — or at a type variable | not by FOL or IFOL | `isaConst(.primitive(.pure(.eq)), …)`; a definition is consumed by S2 |
| Pure `⋀` at a function type | not by FOL or IFOL; S5 | `ifolAll(T, body)` at the function type — S5 is a pass |
| Pure's defined `&&&` `TERM` `sort_constraint` · `_` (`dummy_pattern`) | no · it is no constant | `isaConst(.defined(.pure, …))` · `isaFree(.hidden, T)`, a variable only the proof uses (§4.3b) |
| `OFCLASS(T, c)` | no — FOL has no types | `isaOfClass(T, c)`, the export's own form (§4.3a 5) |

**The quantifier is the one dedicated import because the guard is the calling
convention (§4a).** Everything else is a relabel or data S1/S2 treat alike; as data,
`isaConst(…IFOL.All…)` would be matched by a name, and a quantifier the
lowering missed would silently change every signature. As a kind, rule 11 covers it.

The generic term language — ZF's own vocabulary, not logic at any level:

| node | source | added | left out |
|---|---|---|---|
| `isaConst(Constant, T, args)` | any constant not read as logic above, fully applied, typed (§4.3b): a primitive (`IFOL.eq`, ZF_Base's six, `Pure.eq` at a function type or a type variable), a defined constant (every one `theory/constdefs` defines), or a declared one (a theory's own parameter) | its INSTANTIATED type `T` — it determines the type arguments and back, so the identity is the same | the declared scheme (`IFOL.eq :: 'a ⇒ 'a ⇒ o`): the READER instantiates it from `theory/consts` at the use's type arguments — the file's own variables where it is generic |
| `isaFree(.hidden, T)` | `Pure.dummy_pattern`: a variable only the proof uses (§4.3b) — a free `ZVar` of the statement reads as its closure binder's `isaBound` (§2); `.named` is the index engine's (§4.4) | | |
| `isaBound(k, T)` | `ZBound k`, and a free `ZVar` under its statement's closure | **the type**, from the enclosing binder or the `frees` header | |
| `isaVarApp(head, args)` | a variable applied — a class variable `P(x)` | | the head is an `isaFree` or `isaBound`, never merged into the constant namespace (rule 3) |
| `isaAbs(T, body)` | `ZAbs`, ONLY as a function-typed argument: `Collect(A, λx. …)` | | **`x`** |

`IRType` has no `prop` case (§2). A type variable is `IRType.variable` (§4.3a 3), a class premise
`isaOfClass`, a schematic `Var` malformed (§4.3a).

**The fol side mirrors fol-zfc** (`src/core/formula.h`): a term is a bound variable
(de Bruijn) — fol-zfc's FIXED variables are emission's concern, not a node kind (§4.7);
a formula is a predicate over terms, a
connective, or a quantifier over a body. **The set/class binder kind is NOT
identity** — the checker cannot see it, and `∀A. (set(A) → ψ)` is valid text for
both. It is the translator's bookkeeping, known where lowering builds the binder.

### 4.3a The isa surface, from the verified primitives — ACCEPTED 2026-09-25

**Built, statements and proofs.** Point 3 was reopened and rebuilt 2026-09-25: the closure showed
every CITATION has a ground type, not every theorem. Evidence, eight exported sessions, 9,420 named
theorems: `isa2fol surface data/zf_export` (`docs/SOURCE_SURFACE.md`) and `isa2fol closure
data/zf_export` (`docs/CLOSURE.md`). Principle: read FAITHFULLY, then one pass per construct.

**1. Proof primitives — what every proof rests on.** The closure follows every citation of every
named theorem down to axioms: the set below is exhaustive, and there is no oracle.

| primitive | # | read as | lowered to |
|---|---:|---|---|
| Pure proof steps: ⋀-intro, ⋀-elim, ⟹-intro, ⟹-elim, hypothesis | 5 | `isaAllIntro`, `isaAllElim`, `folImpliesIntro`, `folImpliesElim`, `hyp` (§4.7) | `forall_intro`/`forall_elim` with the R3 guard, `implies_intro`/`implies_elim` |
| IFOL natural deduction: `impI mp conjI conjunct1 conjunct2 disjI1 disjI2 disjE FalseE allI spec exI exE` | 13 | `use` of the axiom | the kernel rule, one to one |
| IFOL equality: `refl`, `subst` | 2 | `use` | `base/` lemmas — `eq` is a defined predicate there |
| IFOL bridges: `eq_reflection`, `iff_reflection` | 2 | `use` | trivial: `≡` already reads as `=` at `i` and `↔` at `o` |
| `FOL.classical` | 1 | `use` | `classical_absurd` |
| Pure equality: `reflexive symmetric transitive combination abstract_rule equal_intr equal_elim` | 7 | `use` | `↔`/`=` reasoning and congruence — S2's CONG; `abstract_rule` under a binder. The simplifier's rewriting: 81–94% of theorems reach these |
| definitions: Pure `prop conjunction term`; IFOL `iff not True ex1 Let term_class`; FOL `induct_*`; ZF 984 | 997 | `use` of a `*_def` axiom | S2/S3 — conservative |
| ZF axioms: ZF_Base's 6, `AC.AC`, 5 in the example theories `Language`, `Static`, `LList` | 12 | `use` | the target's axioms |

**2. A derived rule is a theorem, not a primitive.** The 131 derived Pure/IFOL/FOL rules proofs cite
— `swap`, `ccontr`, `conjE`, `allE`, `TrueI`, `IFOL_simps(n)`, `protectI`/`D`, `conjunctionI`/`D1`/`D2`,
… — are READ from their own proofs like any theorem, as stated. They use no
construct beyond those below.

**3. A type variable is a surface primitive — BUILT 2026-09-25.**

⚠ **THE FIRST BUILD READ EVERY FILE AT A GROUND INSTANCE** — a theorem's type variables
substituted before reading, `dummy` read as `i` — on the argument that no citation leaves a type
variable open (`docs/CLOSURE.md`: 0). THAT COVERS CITATIONS, NOT THEOREMS: a theorem nobody cites
had no instance and was in no table — 7 of the 23 named ZF theorems that state a type variable
(`AC_Equiv.ex1_two_eq`, `Arith.eq_cong2`, `Ntree.maptree_induct`, `Ntree.maptree2_induct`,
`QPair.expand_qsplit`, `ZF_Base.strip(2)`, `pair.expand_split`; names by a probe, not kept). And
choosing a type is a TRANSLATION decision — it exists because FOL-ZFC is one-sorted — which this
section's principle keeps out of the reader.

Isabelle's side:
- A theorem with `'a` holds at every type. `split :: [[i,i] ⇒ 'a, i] ⇒ 'a` applies a two-argument
  `c` to a pair's parts; one `split_def` serves `c` returning a set, a formula or a function.
- A citation is a theorem and ONE TYPE PER TYPE VARIABLE of it — `ZConstp`'s type arguments. It
  proves the statement at those types (`prop_of_atom prop Ts`, `proofterm.ML`); ⋀-elim then
  supplies the terms: `split_def [o] · R`.
- In a generic proof the types are the proof's own variables — `pair.split` cites `split_def` at
  `'a` — so a concrete type is decided by a ground theorem at the top and flows down:
  `pair.split_type` cites the box holding `pair.split`'s proof at `i`.
- Every type variable is written with the EMPTY sort — all 38,923 proof-file headers, 578 with a
  type variable, 0 with a sort (a throwaway scan, not kept): `unconstrainT` made each sort the
  `OFCLASS` premise (5).
- A type variable only a proof uses is written as the type `dummy` (`standard_hidden_types`,
  `zterm.ML`) — in 3 named ZF theorems' proofs: `DPow'_reflection`, `satisfies_MH_reflection`,
  `formula_rec_lambda_replacement_Reflects`.

| | built |
|---|---|
| **3a. `IRType.variable(name)`** | a `tfrees` header variable, and `dummy` — ONE variable: the export no longer tells hidden variables apart, and identifying them is a type instance of the proof. No sort: the export has none, and a sorted one is malformed, as is an undeclared one or a header declaring `dummy`. A named theorem is read AS ISABELLE STATES IT, and its proof checked by ID; there is no `polymorphic` outcome. `≡` at a type variable stays `Pure.eq` — nothing covers it |
| **3b. A citation carries its types** | `use(cited, types, root)` — `types` the citation's type arguments, possibly the citer's own variables; `root` the cited statement READ AT `types`, which is what Isabelle's citation concludes. At the cited theorem's own variables `root` IS its statement, the same node. An unnamed box is inlined as now, read at its citation's types |

Unchanged: `prop` reads as `o` in every type; `itself` stays out — `OFCLASS` is the export's own
form (5); the 7, read for the first time, refuse nothing.

3a and 3b lose nothing: the table holds each theorem as stated and each citation with its types.
What translation makes of a generic theorem — FOL-ZFC is one-sorted — is translation's to decide.

**4. The surface is ONE TO ONE with the isa dialect, after coverage.** A LEAF is COVERED when
FOL has it natively; it then reads as FOL's, the SAME node. A defined constant is never covered (§4.3b):
`↔` and `¬`, which IFOL defines, read as defined constants. Pinned by
`aCoveredLeafReadsAsItsCover`; the reader emits no node kind outside this table
(`theReaderEmitsOnlyTheIsaDialect`: every node it emits has `.isa` in its pattern's `dialects`).

| surface primitive | the Isabelle constructs it covers | isa dialect |
|---|---|---|
| implication | IFOL `⟶`, Pure `⟹` | `folImplies` |
| conjunction · disjunction · falsum | IFOL `∧` · `∨` · `False` | `folAnd` · `folOr` · `folBottom` |
| bi-implication | Pure `≡` at `o`/`prop` | `folIff` |
| `∀` / `∃` at a type `T` | IFOL `∀`, Pure `⋀` / IFOL `∃` — at `i`, `o` or a function type | `ifolAll(T)` / `ifolEx(T)` |
| a constant applied | every other constant: ZF's; `=` (IFOL `eq`, and Pure `≡` at `i`); Pure `≡` at a function type or a type variable; the defined `↔ ¬ True Ex1 Let Uniq induct_*`; Pure's defined `PROP &&& TERM sort_constraint` | `isaConst(Constant, T instantiated)` |
| a variable only the proof uses | `Pure.dummy_pattern` (`standard_hidden_terms`) | `isaFree(.hidden, T)` |
| a bound variable · a variable applied · `λ` | `ZBound`, and a free `ZVar` — its statement's `∀`-closure binds it (§2) · `ZApp` headed by a variable · `ZAbs` as a function argument | `isaBound` · `isaVarApp` · `isaAbs` |
| `⋀`-intro · `⋀`-elim | `ZAbst` · `ZAppt` | `isaAllIntro` · `isaAllElim` |
| `⟹`-intro · `⟹`-elim | `ZAbsp` · `ZAppp` | `folImpliesIntro` · `folImpliesElim` |
| a hypothesis | `ZBoundp` (a free `ZHyp`: 0 in the export) | `hyp` |
| a citation | `ZConstp` — an axiom or a NAMED theorem, with its type arguments; `root` is its closed statement read at them | `use(Cited, types, root)` |
| an unnamed box | `ZConstp` of a theorem with no name — logically not a building block | INLINED: its closed proof, read at its citation's types |
| a type variable | a `tfrees` header variable; the type `dummy` | `IRType.variable(name)` |
| class membership | `OFCLASS(T, c)` — a class premise, a class hypothesis, a class fact | `isaOfClass(T, c)` |

**Not a surface primitive, so no construct:** `Trueprop`, the identity coercion, erased. `protect` (`Pure.prop`)
is Pure's defined identity, read as defined (§4.3b). A schematic `Var` is MALFORMED (`standard_vars` removes every one).

**5. `OFCLASS` is a surface primitive — BUILT 2026-09-26, replacing absorption (the user chose it
over putting the class back on the type variable).**

⚠ **THE FIRST BUILD ABSORBED CLASS BOOKKEEPING** — a translation decision made in the reader, as
reading at a ground instance was (3): it dropped class premises, their discharges and class
hypotheses because `IFOL.term` has no axioms, so membership says nothing. It lost
`ZF_Base.arity_term_i`, the one named theorem not read; and, on a generic theorem, the only record
that its `'a` may be only `i` — 8 of the 23 generic named ZF theorems carry `OFCLASS('a, term)`,
15 are `'a::{}`, and absorbed the two were indistinguishable.

Isabelle's side:
- A class is a named set of types. IFOL declares `=`, `∀`, `∃` at `'a::term` (`class "term"`,
  `default_sort term`); ZF puts one type in it, `instance i :: "term"` (`ZF_Base.thy:17`), which
  Isabelle records as the theorem `ZF_Base.arity_term_i : OFCLASS(i, term)`.
- A proof makes the class explicit (`unconstrainT`): `IFOL.refl`, printed `(?a::?'a::term) = ?a`,
  is exported `OFCLASS('a, term) ⟹ a = a`, and a use at `i` discharges the premise with a box that
  cites `arity_term_i` — in 6,599 proof files.
- Membership is DEFINED as trivially true — `IFOL.term_class_def : OFCLASS('a, term) ≡ (⋀P::prop.
  P ⟹ P)` — `term_class.intro` proves `OFCLASS('a, term)` from it, and `arity_term_i` is that at
  `i`. Every `OFCLASS` is proved by citation, down to that axiom: the export has 0 `ZClassp`, a
  proof of `OFCLASS` from the sort algebra.
- 748 `OFCLASS` propositions in 464 of the 38,923 proof files, 432 of those files IFOL/FOL; every
  one is `IFOL.term` (a grep over the export, not kept). `OFCLASS` is the export's own term form
  (`ZClass`), not `term_class(TYPE('a))`, so no `itself` type is needed.

| | built |
|---|---|
| **5a. `isaOfClass(T, class)`** | a formula, type `o`, no children: `T` is in `class`. It is the export's own term form; spelled as a constant it would need `TYPE(T) :: T itself`, a type the dialect does not have. A class `theory/classes` does not declare is malformed |
| **5b. Nothing is absorbed** | a class premise is an ordinary premise, `isaOfClass('a, term) → …`; a class hypothesis an ordinary `folImpliesIntro`; a discharge an ordinary `folImpliesElim`. `arity_term_i` is a claim like any other, and proved; `classFact` stops being an outcome. A class with axioms is no longer refused — nothing is dropped, so no axiom can be |
| **5c. The census walks what the reader reads** | it absorbed too — 47,386 discharges. Walked: `OFCLASS` is in 9 named statements and 6,045 named theorems' proofs (`docs/SOURCE_SURFACE.md`); `IFOL.term_class_def` is reached by 7,965 (`docs/CLOSURE.md`) |

⚠ **A CITATION'S TERM ARGUMENTS COME BEFORE ITS CLASS DISCHARGES** — `head % terms %% discharges`,
because the statement's `∀`-closure is outermost. Absorption skipped proof arguments wherever they
sat, which hid two test fixtures written the other way round; the export has none.

A `ZClassp` — 0 in the export — stays refused by name. Lowering reads `OFCLASS` as METADATA —
Isabelle's type check, which the exporter made a premise: it checks the class and drops the premise,
its discharge and the proof behind it (§4a, decision 4).

### 4.3b The input layer: axioms and constants  **[DECIDED 2026-10-13 (user); BUILT 2026-10-13]**

**Pure, IFOL, FOL and ZF each contribute two mechanisms: AXIOMS, and CONSTANTS.** A constant is either a LEAF, which
only axioms constrain, or DEFINED, `c ≡ b`, built over leaves and earlier definitions for reuse. A theorem or a proof is
a composition of these, put together with §4.3a 4's formers: variables, `λ`, ⋀/⟹ intro and elim, hypotheses, and
citations. The input layer is the isa dialect, its patterns, its primitives (three names for one thing). It represents
these two mechanisms and those formers, and nothing else. If every pattern is translated, every theorem is (D1).

**Taken from `kinds-proposal`: kept where it did well, improved where a principle faults it.** Kept:
- **The reading** (§4.3a 4). A leaf that FOL has is read as FOL's node. `⋀`/`∀`, `⟹`/`⟶` and `≡`/`↔` at `o` are one
  node each, so no proof bridges Pure and IFOL. A defined constant is read as defined (IFOL's since `21937219`).
- **Constants and axioms are typed values, by layer**, under the reference's names: `Constant`, `Primitive`, `Family`,
  `Axiom`, `Cited`. `meta` and `lambda` are dropped, because they are lowering's. A defined constant keeps its declared
  level instead (§4a "Expand", point 6): a fact of its declaration, which lowering decides by, never a family.
- **A theory's family comes from its ancestry** (`theory/parents`). A definition of a listed leaf is malformed.
- **`Pattern` is built by one rule over every node kind** (point 4).
- **A proof's conclusion is its statement, by ID.**

| the reference | here | principle |
|---|---|---|
| `Pure.dummy_pattern` is a `Primitive.pure`, and reify refuses it by name (`pureConstant`) | `isaFree(.hidden, T)`: the variable only the proof uses | §4.3: a node's meaning follows from the node alone |
| ZF-Coind's and ZF-ex's own parameters are `Primitive.zf`, and their axioms `Axiom.zf` | `declared` and `theoryAxiom` | I1. R1 admits nothing beyond the 19, and these are not ZF's |
| an unlisted leaf or axiom REFUSES the theorem (`Com.loc`: 102 theorems) | an unlisted leaf or axiom of the foundation STOPS the read; above the foundation nothing needs listing | D2: the reader never decides what translates, and a gap fails at its provider |
| `Pure.prop` is erased, marked pending ("until Pure's own step (2b)") | `Pure.prop` is read as defined, like `↔` and `¬`: coverage applies to leaves only | D1: one rule per piece, with no pending exception |
| `isaDefinition(_, of: Constant)`: a definition of a primitive is representable, and checked at load | `isaDefinition(_, of: Defined)` | I1 |
| the census has its own model of the export (`Piece`/`Shape`, types in categories; `Item` here, keyed by name), and CLOSURE classifies a definition by its name | both count patterns over the reader's output (point 5) | D3, D1: the pieces rules are owed are the patterns the passes see |
| `Pattern` is a report (per-stage sets, where a refusal happened); passes test single cases with `if case`, and none dispatches by an exhaustive switch over it | the reader's output set is its contract, tested; each pass states its sets in its own step | I3 |

**The contracts (D2):**

| component | provides | assumes |
|---|---|---|
| IR | the vocabulary: `Constant`, `Cited`, `Pattern`, and `Node`'s input kinds | — |
| Reader | every named theorem as `(statement, proof)`, with `conclusion(proof) == statement` BY ID, with each theorem they cite at no type arguments and each definition they reach (§4a, "The unit and its citations"). Every node it emits is of the isa or both dialect. Every constant and citation is a typed value. `isaFree(.hidden, _)` occurs in proofs only. It makes no translation decision beyond the coverage of leaves | an export of one build; every leaf and axiom of the foundation that occurs is listed, else the read STOPS (point 3) |
| Lowering | each component's business, and each pass's sets by what it owns: §4a, "Lowering's components" (PROPOSED) | the reader's row; the first pass's input set is the reader's output set |

**1. The typed values (I1), each in one home (D3).** The MEANING lives in IR, which every pass reads. The export's
SPELLING (which name is which leaf, what `theory/constdefs` defines) lives in the Reader, which alone reads the export.

```swift
// IR
enum Family    { case pure, ifol, fol, zf }
enum Primitive { case pure(Pure), ifol(IFOL), zf(ZF) }     // the leaves the target lacks
//   pure: eq · ifol: eq · zf: mem zero Pow Union PrimReplace Inf
enum Level     { case object, meta }                      // meta: the declared type mentions `prop` or a type variable
struct Defined { let family: Family; let name: String; let level: Level }
enum Constant  { case primitive(Primitive), defined(Defined), declared(String) }
enum Axiom     { case pure(Pure), ifol(IFOL), fol(FOL), zf(ZF) }
//   pure: reflexive symmetric transitive combination abstract_rule equal_intr equal_elim
//   ifol: refl subst impI mp conjI conjunct1 conjunct2 disjI1 disjI2 disjE FalseE allI spec exI exE
//         eq_reflection iff_reflection · fol: classical
//   zf:   extension replacement Pow_iff Union_iff foundation infinity, AC.AC
enum Cited     { case theorem(String), isaDefinition(String, of: Defined), axiom(Axiom), theoryAxiom(String) }

// Node, changed
case isaConst(Constant, IRType, args: [NodeID])   // was String
case use(Cited, [IRType], NodeID)                 // was String
case isaFree(Free, IRType)                        // Free: .named(String) | .hidden — was isaFree(String, IRType)
```

- A case's raw value is Isabelle's name, which emission writes unchanged (rule 5).
- `Cited` holds what the reader cites, and `lemma(r)`, a lemma's request (§4a, "The unit and its citations"). Base's
  claims are added in the first step that cites base.
- `folNot` moves to the fol-only group: with `¬` defined, the reader no longer emits it.
- ⚠ **THE HIDDEN VARIABLE IS `isaFree(.hidden, T)`, NOT A NEW KIND.** The agreed text proposed `isaHidden(T)` to
  replace `isaFree` as dead. `isaFree` is not dead: the index engine's `abstract` closes over it (§4.4). A variable
  only the proof uses IS a free variable, so it is that kind, its identity typed: `.named` for the index engine's,
  `.hidden` for the reader's, which has no name.

**2. The reading: how a name is read is ONE function in the Reader, and the foundation is ONE table.** The table is
the reference's: `Pure` pure, `IFOL` ifol, `FOL` fol, `ZF.ZF_Base` zf. A theory in the table is in the foundation. Any
other theory's family is `zf` when it descends from `ZF.ZF_Base`.

| a constant name | read as |
|---|---|
| a leaf FOL covers: `Trueprop` · `Pure.imp`, `IFOL.imp` · `conj` · `disj` · `False` · `Pure.all`, `IFOL.All` · `IFOL.Ex` · `Pure.eq` at `o` | erased · `folImplies` · `folAnd` · `folOr` · `folBottom` · `ifolAll(T)` · `ifolEx(T)` · `folIff` |
| `Pure.eq` at `i` | `isaConst(.primitive(.ifol(.eq)))` |
| a `Primitive` | `isaConst(.primitive(p))` |
| `Pure.dummy_pattern` | `isaFree(.hidden, T)` |
| a constant `theory/constdefs` defines: IFOL's `↔ ¬ ∃! True`, Pure's `PROP &&& TERM`, and every ZF definition | `isaConst(.defined(Defined(family, name, level)))` |
| an undefined constant of a theory outside the foundation | `isaConst(.declared(name))` |
| an undefined constant of the foundation, none of the above | the read STOPS: `DialectGap.leaf(name)` |

| a cited axiom | read as |
|---|---|
| an `Axiom` | `.axiom(a)` |
| a definition (`theory/constdefs`) | `.isaDefinition(name, of: its constant)` |
| an axiom of the foundation, none of the above | the read STOPS: `DialectGap.axiom(name)` |
| an axiom of any other theory | `.theoryAxiom(name)` |

A named theorem is read as `.theorem(claim name)`.

⚠ **`Pure.dummy_pattern` IS NO CONSTANT.** The exporter's `standard_hidden_terms` (`src/Pure/zterm.ML:1574`) writes
every variable that a proof uses but its proposition does not as `dummy_pattern`, at the variable's type. It is the
term twin of the hidden type `dummy` (§4.3a 3), and like `dummy` it is ONE variable per type. That is sound, because a
proof stays a proof under substitution for its free variables. The exporter merged the names away, so it has none.

⚠ **A THEORY'S OWN PARAMETER IS NOT A ZF LEAF.** These are `declared`:
- ZF-Coind's `Language.Const`, `c_app` and `ExVar` (`axiomatization`: "these really can't be definitions"),
  `Static.isof` and `Types.TyConst`;
- ZF-ex's `LList.flip`;
- ZF-IMP's `Com.loc`.

Their axioms `constNEE`, `c_appI`, `isof_app`, `flip_LNil` and `flip_LCons` are `theoryAxiom`s. Filed under ZF, they
would give the switch over ZF's axioms a case whose only rule is a refusal (D1). What a theorem resting on them becomes
is lowering's question.

**3. A gap in the dialect stops the read; it is never a refusal.** A refusal would skip theorems silently. A gap is
fixed by adding the case. Abbreviations (`IFOL.not_equal`, `ZF_Base.not_mem`, …) and Pure's proof-term constants
(`Pure.Appt`, …) are declared and undefined but never occur. So the check is made where a name is read, never over the
whole declaration list.

**4. A pattern is a primitive at its `IRType`.** One primitive used at several types gives several patterns.
`Pure.combination` at `'a, 'b :=` `i, i` · `i, o` · `o, o` is congruence at a function, at a predicate and at a
proposition: three cases, three encodings in NBG, and none can be missed. There are no type categories: a pass that
decides by a type switches over `IRType`'s own constructors and recurses into `fn`.

**Every pattern is built by ONE rule, the reference's** (`kinds-proposal:Sources/IR/Pattern.swift`). Take the node and
replace each child by its type (a proof step by `o`), and a list of children by the list of their types. Replace a
constant or a citation by its kind. Drop names, de Bruijn indices and class names (D1: a rule never keys on a name, the
primitives excepted). A constant's kind is `primitive(p)`, `defined(family, level)` or `declared`. A citation's kind is
`theorem`, `isaDefinition(family, level)`, `axiom(a)` or `theoryAxiom`. For example:
- `isaConst(c, T, xs)` gives `isaConst(kind, T, args: types of xs)`;
- `isaAllElim(p, x)` gives `isaAllElim(o, type of x)`;
- `use(c, Ts, r)` gives `use(kind, Ts, o)`;
- `folPred(_, xs)` gives `folPred(args: types of xs)`.

The rule decides nothing per kind, so it covers every node kind, fol-only ones included. A list stays a list (the
reference made it a set): ordered, it prints the same every run (§4.6) by Swift's own description of an enum, with no
hand-written one per case.

⚠ **A FOL NODE CAN CARRY A TYPE.** `folPred`'s arguments and `folExistsIntro`'s witness are variables, and a class
variable is at `i ⇒ o` (`Table.expectTermVariable`). A pattern built from the kind alone loses that type.

`Pattern(node, in: table)` is that rule, in IR. Every node kind has a pattern, so a pass's input and its output can each
be stated as a set of patterns (I3). A switch over `Pattern` has no `default` (rule 11). The reader's output set is the
patterns of the isa and both dialects, which `Pattern.dialects` states and `theReaderEmitsOnlyTheIsaDialect`
tests. How a pass states its sets, and where they are checked: §4a, "Lowering's components".

**5. The census counts patterns** (`Reader.census()`, `Sources/Reader/Census.swift`). Its population is the
reference's: the named theorems of the ZF sessions, everything they cite, and the definition of every constant that
occurs, transitively. A count is the named theorems whose closure holds the pattern. `docs/SOURCE_SURFACE.md` lists
every pattern the reader emits. `docs/CLOSURE.md` lists the citations of axioms, definitions and theory axioms. Both
are computed from the reader's output; the decoder census (`Sources/Reader/Surface.swift`) is deleted. D1's pieces
are then exactly the patterns the passes switch over.
⚠ **A DEFINITION'S STATEMENT `c ≡ b` NAMES ITS OWN CONSTANT**: its closure leaves `c` out, or the walk revisits the
definition forever (it filled 32 GB before the fix). A constant reached again while it is open throws `cyclicClosure`.

**Pinned by:** `theCoveredLeavesReadAsFolNodesAndADefinedConnectiveAsDefined`,
`truepropIsErasedAndPropIsADefinedConstant`, `dummyPatternReadsAsTheHiddenVariable`,
`anUnlistedLeafOfTheFoundationStopsTheRead`, `eachKindOfConstantHasItsReading`,
`theExportsConstantsReadByTheirTheoriesAndDefinitions` (on the export: `Com.loc` declared, `IFOL.not_equal` a gap),
`aVariableOnlyTheProofUsesIsTheHiddenVariable`, `aCitedAxiomIsTypedByWhatItIs`,
`anUnlistedAxiomOfTheFoundationStopsTheRead`, `onePrimitiveAtSeveralTypesIsSeveralPatterns`,
`aFolPatternKeepsItsArgumentsTypes`, and the census's three tests.

**Measured** (whole export): `read` proves all 9,420 and the 200 theorems they cite outside the ZF sessions, 0
refused, the read never stops — in 62.8 s, as before; the guard lowers 2,685 and refuses 6,735, unchanged; the census
holds 2,592 patterns, `Pure.combination` alone at 281 instances, and finishes in 76 s at the read's 3.5 GB.

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
| `instantiate(body, t)` — a binder was removed | `k = d` → `t` shifted by `d`; `k > d` → `k − 1` | — | `forall_elim`, `exists_elim`, β-reduction: `beta(f, args)`, one `instantiate` per argument |
| `abstract(φ, x)` — close over a name | `k ≥ d` → `k + 1` | `x` → `d` | closing a statement over its frees |

The guard needs none: `∀. body` → `∀. (set(0) → body)` leaves the body at its depth.

```
  S1:           ∀. mem(f(0), 0)          →  ∀. ∀. ( F(1, 0) → mem(0, 1) )      old x: 0 → 1 under the new r
  forall_elim:  ∀. ∀. (mem(1,0) → mem(0,1)) at a  →  ∀. (mem(a, 0) → mem(0, a))  x is 1 inside the inner ∀
  capture:      ∀. mem(1, 0), x := z (= 0)  →  ∀. mem(1, 0), NOT ∀. mem(0, 0)     t shifted under y
  β:            (λ. mem(0, 1)) z             →  mem(0, 0)                          1 → 0: the λ is gone
  close x:      mem(x, A) → ∀. mem(0, x)     →  ∀. ( mem(0, A) → ∀. mem(0, 1) )     ONE node x: 0 here, 1 there
```

Frees close over the PROPOSITION's frees in first-occurrence order: free `i` of `n` at depth `d`
↦ `d + (n − 1 − i)`, the first outermost. That is Isabelle's own closure
(`forall_intr_variables_term`, `variables_of` in `proofterm.ML`), which fixes the order in
which every citation's `ZAppt`s instantiate — the proof reader's by-ID check confirms it over the
whole export. The reader closes by reading (§2): the frees are the outermost binders of a file's
scope, so no pass abstracts them and `abstract` has no caller. The `frees` header lists the same frees first
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
  Unit        the table + statements (theorems, lemmas) + definitions; a citation names a statement
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
    associatedtype Context: Hashable = Depth
    var start: Context { get }
    func enter(_ c: Context, _ binder: Node, _ binds: Binds, in t: Table) -> Context
    func narrow(_ c: Context, _ id: NodeID, in t: Table) -> Context          // default: c
    func before(_ id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
    func after(_ n: Node, context: Context, in t: inout Table) throws -> NodeID?
}
public func transform<R: Rule>(_ roots: [NodeID], _ rule: R, in t: inout Table) throws -> [NodeID]
public protocol Pass { var name: String { get }
                       func owns(_ p: Pattern) -> Owned?                 // .rule, .unbuilt; nil: not its own
                       func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] }
public protocol Registry { func prove(_ lemma: Lemma, _ statement: NodeID, _ definitions: [Definition],
                                      in t: inout Table) throws -> Proved }   // .proof(NodeID) or .unbuilt
```

- **A pass never writes its own recursion.** It supplies a rule for the kinds it handles;
  every other kind is rebuilt from its rewritten children.
- **A pass is one walk.** No rule writes a pattern its pass owns (§4a, "Lowering's components"), so a second
  walk would find nothing.
- **The traversal hands a rule its CONTEXT — what the binders above a node made of it.**
  A variable is a position, not a pointer, and a shared node has no parent, so the path
  exists only in the walk. `visit` calls `enter(c, binder, binds)` once per bound child —
  the child `mapChildren` marks, never `A` in `folImpliesIntro(A, body)` — on the way
  down; the context is a value passed down, so nothing pops it. The rule chooses the
  type and what an entry records; the framework records nothing. `Depth` is the default:
  `enter` adds the counts. Coq's kernel does the same with `push_rel`.
- **A pass may take arguments beyond the node** — its context from the traversal, and
  whole-statement parameters it computes from the root before transforming (the ordered
  frees that closing needs: one interned free-variable node becomes `bvar 0` at one
  site and `bvar 1` under an inner binder).
- **A pipeline** is the whole plan. It runs its passes in order, each over every statement's root AND its proof
  in ONE walk — one cache for the unit — and after each pass every proof must still
  conclude its root, BY ID — else
  `PipelineError.unproved` names the statement and the pass. Around every pass it checks the pass's sets
  (§4a, "Lowering's components"), adds every lemma the pass's output cites, and hands each definition to the pass that
  owns its constant; after the pass it names it asks the registry for each lemma's proof. After the last pass it calls
  `legalize`, and links: every citation names a statement, and a statement citing a refused one falls (§4a, "The unit
  and its citations").
- **A rule sees a node BEFORE its children, and a non-nil result replaces that subtree
  without descending into it.** Returning the node itself means "unchanged, do not
  descend" — how the index engine prunes a closed subtree (§4.4).
- **One cache per walk, keyed on `(node, narrowed context)`.** `narrow` is the rule's: the
  part of the context its rewrite of THIS node depends on — for a de Bruijn context, the
  binders from the nearest back to the farthest the node reaches (`looseBound`,
  `looseHyps`), so a closed node narrows to nothing and is rewritten once wherever it is
  shared. The node then sees ONLY the narrowed context — `before`, `after`, `enter` — so a
  rule cannot depend on what its key dropped. Measured over the 9,420 named proofs with a
  guard-shaped context (a throwaway probe, not kept): no cache, 2.4 × 10¹⁵ visits; keyed
  on the FULL context, one proof alone exceeds 150 M; narrowed, 93.6 M with a cache per
  statement and **4.1 M** with one per unit, against 2.6 M distinct nodes.
  ⚠ **A RULE MUST BE A FUNCTION OF (node, context, table)** — one with state sees each key
  once.
- **One unit per run**; imports arrive as text or a compiled library, as `proof_checker`
  loads them. So one table per process, and an out-of-range ID is the only foreign ID.

**Four exhaustive switches — adding a kind breaks exactly these** (rule 11):

| switch | its question | derived from it |
|---|---|---|
| **structure** — `mapChildren(node, f(child, underBinder))` | children, and which sit under a binder | children (`f` records), rebuild (`f` returns new), binder body, `looseBound` = max over children of `looseBound(child) − (underBinder ? 1 : 0)` |
| **bound variable** | is this a bound variable, at which index | the `k + 1` leaf of `looseBound`; the index engine's leaves |
| **type** | the node's type, and whether its children are well-typed | `intern`'s validation |
| **dialects** — `Pattern.dialects` | isa only, fol-zfc only, or both (a leaf FOL covers, §4.3a 4); `isaFree` is isa: the reader's hidden variable (§4.3b); a citation is fol-zfc's only of a theorem or a lemma at no type arguments | `legalize` — the seal; the reader's output is the isa dialect, pinned by `theReaderEmitsOnlyTheIsaDialect` |

⚠ **WHICH KINDS BIND EXISTS IN EXACTLY ONE PLACE — THE STRUCTURE SWITCH.** The traversal,
the index engine and `looseBound` all derive from it, so they cannot disagree. Separate
functions could, and the disagreement is D2's silent error: a binder one of them misses
has its body skipped by `shift`. The cost — "children" is read by rebuilding, allocating
for `isaConst`/`folPred`'s arrays — is an unmeasured constant factor.

**`render` is a FIFTH exhaustive switch** — an emitter must know every target kind's
text, so it cannot be derived; its source-kind cases throw. Adding a kind that can reach
the text costs five switches.

⚠ **`legalize` STAYS THE SEAL.** Every pass's ownership is an exhaustive switch over `Pattern`, so a new
kind breaks every pass until each answers it; `legalize`, at the pipeline's end, refuses what fol-zfc lacks.
`Node` declares its kinds in the dialects' groups, commented: the first two are the reader's output.

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
in the SAME table, lowered by the SAME `transform` as formulas. Its
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
| `Rule.after(node, context)` | the node with its REWRITTEN children, before `intern` — a step can only be rewritten once its premises have been, and `intern` would reject `isaAllElim(p′, a)`. `before` stays for pruning |
| conclusion at `intern` | the type switch computes it; a step whose principal connective is wrong cannot exist |
| D1 for steps | a hypothesis reference carries its formula, as `isaBound` carries its type; a citation carries its statement's root, imported into the table |
| two binder namespaces | term binders (`∀`, `λ`, ⋀-intro) and hypothesis binders (⟹-intro) number separately: the structure switch says which, `looseBound` is per namespace, and discharging a hypothesis is a proof-level `instantiate`. Isabelle counts the same way (§4.8) |
| emission | a proof tree becomes the checker's linear stack program — `folImpliesIntro(A, body)` → `assume A` … `implies_intro` — in `FolDialect`. A binder's scope is its body subtree, so `exists_elim` wraps a LOCAL subproof; nothing moves "the rest" |

**The step kinds — minimal: a checker rule is a kind only when something the source
contains needs it.** Every Isabelle proof bottoms out in Pure's constructors and in
citations; a citation is a step concluding the cited statement, so ONE kind covers every
axiom — how `use conjI` becomes `and_intro`, or `use combination` becomes CONG, is pass
detail.

| | kinds |
|---|---|
| neutral — concludes what it carries, any dialect | `use(cited, types, root)` (`PThm`/`PAxm` with its type arguments; `root` imported into the table) · `hyp(k, A)` (`PBound`; carries `A`, D1) |
| fol intro | `andIntro(p, q)` · `orIntroL(p, B)` · `orIntroR(A, q)` · `impliesIntro(A, body)` ◆ · `notIntro(A, body)` ◆ · `iffIntro(p, q)` · `forallIntro(body)` ● · `existsIntro(p, v)` |
| fol elim | `andElimL(p)` · `andElimR(p)` · `orElim(p, q, r)` · `impliesElim(p, q)` — `q` concludes the antecedent BY ID · `notElim(p, q)` · `iffElimL(p, q)` · `iffElimR(p, q)` · `forallElim(p, v)` — `v` a fol variable (S1) · `existsElim(p, body)` ●◆ · `bottomElim(p, C)` |
| fol classical | `classicalAbsurd(A, body)` ◆ — with `notElim` it covers FOL's one axiom, `(¬P ⟹ P) ⟹ P` |
| isa — the typed quantifier only | `isaAllIntro(T, body)` ● (`ZAbst`, produces `ifolAll`) · `isaAllElim(p, t)` (`ZAppt`, consumes `ifolAll`; `t` any isa term of type `T`, concluding `instantiate(body, t)`). They also cover `⋀P:o` and `⋀P:i⇒o` — instantiating a proposition or class variable, as citing an IFOL rule does |
| isa — lowering's | `isaGuard(x, G)`: the guard of the bound variable `x`, concluding the formula it carries, as `hyp` does; Fol makes it the assumption it writes at `x`'s binder (§4a, "Fol") |

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
- emission unfolds a shared subproof once per use — no memo; rewrites have one (§4.5).

**It links like a compiled language.** A claim is a signature, a proof a body, `use` a
call, an `UNPROVED` stub an `extern` — and **the R3 guard is the calling convention**:
every caller's `forall_elim` at `t` owes an extra `set(t)`.

### 4.8 Proof-level depth — SETTLED

A term `ZBound` inside a proof counts the enclosing `ZAbst` binders (⋀-intro) and NEVER the
`ZAbsp` ones (⟹-intro): Isabelle keeps two namespaces exactly as the table does. Measured over
all 38,921 proof files of the eight exported sessions, the 2 over 20 MB skipped: of 2,720,438
terms inside proofs, 1,791,509 are closed, 928,929 have loose indices all covered by enclosing
`ZAbst` binders, 0 need a `ZAbsp` binder, 0 are unresolved (a throwaway decode, not kept). So
the statement reader's `Scope` serves proofs unchanged: `ZAbst` is a source binder, `ZAbsp` is
not a term binder at all.

## 4a. Lowering passes  **[PASS 1 BUILT]**

**The statement is TRANSLATED, not passed through.** A declaration is not an
interface the proof reads unchanged — lowering changes the proposition's shape,
and the proof must be built against the changed one.

```
⋀x. (mem(x,y) ⟹ mem(x,y))     →     ∀x. (set(x) → (mem(x,y) → mem(x,y)))
```

**The passes.** Expand has its rules, and Fol has rules for binders and variables at `i`; the rest are declared,
unbuilt ("Lowering's components", below).

| # | pass | FOUNDATION | status |
|---|---|---|---|
| — | **expand** — the logic's defined constants unfolded, a citation of their definitions as `Pure.reflexive` | — | BUILT, below |
| — | **fol** — the binders and variables at `i`: a guard on each binder, fol-zfc's variables | R3, S6's enforceable form | BUILT, below |
| — | **logic**, **reify**, the rest of **fol** — the meta level lowered onto FOUNDATION §1a; each component's business in "Lowering's components", below | S1, S3, S4, S5, R3 | DECIDED, below; not built |

### Lowering's components  **[DIVISION DECIDED 2026-10-13 (user), TYPING A REGISTRY 2026-10-14 (user); THE INTERFACE AGREED AND BUILT 2026-10-13 — `Sources/IR/Pass.swift`, `Sources/Lowering`]**

**Each component minds its own business** (user, 2026-10-13). In the reference every component knew the others'
gaps (`kinds-proposal` DESIGN.md, "Step C by contracts", reasons 1–3). Here a piece belongs to one component, and a
component that meets another's piece calls that component or cites its lemma; it never handles the piece itself.

| component | its business | calls |
|---|---|---|
| **Logic** | the logic's own primitives. First `expand` — the reference's, kept, and extended to Pure's defined constants, which this reader reads as defined: every Pure, IFOL and FOL defined constant unfolded by its definition at the use's type, and a citation of that definition read as `Pure.reflexive`. Then IFOL's and FOL's rules as the kernel's steps, and Pure's rules and `≡` at every type, congruence included | — |
| **Reify** | S1: a compound term becomes a variable where it stands. It states and proves the EX and UNIQ of each function it names, by one walk over a term ("The unit and its citations", point 4), and nothing more | Typing, for guards; Tuple |
| **Lambda** | a wrapper: a λ's class is function reify's of its body | Reify |
| **Typing** | no pass. The registry: it hands each lemma to the component that states it. The guard each binder type gets (a set, a function, and so on); the typing lemmas, the discharges and the helpers | — |
| **Tuple** | the tuple's lemmas at every arity — the reference's, kept | base |
| **Fol** | every isa binder and variable becomes fol-zfc's: a binder with the guard Typing gives its type, an instance and the guard of a variable discharged by that variable's guard; then `legalize` | Typing |

⚠ **REIFY NEVER HANDLES A CONGRUENCE OR A BODY.** A congruence belongs to whatever produced it. It is Logic's where a
proof applies Pure's or IFOL's rules, and it belongs to the translation of a Pure or FOL constant where that constant
unfolds. The reference's reify walked both (`valueChain`, `isaCongruence`).

**The pass-sets interface (I3).**

1. **A pass owns patterns.** ONE exhaustive switch over `Pattern`, in the pass's own file, gives every pattern one of
   three answers:
   - **a rule**: the pass translates the pattern, and no instance survives the pass;
   - **unbuilt**: the pass owns the pattern but has no rule for it yet;
   - **not its own**: the pattern is rebuilt from its rewritten children.

   The same switch dispatches the pass's rules. A rule may rebuild a pattern it does not own (Fol renumbers a `hyp`
   under the guards it inserts), but it never writes one that its pass owns. A new `Pattern` case breaks every pass's
   build until each pass answers it. IR sees the switch as `owns(_ p: Pattern) -> Owned?`, where `Owned` is `.rule` or
   `.unbuilt` and `nil` means not its own. A rule's `enter` sees the table, so Fol decides which binder brings a guard
   by the same switch.
2. **The sets follow from ownership and the plan's order**, so nothing lists a set twice. A pass's input is every
   pattern that no earlier pass owns. Its output is every pattern that neither it nor an earlier pass owns. The reader's
   output is the first input (`theReaderEmitsOnlyTheIsaDialect`), and fol-zfc's patterns are the last output:
   `Pattern.dialects`, where a citation is fol-zfc's only of a theorem or a lemma at no type arguments.
3. **The pipeline checks the sets, so a failure lands at the provider.** The plan is declared whole: every pass is in
   the pipeline from the start, owning its patterns, and stays unbuilt until its step.

   | when | a statement holding … | is |
   |---|---|---|
   | before the first pass | a pattern that no pass owns and fol-zfc lacks | refused, naming every such pattern: a piece with no rule (D1) |
   | before a pass | a pattern the pass owns but has not built | refused at that pass, naming every such pattern (D2) |
   | after a pass | a pattern owned by that pass or an earlier one | a `PipelineError` that stops the run: a rule left its pattern, or wrote back an earlier pass's |

   Before all three, a pattern two passes own stops the run (`PipelineError.twoOwners`), checked on every pattern a run
   meets. After the last pass, `legalize` checks that each statement is fol-zfc. How a lemma enters the unit and is
   checked there: "The unit and its citations", below.
4. **A built rule never refuses.** What it cannot handle is either a pattern of its own, still unbuilt, or a lemma it
   cites, which the registry refuses (I2). So `transform` catches nothing and a pass returns node IDs.

**The owner of each of the reader's patterns**, from the division. The rows are coarse; each pass's step states its
own rows exactly.

| patterns | owner |
|---|---|
| a Pure, IFOL or FOL defined constant, or a ZF one at the meta level ("Expand", point 6); a citation of its definition | Logic, `expand` |
| a citation of a Pure, IFOL or FOL axiom; Pure's `≡` at a function type; a binder or an instance at any other type than Typing's (`o`, a function of propositions) | Logic |
| an applied constant (a ZF primitive, a ZF definition at the object level, a declared constant, `IFOL.eq`); an applied variable; a `λ`, through Lambda | Reify |
| a binder, an instance, a variable or the guard of a variable at `i`, `iⁿ ⇒ i` or `iⁿ ⇒ o` | Fol, with the guard Typing gives the type |
| a bound variable at another type | Fol, unbuilt: no such variable outlives its binder's owner |
| the both dialect's connectives, ⟹-intro and ⟹-elim, a hypothesis, and a theorem or a lemma cited at no type arguments | none: fol-zfc has them |
| a type variable, `OFCLASS` or a theorem cited at type arguments (decision 4); the hidden variable; a citation of a ZF axiom, a theory axiom or a ZF definition at the object level | **no owner yet**: each is its component's design question, and is refused before the first pass |

**Built.** `Lowering.plan` is the four passes in order — expand, logic, reify, fol — and `Lowering.pipeline` adds
Typing's registry, proving after reify. Logic and Reify are unbuilt: a switch over `Pattern` stating their rows, and no
rule. Expand has its rules ("Expand", below). Fol has the rules for binders, instances, variables and guards of
variables at `i`. `Pattern.dialects`
replaces `Node.dialects` and `legalize` reads it. `RulePass` is gone: no rule writes a pattern its pass owns, so one
walk is the whole pass. `forall_elim` takes an isa variable of any type but `o`, as `folPred` does. `lower` counts a
statement only when it reaches fol-zfc.

**Measured** (`isa2fol lower data/zf_export`): of the 9,420, 0 are lowered, and each is refused where it first stops.
No pattern has two owners.

| stops | statements | patterns | the most frequent |
|---|---:|---:|---|
| no owner | 7,178 | 184 | `use(theorem, [i], o)` 6,040, `isaOfClass(i)` 6,039, `use(definition zf, [], o)` 1,544, `isaFree(i)` 1,489 |
| expand | 1,048 | 6 | `isaConst(defined pure, (o => o), args: [o])` 788 |
| logic | 133 | 33 | `ifolAll(o, body: o)` 89 |
| reify | 1,061 | 89 | `isaConst(defined zf, (i => i), args: [i])` 553 |

None reaches Fol. The pipeline takes 17.0 s after a 61.9 s read, most of it spent computing each statement's
patterns.

### The unit and its citations — the framework's other half  **[AGREED AND BUILT 2026-10-14 — points 1–3 and 5, and the four-pass plan; 4 and 6 in their own steps — `Sources/IR/Pass.swift`, `Sources/Reader/Reader.swift`, `Sources/Lowering/Typing.swift`, `Fol.swift`]**

The pass-sets interface says which pass lowers what. This says what the reader hands lowering, and how a statement, a
lemma and a citation meet (I2; prerequisite 2 of the pass plan). Every component after Expand meets through it: Reify
states and proves EX and UNIQ, Typing keeps the registry, Tuple provides the tuple's lemmas. Built first, it leaves no
component to invent its own way to request, cite or refuse a lemma.

Today `lower`'s unit holds the named theorems only, `Statement` is `(name, root, proof)`, `Cited` has the reader's four
kinds, and nothing falls with a statement it cites.

**The plan is `expand · logic · reify · fol`, with Typing's registry proving between reify and fol.** Typing is not a
pass (the division above): Reify states and proves EX and UNIQ, and Fol walks every binder, with the guard Typing gives
its type. The guard pass's rules are Fol's ("Fol — binders, guards and variables", below).

**1. The reader provides what its theorems rest on.**
- **Every theorem they cite at no type arguments, transitively.** `read` proves the 200 cited outside the ZF sessions,
  but `lower`'s unit leaves them out, so such a citation names no statement lowering sees. A theorem cited at type
  arguments is decision 4's.
- **Every definition they reach.** A theorem may use `A ↔ B` without citing `IFOL.iff_def`, and Expand must still
  unfold `↔`. The unit holds the definition of each defined constant that occurs in a theorem or in a definition so
  reached, at each type it occurs at: `Definition(constant, type, definiens)`, an IR value, the `b` of `c ≡ b` read at
  that instance by the reader's one reading (I1).
- **A definition is lowered with the statements up to the pass that owns its constant, and read there.** Expand reads
  a Pure, IFOL or FOL definition as read, to unfold its constant; Reify's prover reads a ZF definition as expand and
  logic left it, to prove EX and UNIQ (point 4). A pattern that a pass before the owner has not built stops the
  definition there, and a lemma whose proof needs it is refused at the registry.
- An axiom a proof cites needs no provision: the citation carries its statement at its types (§4.7). The one Expand
  cites, `Pure.reflexive` at each definition's equation type, comes with the definition ("Expand", point 4).
- Replaces the reference's driver loop, which asked `Expand.instances` and `Reify.constantsToDefine` what to read, then
  expanded, compiled and guarded each ZF definition outside the pipeline.

**2. A citation of a theorem or a lemma names a statement of the unit, and falls with it.** `A` cites `B`, and `B`
stops at reify on a term only its proof holds. `A` holds `B`'s statement but not its proof, so the pipeline lowers
`A`, citing a claim that is never emitted. After the last pass, a statement citing a refused one is refused,
`cites(B)`, transitively (I2). The run stops on a citation naming no statement of the unit, on one whose root is not
its statement's root by ID, and on a cycle of citations.

**3. A lemma is stated and proved by the component that owns its request; Typing's registry routes it.**
- A component cites a lemma by a typed request (I1): `use(.lemma(r), [], root)`. IR holds `r` by an identity and a
  name and never reads it (D3). The pattern is `use(lemma, [], o)`: both dialects, owned by no pass.
- The request's owner states `root` from `r` alone (I2), in the registry's vocabulary: no pattern that a pass before
  the registry owns. So every citer, at any pass, cites one node, and the passes before the registry leave it unchanged.
- After each pass, the pipeline adds every lemma that pass's output cites and the unit lacks, as a statement without a
  proof, in the order the walk meets them (§4.6 R3).
- After reify, the pipeline hands Typing's registry each lemma without a proof. The plan gives the registry one prover
  per component that states lemmas — Reify, Tuple, Typing itself — so Typing never calls one by name. A prover owns its
  requests by ONE exhaustive switch, as a pass owns its patterns, and answers each with a proof concluding its
  statement by ID, in the vocabulary of every other proof before fol and checked at once as a pass's output is; or
  with unbuilt, which refuses the lemma there. A proof may cite more lemmas; they are added and proved in turn, until none is new.
  Fol then lowers each lemma with its citers, as one node (R1).
- The run stops on a request that no prover or two provers own, on a lemma holding a pattern that a pass before the
  registry owns or that no pass owns (its statement is wrong, I3), on a lemma cited after the registry, and on one name
  given to two requests, or to a theorem and a lemma.

  ```
              T                                  L                                    unit holds
  reader      statement + proof                                                       T, what it cites, definitions
  expand      ●  unfolds by its definitions
  logic       ●
  reify       ●  T's proof now cites L ─────────► added: S, as L's owner states it;   T, L
                                                  no proof
  registry                                        ● handed to L's prover: a proof     T, L
                                                    of S, or unbuilt: L refused
  fol         ●  S becomes S′ in T's proof        ●  S becomes S′: one node            T, L
  link        kept, or refused: cites(L)
  ```
- Replaces the reference's `Pass.run → (rewrites, added)`; `Provider: Pass`, where the pass that added a lemma proved
  it in a job of its own; `Statement(citedAs:content:)`; `Run.claimed`'s registry of names; and lemmas named by
  strings (`c + "_EX"`).

**4. EX and UNIQ: one walk over a term, recursive through the registry.** Reify's prover proves `EX c` by walking c's
body as a term, the walk Reify makes wherever Isabelle instantiates at a compound term. At each application it cites
the head's EX, which the registry proves in turn by the same walk over that head's definition, down to the primitives,
whose EX and UNIQ come from base (S3: a body uses only constants defined before it). It walks the term only: a formula
inside, such as a class argument `λx. φ`, stays with its owner. `UNIQ c` is the same walk, citing each head's UNIQ,
the tuple's UNIQ and membership's congruence (base).

```
EX succ, succ ≡ λi. cons(i, i): for every set x, some set r with ⟨⟨x⟩, r⟩ in succ's class
  some set r = cons(x, x)            the walk over cons(x, x), as expand and logic left it:
    the tuple ⟨x, x⟩ exists            Tuple: the tuple's EX at 2
    cons has a value at it             EX cons, cited: the registry hands it to Reify, which walks
                                         Upair(a, a) ∪ A the same way, down to the primitives
  ⟨⟨x⟩, r⟩ in succ's class            succ's class definition (decision 5)
```

**5. The guard of a variable.** A proof before fol may need a guard that fol has not written yet: citing base's
`Pow_EX: forall A. (set(A) -> …)` at its own variable `y` needs `set(y)`. It writes `isaGuard(y, G)`, the guard of `y`,
concluding `G`, the guard Typing gives `y`'s type. The step carries its formula, as `hyp` does, so IR knows no guard.
Fol replaces it by the hypothesis it introduces at `y`'s binder, as it does for an instance at `y`. The guard of a
variable whose binder brings none, or another one, is malformed and throws.

```
the proof before fol                        emitted
fix y                                       fix f0
                                            _0 = assume set(f0)        ← fol, at y's binder
use Pow_EX                                  _1 = use Pow_EX
forall_elim at y                            _2 = forall_elim _1, f0
implies_elim with the guard of y            _3 = implies_elim _2, _0   ← the guard of y
```

**6. A base claim is cited with base's own statement**, parsed from its text (§3's `parse`), never a shape built by
hand (the reference's `Base.claims`); a schema, by instantiation (§4.7's `schema_inst`). Built in the first step that
cites base.

Not in this step: emission, the unit in the order its citations and definitions require; a `@def` as a prover's
answer, which waits on decision 5; and point 4 itself, Reify's own step, which this one gives the registry, the
definitions and the guard of a variable.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | each named theorem of the ZF sessions and each theorem they cite at no type arguments, `(statement, proof)`; each definition they reach, at every type, with what Expand cites it by ("Expand", point 4) | an export of one build |
| the pipeline | each pass's input; each definition, as it stands at its owner's input, to that pass and to the provers; each cited lemma added once; the registry asked after reify; every citation linked, every refusal carried to its citers | each pass's `owns`; one registry |
| a citer | `use(.lemma(r), [], root)`, `root` the owner's statement of `r` | the registry proves `r`, or refuses it there |
| Typing's registry | each lemma handed to the one prover that owns its request | the plan's provers |
| a prover | for each request it owns, by one switch: its statement, from the request alone, and a proof of it, or unbuilt | the definitions at their owners' input; the statements of the lemmas it cites |
| Fol | each binder with the guard Typing gives its type; each instance and each guard of a variable discharged by that variable's guard; each variable fol-zfc's | Typing's guards |

**Tests, written first.** `PipelineTests`, on fake passes and a fake registry: a statement citing a refused one is
refused, transitively; a lemma two statements cite is added once, unchanged until the registry, and lowered with both
as one node; the registry hands each lemma to the prover that owns it, and the lemmas its proof cites in turn; a lemma
its prover has not built is refused there, and its citers fall; a pass reads the definitions of the constants it owns
as they stand at its input; the run stops on a citation of no statement, two statements for one lemma, a cycle of
citations, a lemma cited after the registry, a lemma holding a pattern that a pass before the registry owns, and a
lemma named as a theorem. `TableTests`: the guard of a variable concludes its formula. `ReaderTests` (`UnitTests`): the
unit holds each theorem its theorems cite at no type arguments, and the definition of each constant they reach, at
each type, `c ≡ λx. b` and `primrec`'s applied `c(x) ≡ b` alike. `LoweringTests`: the guard's tests, run on Fol, and
the guard of a variable (`FolTests`); Typing's registry hands a lemma to the one prover owning its request, and a
request no prover or two own stops the run (`TypingTests`); the plan is the four passes, the registry proving after
reify with no prover yet (`PlanTests`).

**Built.**
- IR: `Statement` is a theorem or a lemma (`lemma: Lemma?`, `proof: NodeID?`); `Cited.lemma(Lemma)`, `Lemma` holding a
  `Request` by its identity and name; `Definition(constant, type, definiens)`; `Unit.definitions`; `Pass.run(roots,
  definitions, in:)`; `Registry`, answering `Proved.proof` or `.unbuilt`; `Pipeline(passes:, registry:, provingAfter:)`;
  `isaGuard(x, G)`; `PipelineRefusal` `lemmaUnbuilt`, `cites`, `unread`.
- Reader: `Reader.unit()`. ⚠ **A DEFINITION IS WRITTEN IN TWO FORMS**: `c ≡ λx. b`, and the applied `c(x) ≡ b` that
  `primrec` writes, its arguments the axiom's frees in their order (`ZF.iterates.iterates_nat_def`). Both read as the
  definiens `λx. b`; a third form stops the read, `MalformedExport.notADefinition`.
- Lowering: `Typing` is the registry, routing to `Prover`s; `Lowering.pipeline` has none yet. Fol has the guard's rules,
  makes a variable at `i` fol-zfc's (`folBound(k)`), and resolves the guard of a variable.

**Measured** (`isa2fol lower data/zf_export`): the unit holds the 9,420 named theorems, 133 they cite outside the ZF
sessions at no type arguments, and 1,004 definitions they reach; 892 of these reach the pass that owns their constant.
The refusals are unchanged: no owner 7,178, expand 1,048, logic 133, reify 1,061; none reaches Fol, and no lemma is
cited. Read 61.9 s, lowered 17.0 s.

**Then Expand**, against point 1: the next section.

### Expand — the logic's defined constants, unfolded  **[AGREED AND BUILT 2026-10-14 — `Sources/Lowering/Expand.swift`]**

**Expand replaces each defined constant of Pure, IFOL and FOL, and each ZF one at the meta level (6), by its
definition, and each citation of such a definition by `Pure.reflexive`.** It is the Logic component's first pass
("Lowering's components"): after it nothing of the logic is left but its leaves and binders, and Logic's rules meet no
defined constant. Before it was built, 1,048 named theorems stopped there (`isa2fol lower data/zf_export`).

**1. Expand owns two patterns**, by ONE switch over `Pattern` that also dispatches its rules:

| pattern | answer |
|---|---|
| `isaConst(defined pure · ifol · fol at either level, or zf at meta, T, args)`, no type variable in `T` | a rule: unfold (2) |
| `use(isaDefinition(the same), types, o)`, no type variable in `types` | a rule: `Pure.reflexive` (3) |
| every other pattern | not its own |

At a type variable both have no owner: decision 4's, refused before the plan. The constants are those `theory/constdefs`
lists for Pure, IFOL and FOL (§4.3b): Pure's `PROP &&& TERM`, IFOL's `↔ ¬ True ∃! Uniq Let`, FOL's `induct_*`; and the
five ZF ones at the meta level (6).
`IFOL.term_class_def` defines `OFCLASS`, which the reader reads as `isaOfClass`, never as a constant: a citation of it
holds `isaOfClass`, which no pass owns, so it never reaches Expand.

**2. A constant unfolds by its definition at its own type.** `c(a⃗)` at `T` becomes `c`'s definiens at `T`, `λx⃗. b`,
applied to the rewritten `a⃗` and β-reduced: `b[a⃗/x⃗]`. An argument at a function type is a `λ`, and reduces into the
body as `instantiate` reduces an applied variable whose head becomes a `λ` (§4.4).

```
Isabelle          read as                  after Expand
¬A                Not(A)                   A ⟶ ⊥
∃!x. x ∈ A        Ex1(λx. x ∈ A)           ∃x. x ∈ A ∧ (∀y. y ∈ A ⟶ y = x)
True              True                     ⊥ ⟶ ⊥
PROP A            prop(A)                  A
A &&& B           conjunction(A, B)        ⋀C. (A ⟹ B ⟹ C) ⟹ C
```

- **Every formula unfolds, a citation's statement included.** A cited theorem's statement and the theorem's own stay
  one node. An axiom's statement arrives unfolded: of the logic's, `iff_reflection`'s `↔` and `classical`'s `¬`, the
  only two; of ZF's, the `↔` of `extension`, `Pow_iff`, `Union_iff` and `replacement`, and `foundation`'s `¬`. A step's
  conclusion is computed from its unfolded premises, so each proof still concludes its statement, by ID.
- **The definitions are unfolded among themselves first**, walk after walk until a walk changes nothing: a definiens
  may use an earlier constant (S3), and a rule never writes a pattern its pass owns.
- **The rule needs no context**: a node unfolds alike under any binders, so the walk rewrites each node once.

**3. A citation of a definition becomes `Pure.reflexive`.** IFOL and FOL state a definition `c ≡ λx⃗. b`: unfolded it
says `λx⃗. b ≡ λx⃗. b`, `Pure.reflexive` at `c`'s type, instantiated at the definiens. Pure states its own applied,
`prop(A) ≡ A`, closed over its parameters (§4.4): unfolded it says `⋀x⃗. b ≡ b`, `Pure.reflexive` at `b`'s type under a
`⋀`-intro at each parameter.

```
read as                                after Expand
use IFOL.not_def_raw                   isaAllElim(use Pure.reflexive [o ⇒ o], λP. P ⟶ ⊥)
  ⊢ Not ≡ λP. P ⟶ ⊥                      ⊢ (λP. P ⟶ ⊥) ≡ (λP. P ⟶ ⊥)
use Pure.prop_def                      isaAllIntro(o, isaAllElim(use Pure.reflexive [o], A))
  ⊢ ⋀A. prop(A) ≡ A                      ⊢ ⋀A. A ≡ A
```

The proof is built from the definition, never by reading the citation's statement back (I1); the pipeline checks that
it concludes the unfolded statement, by ID. `Pure.reflexive`'s statement comes from the reader, as the export states
it, never a shape built by hand, as point 6 of "The unit and its citations" rules for base's claims.

**4. The reader adds three things to a definition.** A citation names a definition by its axiom's type arguments, not by
its constant's type; Pure's applied form must be told from `c ≡ λx⃗. b`; and `Pure.reflexive` is needed at a type no
proof may cite it at.

```swift
public struct Definition {
    public let constant: Defined
    public let type: IRType            // c's type at this instance
    public let axiomTypes: [IRType]    // new: the axiom's type arguments here, as a citation of it carries them
    public let parameters: Int         // new: n for c(x1 … xn) ≡ b, 0 for c ≡ λx⃗. b
    public var definiens: NodeID       // λx⃗. b
    public let reflexive: NodeID       // new: Pure.reflexive read at the type of the axiom's equation, b's
}
```

`definition(of:at:)` already computes the first two; the third is one more statement read. Expand finds a constant's
definition by `(constant, type)` and a citation's by `(constant, axiomTypes)`. An axiom a proof cites needs no
provision; the one Expand cites comes with each definition (point 1 of "The unit and its citations").

**5. IR exports β.** `instantiate`'s reduction of an applied `λ` becomes `beta(f, args)`, public: `instantiate` calls it
and Expand unfolds by it, one home (D3, rule 4).

**6. A ZF definition at the meta level is Expand's too.**  **[AGREED AND BUILT 2026-10-14]**

Five ZF constants are declared at Pure's level: their declared type mentions `prop` or a type variable.

| constant | declared type |
|---|---|
| `ZF_Base.split`, `QPair.qsplit` | `(i ⇒ i ⇒ 'a) ⇒ i ⇒ 'a` |
| `MetaExists.ex` | `('a ⇒ prop) ⇒ prop` |
| `L_axioms.L_Reflects` | `(i ⇒ o) ⇒ (i ⇒ i ⇒ o) ⇒ prop` |
| `AC_Equiv.AC18` | `prop` |

None can be named. `split` is one constant at several types, which one name cannot denote; `AC18` as a class would
quantify over classes. So each has one translation, unfolding, and Expand has its two rules: the definition at the
use's type, and a citation of it as `Pure.reflexive` (D1). Today they read as `defined zf`, so Reify owns them at a
concrete type, and Reify only names; owning them, it would hold a second copy of Expand's rule (rule 4). At a type
variable they have no owner, decision 4's, like every constant of the logic.

**The reading loses what tells them apart.** `prop` reads as `o`, and a use instantiates `'a`:

```
AC18 :: prop                                     isaConst(defined zf, o, [])            AC1 :: o reads the same
MetaExists.ex :: ('a ⇒ prop) ⇒ prop, at i        isaConst(defined zf, (i ⇒ o) ⇒ o, …)   as an object-level constant
```

So a defined constant keeps its declared level, a typed value the reader builds from the declared type (I1, rule 3):

```swift
enum Level { case object, meta }              // meta: the declared type mentions `prop` or a type variable
struct Defined { let family: Family; let name: String; let level: Level }   // was (family, name)
// Pattern: ConstantKind.defined(Family, Level), CitedKind.isaDefinition(Family, Level)
```

The level is no family. A family is the theory layer a constant comes from (§4.3b); the level is a fact of its
declaration, which the reader states and lowering decides by. The logic's constants carry theirs too (`¬` at
`object`, `∃!` at `meta`) and unfold whatever it is.

**The border is one function**, `unfolds(family, level)` in `Plan.swift`, which Expand's switch and Reify's both read:

| a defined constant, or a citation of its definition | owner |
|---|---|
| Pure, IFOL, FOL, at either level | Expand |
| ZF, at `meta` | Expand, by its two rules unchanged |
| ZF, at `object` | Reify; a citation of its definition has no owner yet (decision 5) |

Every defined constant's pattern now shows its level, so `docs/SOURCE_SURFACE.md` is regenerated. Unfolding `ex` puts
a `⋀Q::o` inside a premise: Logic's `ifolAll(o, …)`, as `&&&` unfolded already gives.

**FOUNDATION first.** FOUNDATION carries the border: §2's "A constant is named only at the object level", R5's note
that unfolding a meta-level constant is not the inlining R5 forbids, and R6's "`split` is no longer one of the two",
all three the reference's own text. Two adaptations: `AC18`'s class is argued without the reference's class of the
empty tuple, which this branch's S4 lacks, and Pure's constants unfold by family with IFOL's and FOL's.

**Tests, written first.** `ConstantsTests`: a defined constant declared over `i`, `o` and `⇒` reads at `object`
(`ZF_Base.Ball`, `IFOL.Not`); one declared with `prop` or a type variable at `meta` (`ZF_Base.split`, `Pure.prop`).
`PlanTests`: `defined(zf, meta)` and a citation of its definition are Expand's, `defined(zf, object)` Reify's, and no
pattern has two owners. `ExpandTests`: `split(λx y. x ∈ y, A)` at `'a := o` unfolds by `split`'s definition, and a
citation of that definition at `[o]` becomes `Pure.reflexive`.

**Built.** `Level` and `Defined.level` in IR, the reader's `IsaType.level`; `ConstantKind.defined(Family, Level)` and
`CitedKind.isaDefinition(Family, Level)`; `unfolds(_:_:)` in `Plan.swift`, read by Expand and Reify.

**Measured** (`isa2fol lower data/zf_export`): Reify owns no `defined zf meta` pattern, so none stops there. Refused at
no owner 7,176, logic 1,078, reify 1,115, and 51 still fall citing `IFOL.TrueI`: 62 statements move from reify to
logic, and 2 that only a meta-level definition's citation held leave no owner. 1,000 of the 1,004 definitions reach
their owner. The surface holds 2,597 patterns, against 2,592: a level splits five (`isa2fol surface data/zf_export`).
Read 65.8 s, lowered 20.6 s.

**Kept from the reference, and changed.** Kept: unfolding at the use's type, applied and β-reduced; the definitions
unfolded among themselves to a fixpoint; a citation as `Pure.reflexive` at its type, whose statement the reader reads
(the reference's driver called `reader.axiom(reflexive, at: [T])`). Changed:
- Pure's `PROP &&& TERM` unfold like IFOL's; the reference left `Pure.prop` pending (D1).
- The citation's proof comes from the definition; the reference read the citation's statement back (`sides`,
  `notReflexive`), against I1.
- Pure's applied form is reflexivity under its parameters; the reference, with Pure pending, never met it.
- The definitions and `Pure.reflexive` come with the unit; the reference's driver asked `Expand.instances` and kept a
  `reflexive[T]` of its own.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | each definition at each type, with `axiomTypes`, `parameters` and `reflexive` | an export of one build |
| the pipeline | each Pure, IFOL and FOL definition the unit holds at a type with no type variable, handed to Expand as read | each pass's `owns` |
| Expand | every statement, proof and definition it walks free of its two patterns, each proof still concluding its statement by ID; every axiom's statement unfolded; a definition's citation as `Pure.reflexive` at its equation's type | the definition of each constant it owns at each type it meets it |

A constant or a citation Expand owns with no definition handed stops the run (`ExpandError.noDefinition`): the reader or
the pipeline broke its row. That is no refusal; a built rule never refuses. Logic's step assumes Expand's row.

**Tests, written first.**
- `ExpandTests`, Expand run alone, each proof checked to conclude its statement by ID: `¬A` unfolds in a statement and
  its proof; `∃!x. x ∈ A` unfolds, its `λ` reduced into the body; `True`, of no arguments; a definition using another,
  through both; a citation of `not_def_raw` becomes `Pure.reflexive` at `o ⇒ o`, instantiated at the definiens; one of
  the applied `prop_def`, a `⋀`-intro over `Pure.reflexive` at `o`; a cited theorem's statement and the theorem's own
  stay one node, and `iff_reflection`'s statement unfolds; a constant with no definition stops the run.
- `PlanTests`: Expand answers `.rule` for its two rows; a ZF definition holding `¬` reaches Reify unfolded.
- `UnitTests`: a definition carries its axiom's type arguments, its parameters and `Pure.reflexive` at its equation's
  type: `IFOL.Not` (0 parameters, at `o ⇒ o`), `Sum.Inl` (applied, 1, at `i`), `split` at `o` (`axiomTypes` `[o]`).
- `IndexTests`: `beta` applies a `λ` argument by argument.

**Built.**
- IR: `beta(f, args)`, which `instantiate` calls; `IRType.domains`, one home for the reader's and the pipeline's
  copies; `Definition` carries `axiomTypes`, `parameters` and `reflexive`.
- Reader: `definition(of:at:)` fills them, reading `Pure.reflexive` at the equation's type.
- Lowering: `Expand` owns its two rows with a rule each, unfolds the definitions it is handed to a fixpoint, and walks
  with no context. A missing definition throws `ExpandError.noDefinition(node)`.
- ⚠ **`reflexive` IS NEVER LOWERED**: the pipeline lowers a definition's `definiens` alone. Only Expand, the first
  pass, reads `reflexive`, so it reads it as the reader wrote it.
- `lower` names, for a statement that falls with one it cites, the statement it cites.

**Measured** (`isa2fol lower data/zf_export`): none stops at expand. Of the 1,048 that did, the refusals move on: no
owner 7,178, logic 1,014, reify 1,177. 51 named theorems pass every pass, the first to, and fall because each cites
`IFOL.TrueI`, which stops at logic (a scratch print, not kept: `lower` reports only the named theorems' refusals). 999
of the 1,004 definitions reach the pass that owns their constant, against 892: a ZF definition holding a logic constant
now passes Expand. Read 61.1 s, lowered 19.2 s.

### Fol — binders, guards and variables  **[BUILT 2026-09-28 as the guard; Fol's 2026-10-14 — `Sources/Lowering/Fol.swift`]**

**The quantified variables of type `i` get a guard, the binder becomes fol-zfc's, and so does the variable.** The
guard was Typing's pass until 2026-10-14; Typing keeps no pass ("The unit and its citations"), so Fol writes each
binder with the guard Typing gives its type (`Typing.guarded`). A variable keeps `isaBound(k, T)`, its type, until
Fol: that type is how Fol tells a set binder from a class binder.

⚠ **A VARIABLE BECOMES `folBound` ONLY AT `i`, AND ONLY IN FOL, THE LAST PASS.** A `folBound` is typed `i`, so a class
variable relabelled while a pass still reads types would look like a set, open to `set(P)`; the guard relabelled before
reify until 2026-09-29. So Fol relabels a variable at `i` in the walk that guards its binder, and a variable at a class
type stays isa with its binder, both unbuilt. An instance's discharge reads the binder's entry in the context, never
the instance's rewritten child.

⚠ **`set(t)` CANNOT BE WRITTEN FOR A COMPOUND `t`** — `folPred` takes only variables, S1 as a
check. So a compound instantiation is not discharged by a closure lemma over terms
(`set(C) → set(Pow(C))`); the term must first become a variable, FOUNDATION §2's S1 route, whose
EX delivers `set(r)` with it.

| before | after |
|---|---|
| `ifolAll(i, φ)` | `folForall(folImplies(set(0), φ′))` |
| `ifolEx(i, φ)` | `folExists(folAnd(set(0), φ′))` |
| `isaAllIntro(i, body)` | `folForallIntro(folImpliesIntro(set(0), body′))` — the guard is a hypothesis the fixed variable brings |
| `isaAllElim(p, x)`, `x` a bound variable | `folImpliesElim(folForallElim(p′, x′), hyp(j, set(x′)))` — discharged by `x`'s own guard |
| `isaGuard(x, G)`, the guard of a variable | `hyp(j, G′)`, the same discharge; `G` not `x`'s guard (`notItsGuard`), or `x`'s binder bringing none (`unguardedBinder`), is malformed |
| `isaBound(k, i)` | `folBound(k)` |
| `isaAllElim(p, t)`, `t` a compound term | never reaches Fol: `t` is Reify's, an earlier pass; an instance at anything but a bound variable throws `instanceNotAVariable` |
| `hyp(k, A)` | `hyp(k + g, A′)` — `g` the guards inserted between it and its binder |
| a quantifier, `⋀`-intro or `⋀`-elim, a variable or the guard of a variable at `iⁿ ⇒ i` or `iⁿ ⇒ o` | Fol's, unbuilt: Typing has no guard for the type yet |
| … at `o`, at a function of propositions, at a type variable; a `λ` | not Fol's: Logic's, no owner's (decision 4), Reify's |

The walk rewrites every `use`'s root too, so a cited statement and the theorem's own lowered
statement are one node.

**Its context is a stack of binder entries**, nearest last:

```swift
enum Entry: Hashable { case fix(guarded: Bool), assume }
```

`enter` pushes one `.fix` per term the binder binds — `guarded` exactly when Fol's switch over `Pattern` gives the
binder a rule: `isaAllIntro`, `ifolAll` or `ifolEx` at `i` — and one `.assume` per hypothesis. `narrow` keeps the top
of the stack down to the deepest binder the node reaches (`looseBound`, `looseHyps`); a closed node keeps nothing.
Reading it, "above" meaning nearer the top:

- **the guard of `x`, bound `k`**: its entry is the `(k+1)`-th `.fix` from the top, and `j` = the `.assume`s above it +
  the guarded `.fix`es above it. An unguarded entry there — a binder bringing no guard — is MALFORMED and throws; it is
  not a refusal.
- **`hyp(k, A)`**: its binder is the `(k+1)`-th `.assume` from the top, and `g` = the guarded
  `.fix`es above it.

```
fix x, assume P(x), lem at x              stack [x✓, h]      above x: 1 assume     → hyp(1, set(x))
assume C, fix x, assume P(x), hyp(1, C)   stack [c, x✓, h]   above c: 1 guard      → hyp(2, C)
```

**One walk.** Fol writes fol-zfc's binders and variables, never a pattern it owns, so nothing is left for a second.

**Where it lives:** a module `Lowering`, depending on `IR` — the framework never sees a pass.

**Tests** (`FolTests`): Fol is run alone, each proof checked to conclude its statement BY ID. The pipeline over the plan
stops every fixture that has `P(x)` at Reify, and lowers `⋀x. ⊥ ⟹ ⊥` whole (`PlanTests`).

1. `∀`/`∃` at `i` is guarded and its variable becomes fol-zfc's; at `o`, `i ⇒ o` and a type variable it is unchanged.
2. fix x, assume P(x), lem at x: the lowered proof concludes the lowered statement by ID; the discharge is `hyp(1, set(x))`.
3. assume C, fix x, assume P(x), `hyp(1, C)`: it becomes `hyp(2, C)`, and the proof concludes.
4. an elimination at `Pow(a)` stops at Reify, the term's owner (`PlanTests`).
5. a cited statement and the cited theorem's own lowered statement are one node.
6. `⋀x y`: an elimination at `x` skips `y`'s guard — `hyp(2, set(x))`.
7. `C ⟹ ⋀P::o. P ⟹ C`: a binder at `o` inserts nothing and renumbers nothing.
8. the guard of `x` is the assumption Fol writes at `x`'s binder; under `forall_intro`, or not `set(x)`, it throws.

### A refusal inside the walk  **[BUILT 2026-09-28; DELETED 2026-10-13 with the pass-sets interface]**

A built rule never refuses ("Lowering's components", point 4), so `transform` catches nothing: `Refusal` and
`Rewrite` are gone. Only the pipeline refuses a statement, before a pass, naming its patterns. `Reader` exposes a
theorem's claim name (`name(4)` → `name.4`, CLAUDE.md rule 5) for the unit's statements.

### The meta level, lowered — the pass plan  **[DECIDED 2026-09-29 — decision 4 deferred; nothing built]**

**Every meta-level object is a set or a class** (FOUNDATION §1a). `base/` proves what replaces Pure's
λ-calculus: tuples (`tuples`), class existence over them (`classes`), class functions with β, η,
extensionality and combination (`metafun`). **Every function is a class** — a constant, a λ and a function
variable alike — applied by membership.

Notation: `t` is the tuple of the arguments, a 1-tuple at arity 1 (decision 1), and `fn_apply(F, t, r)` is
`⟨t, r⟩ ∈ F`, base's `pmem(t, r, F)`. **β** is Isabelle's free reduction of `(λx. b)(a)` to `b[a/x]`; here
the λ is a class `C`, and unfolding `a`'s membership in `C` to the body by `C`'s defining property is a
proof step — "β as proof".

**Passes, in order.**

| # | pass | removes |
|---|---|---|
| 1 | **logic** — IFOL's ND rules and `FOL.classical` to the kernel's own steps; an inlined box instantiated at once, reduced at the proof level (`instantiate`) | every `⋀P::o`; those rules' and boxes' class instantiations |
| 2 | **reify** — every compound term becomes a variable with its defining atom; every function becomes a class | `isaConst` at `i` or a function type, `isaVarApp`, `isaAbs`, `Pure.eq` at a function type, `isaAllElim` at a function type |
| 3 | **fol** — `set(x)` on every set binder, Isabelle's and reify's, a class binder bare, each written as fol-zfc's binder; every variable to `folBound`; then `legalize`. Until 2026-10-14 the guard was a pass of its own, before fol | the isa binders at `i`, `iⁿ ⇒ i`, `iⁿ ⇒ o`, and the rest of the isa dialect |

- **logic before reify**: an IFOL rule at a λ becomes the kernel's step and no class is built. `spec` at
  `λx. x∈A ⟶ x∈B`, then at `c`, is `isaAllElim` at `c`: `∀` and `⋀` are one node.
- **reify before fol**: reify's variables are set binders too, and R3 guards "the ones S1 invents".
- **the guard in fol, the last pass** (2026-10-14): fol reads the binder's IR type — `i` guarded, a class bare — and
  writes `folForall`, which carries none; each variable keeps its type until fol relabels it, in the same walk.

⚠ **`subst` IS NOT AN ND RULE.** Logic does not remove its class instantiations: at the λ's class it is
membership's congruence (`g3_pmem_cong1`), then β as proof — reify's.

**Prerequisites, in the framework — both built:**

1. **A fol node accepts a variable whose IR type matches** — **BUILT 2026-09-29.** `folPred` takes any
   variable, `folBound` or `isaBound` at a type other than `o` (a proposition is never a term, S4:
   `propositionAsTerm`); `exists_intro` at `isaBound(k, T)` concludes `ifolEx(T, …)`, and `exists_elim`
   opens `ifolEx` as well as `folExists`. Variables keep `isaBound(k, T)` until fol, and `legalize`
   enforces fol-only at the end. ⚠ **NO RELABEL PASS**: relabelling early makes a class variable a
   `folBound`, typed `i` — indistinguishable from a set, and open to `set(·)`. Fol relabels, last. Its rules for
   `∃`-intro and `∃`-elim at `i` — the witness's guard into the `∧`, the hypothesis becoming `set ∧ φ` — come with
   logic, their first producer. `forall_elim` takes an isa variable too (2026-10-13). Open for that step:
   `exists_intro` at `isaBound(k, i)` concludes `ifolEx(i, …)`, and Fol writes `folExists`.
2. **A pass may add statements** — **BUILT 2026-10-14 otherwise** ("The unit and its citations"): a pass never adds a
   statement; the pipeline adds each lemma a pass's output cites, and the prover that owns its request proves it.

**What each construct becomes.**

| isa | becomes |
|---|---|
| a bound variable at `i` | a set variable, guarded (R3) |
| … at `i^n ⇒ i` | a class variable `F`, bare, owing `mfun(F, D)` (S5) |
| … at `i^n ⇒ o` | a class variable `P`, bare (S4) |
| … at `o` | classified out: `⋀P::o` is the kernel's own rules (S4) |
| a constant — a function or a predicate | a class, cited globally (decision 5) |
| `c(x⃗) : i`, `f(x⃗) : i` | `∃r. fn_apply(F, t, r) ∧ φ(r)`, at the atom where it appears (decision 3) |
| `P(x⃗) : o`, a predicate constant or variable | `t ∈ P` |
| `ZF_Base.mem`; `IFOL.eq`, and Pure `≡` at `i`, which the reader reads as it | `elem`; `eq` — the target's own, not classes |
| Pure `≡` at `o` | `↔` — the reader reads it so |
| `f ≡ g` at a function type | `∀t r. fn_apply(F,t,r) ↔ fn_apply(G,t,r)` (FOUNDATION §3b) |
| `λx⃗. b : i^n ⇒ i` / `λx⃗. φ : i^n ⇒ o` | a class `C`: `∀t r. fn_apply(C,t,r) ↔ ⟦r = b(t)⟧` (`lam_class`) / `∀t. t ∈ C ↔ ⟦φ(t)⟧` (`lam_pred`) — LOCAL, never a global claim |
| a class argument, `c(A, λx. φ)` | outside the tuple, a parameter of `c`'s defining property (R4) |
| `If(φ, a, b)`, an `o` argument | read where it appears: `(φ ∧ r = a) ∨ (¬φ ∧ r = b)` (FOUNDATION R6's note) |
| `c ≡ λx⃗. b`, a definition | `c`'s defining property |
| `OFCLASS(T, c)` | not a formula: checked, then dropped (decision 4) |

**Where Isabelle's computation becomes proof.**

| Isabelle step | becomes |
|---|---|
| `⋀`-elim at a variable | `forall_elim`, and the guard's discharge |
| `⋀`-elim at a compound `i`-term | `forall_elim` at the term's variable, opened where the term appears; EX and UNIQ where two forms meet |
| `⋀`-elim at a λ | `forall_elim` at the λ's class, then β as proof |
| Pure `combination` at a function type | `mfun_comb` — membership respects `eq` — then β as proof at both ends |
| Pure `abstract_rule` | `∀`-intro, and a lemma relating `f ≡ g` to `⋀x. f x ≡ g x` under `mfun` — not in `metafun` yet |
| Pure `reflexive`, `symmetric`, `transitive` at a function type | `↔` reasoning under `∀t r` |
| an inlined box instantiated at once | reduced at the proof level: the box read at its instance, no class |
| IFOL's thirteen ND rules, `FOL.classical` | the kernel's rules: `spec` is `forall_elim`, `exE` is `exists_elim`, … |

**Decisions (2026-09-29).**

1. **Arity 1 is a 1-tuple**, as R7 reads every arity. The value itself would save a tuple per unary
   application — a later size optimisation.
2. **Order: logic → reify → guard → fol**, on prerequisite 1; the guard is fol's since 2026-10-14.
3. **A compound term's variable is bound where the term appears, never wider**, written with S1's `∃`:
   `P(f(x))` is `∃r. fn_apply(F, t, r) ∧ P(r)` in place. Isabelle's local variables stay local: a λ or a
   compound term is never lifted into a global claim, which would close it over its locals and need a fresh
   name (rule 5). Where two forms of one term meet — β as proof's and a statement's, a hypothesis's and a
   conclusion's — EX and UNIQ convert, and every function has both.
4. **Deferred** until it blocks. `OFCLASS` is Isabelle's type check, made a premise by the exporter —
   metadata: lowering checks it (`term`'s only type is `i`; `arity_term_i` is the export's only class
   instance) and drops the premise, its discharge and the proof behind it; the reader keeps it as the
   export writes it. A `term`-restricted type variable is read at `i`, exactly. An UNRESTRICTED one is
   open, and reify's first cut refuses a node whose type is a variable, by name. Outside Pure's equality
   rules, which lower per type anyway, only `ZF_Base.split_def`, `pair.split`, `QPair.qsplit_def`,
   `FOL.meta_simps(1)` and `MetaExists.meta_exI`/`meta_exE` are cited at a type other than `i` (a scratch
   probe, not kept). Candidates when it blocks: unfold a notation-only definition (`split`) where it is
   used, and put a generic proof in place at the type of its use — no new name; `MetaExists`, defined over
   all propositions, separately.
5. **A constant is a class, cited globally by Isabelle's name.** The checker's one global naming form is
   `@def`, so what is named is the constant's defining property, and a claim using the constant binds its
   class with that property as a hypothesis. Of the relation form's four per-constant lemmas (FOUNDATION §2
   S2, R5), two go and two merge:

   | relation form | class form |
   |---|---|
   | GRAPH | the constant is its class |
   | CONG | membership respects `=` for every class — `g1_pmem_cong`, proved once |
   | EX, UNIQ | `mfun(C, D)` |
   | — | the class exists: class existence from the definition's body, the classes of the constants it uses as parameters (R5) |

   **The translator builds this definition/lemma graph** — during reify, as helpers, in definitional order
   (S3) — not as a phase before or after the passes. Not built: the per-formula class existence proof
   (FOUNDATION §3, "per-formula generation stays"). `base/` states the five primitives as relations
   (`primitives`, `skolem`: `Pow(A, r)`); their classes are built from those.

### Pass-level questions — for the passes, not the framework

| | |
|---|---|
| S1 placement | where the term appears, never wider (the pass plan, decision 3) |
| meta functions | every function — a constant, a λ such as `RepFun(A, λx. f(x))`'s, a function variable — is a CLASS, its graph (decision 5) |

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
