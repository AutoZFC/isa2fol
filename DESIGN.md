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
  Lowering/      the plan (§4a): the passes Expand · Logic · Fol, Reify's code in Logic's walk, and the registry
  isa2fol/       CLI
Tests/
  YXMLTests/  FolDialectTests/  IRTests/  ReaderTests/  LoweringTests/
```

```
  YXML  ─►  Reader  ─►  IR  ─►  Lowering  ─►  FolDialect
```

**The reader, the unit's citations and lemmas, Expand, Logic's first step and Fol's binders and variables at `i` are
built**; the rest of Logic, Reify, the provers (§4a) and the emission of a unit are not.

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

## 3. FolDialect — the text boundary over the table  **[render BUILT, a schema instance since "EX and UNIQ — their prover"; parse BUILT for base's statements]**

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
| `render` | the table → text: one line per declaration, bound variables named by level `b0, b1, …`; a base schema instantiated at every letter is one `schema_inst` step, its letters named as base's schema line declares them (`schemaLetters`); refuses an isa node, a partial schema instance, an unclosed root, a malformed name |
| `parse` | base's text → table nodes in lowering's vocabulary: a schema's letters are `⋀::o`, and a guarded quantifier, `forall x. (set(x) -> φ)` or `exists x. (set(x) & φ)`, is a set binder `∀ᵢ`, `∃ᵢ`, which Fol writes back as the text ("EX and UNIQ — their prover", 4) |

⚠ **THE ROUND TRIP IS AN ID COMPARISON:** `intern(parse(render(root))) == root`, and for a guarded quantifier, which
parses as a set binder, `Fol(parse(text))` is the text's own fol-zfc reading (`aParsedBaseClaimLoweredByFolIsItsText`).
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

**A schema's letter is Isabelle's own `⋀P::o`** (§4a, "Logic"): the binder, its ⋀-intro and its variable at `o` are
both dialects, and `schema_inst` is `folSchemaInst`. `render` refuses both, `RenderError.schema`, until emission
writes schemas.

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
| Pure equality: `reflexive symmetric transitive combination abstract_rule equal_intr equal_elim` | 7 | steps: `isaReflexive`, `isaSymmetric`, `isaTransitive`, `isaCombination`, `isaAbstract`, and fol-zfc's `iff_intro`, `iff_elim_l` (§4a, "Logic's second step") | `↔`/`=` reasoning and congruence — S2's CONG; `abstract_rule` under a binder. The simplifier's rewriting: 81–94% of theorems reach these |
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
| **3b. A citation carries its types** | `use(cited, types, root)` — `types` the citation's type arguments, possibly the citer's own variables; `root` the cited statement READ AT `types`, which is what Isabelle's citation concludes. At the cited theorem's own variables `root` IS its statement, the same node. An unnamed box is inlined as now, read at its citation's types — but one binding a proposition, a statement cited by its name ("Boxes binding a proposition, read as schemas") |

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
| `⋀`-intro · `⋀`-elim | `ZAbst` · `ZAppt` | `isaAllIntro` · `isaAllElim`; at `o` below a statement's top, Pure's `⋀` over a proposition, `isaPropIntro` ("Functions of propositions and the bound `⋀P`", 6) |
| `⟹`-intro · `⟹`-elim | `ZAbsp` · `ZAppp` | `folImpliesIntro` · `folImpliesElim` |
| a hypothesis | `ZBoundp` (a free `ZHyp`: 0 in the export) | `hyp` |
| a citation | `ZConstp` — an axiom or a NAMED theorem, with its type arguments; `root` is its closed statement read at them | `use(Cited, types, root)` |
| an unnamed box | `ZConstp` of a theorem with no name — logically not a building block | INLINED: its closed proof, read at its citation's types; one binding a proposition on its spine a statement, `use(.theorem("<theory>.BOX_<fingerprint>"), …)` ("Boxes binding a proposition, read as schemas") |
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

A `ZClassp` — 0 in the export — stays refused by name. Lowering states `OFCLASS` by its class's
definition, `⋀P::prop. P ⟹ P` (FOUNDATION S4; "OFCLASS — a class's membership by its definition"):
trivially true at `i`, the only type in `term`, never dropped — `arity_term_i` proves it.

### 4.3b The input layer: axioms and constants  **[DECIDED 2026-10-13 (user); BUILT 2026-10-13]**

**Pure, IFOL, FOL and ZF each contribute two mechanisms: AXIOMS, and CONSTANTS.** A constant is either a LEAF, which
only axioms constrain, or DEFINED, `c ≡ b`, built over leaves and earlier definitions for reuse. A theorem or a proof is
a composition of these, put together with §4.3a 4's formers: variables, `λ`, ⋀/⟹ intro and elim, hypotheses, and
citations. The input layer is the isa dialect, its patterns, its primitives (three names for one thing). It represents
these two mechanisms and those formers, and nothing else. If every pattern is translated, every theorem is (D1). Pure's
equality is the one exception: its seven rules are Pure's inference steps, and the reader reads them as steps, never as
cited axioms (§4a, "Logic's second step").

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
| a leaf FOL covers: `Trueprop` · `Pure.imp`, `IFOL.imp` · `conj` · `disj` · `False` · `Pure.all`, `IFOL.All` · `IFOL.Ex` · `Pure.eq` at `o` | erased · `folImplies` · `folAnd` · `folOr` · `folBottom` · `ifolAll(T)`, and `Pure.all` at `o` below a statement's top `isaPropAll` · `ifolEx(T)` · `folIff` |
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
| `instantiate(body, t)` — a binder was removed | `k = d` → `t` shifted by `d`, its type the variable's, unless either is a fol-zfc variable, which is untyped; `k > d` → `k − 1` | — | `forall_elim`, `exists_elim`, β-reduction: `beta(f, args)`, one `instantiate` per argument |
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
    func after(_ n: Node, was id: NodeID, context: Context, in t: inout Table) throws -> NodeID?
}
public func transform<R: Rule>(_ roots: [NodeID], _ rule: R, in t: inout Table) throws -> [NodeID]
public protocol Pass { var name: String { get }
                       func owns(_ p: Pattern) -> Owned?                 // .rule, .unbuilt; nil: not its own
                       func run(_ roots: [NodeID], _ definitions: [Definition], in t: inout Table) throws -> [NodeID] }
public protocol Registry { func prove(_ lemma: Lemma, _ statement: NodeID, _ definitions: [Definition],
                                      in t: inout Table) throws -> Proved     // .proof(NodeID) or .unbuilt
                           func define(_ c: Defined, _ definitions: [Definition],
                                       in t: inout Table) throws -> Stated }  // .statement(NodeID) or .unbuilt
```

- **`after` sees the node as it stood** (`was`), beside `n`, rebuilt from its rewritten children: a rule consuming a
  term reads Isabelle's formula there, never a named form back (I1). Reify's instance reads it; every other rule
  ignores it.

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
| fol schema | `schemaInst(p, A)` — `schema_inst`: the letter at the top of `p`'s conclusion, instantiated at `A`. At `o`, `ifolAll`, `isaAllIntro` and `isaBound` are the schema's letter (§4a, "Logic") |
| isa — the typed quantifier only | `isaAllIntro(T, body)` ● (`ZAbst`, produces `ifolAll`) · `isaAllElim(p, t)` (`ZAppt`, consumes `ifolAll`; `t` any isa term of type `T`, concluding `instantiate(body, t)`). They also cover `⋀P:o` and `⋀P:i⇒o` — instantiating a proposition or class variable, as citing an IFOL rule does |
| isa — lowering's | `isaGuard(x, G)`: the guard of the bound variable `x`, concluding the formula it carries, as `hyp` does; Fol makes it the assumption it writes at `x`'s binder (§4a, "Fol") |

◆ binds a hypothesis, ● a term variable — exactly the checker rules that close a scope
(`src/proof/nd/stack.cpp`: `implies_intro:303`, `not_intro:351`, `forall_intro:495`,
`exists_intro:552` closing `exists_elim`, `classical_absurd:698`). Left out until a pass
needs them: `double_neg_elim`, `excluded_middle`, `peirce` (covered classically above);
`eq_subst`, `eq_sym` (`eq` is a defined predicate, FOUNDATION §2 retires `eq_subst`); `iota_elim` (S1).

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

**The passes.** Expand has its rules; Logic its rules for a proposition's letter, the logic's propositional axioms and
Pure's equality at `o` and at functions of propositions, and in its walk Reify's, a term named where it stands and an
instance at a compound term; Fol its rules for binders and variables at every object type and `∃` at `i`; the rest are
declared, unbuilt ("Lowering's components", below).

| # | pass | FOUNDATION | status |
|---|---|---|---|
| — | **expand** — the logic's defined constants unfolded, a citation of their definitions as `Pure.reflexive` | — | BUILT, below |
| — | **fol** — the binders and variables at every object type and `∃` at `i`: the guard Reify gives each binder, fol-zfc's variables | R3, S5, S6's enforceable form | BUILT, below |
| — | **logic** — an instance at `o` as a schema's `schema_inst`, or reduced on a ⋀-intro; the logic's propositional axioms as the kernel's steps; Pure's equality at `o` and at functions of propositions; Reify's naming and its instance at a compound term | S1, S4 | BUILT, below |
| — | the rest of **logic** — Lambda's instance at a class type, Pure's equality at objects — and Reify's provers, EX and UNIQ; each component's business in "Lowering's components", below | S1, S3, S4, S5, R3 | DECIDED, below; not built |

### Lowering's components  **[DIVISION DECIDED 2026-10-13 (user), REIFY AND TYPING ONE COMPONENT, THE REGISTRY APART 2026-10-14 (user); THE INTERFACE AGREED AND BUILT 2026-10-13 — `Sources/IR/Pass.swift`, `Sources/Lowering`]**

**Each component minds its own business** (user, 2026-10-13). In the reference every component knew the others'
gaps (`kinds-proposal` DESIGN.md, "Step C by contracts", reasons 1–3). Here a piece belongs to one component, and a
component that meets another's piece calls that component or cites its lemma; it never handles the piece itself.

| component | its business | calls |
|---|---|---|
| **Logic** | the logic's own primitives. First `expand` — the reference's, kept, and extended to Pure's defined constants, which this reader reads as defined: every Pure, IFOL and FOL defined constant unfolded by its definition at the use's type, and a citation of that definition read as `Pure.reflexive`. Then IFOL's and FOL's rules as the kernel's steps, and Pure's rules and `≡` at every type, congruence included; replacement of equivalents over a formula, its holes the caller's (`Replacement`), the one home of every congruence | — |
| **Reify** | terms and their types ("Reify and Typing as one component"). S1: a term, and a λ in a class slot, named where it stands; a constant's class, stated by its `@def`; an instance at a compound term, citing the EX and UNIQ of the term, which its prover states and proves per term, a constant's typing lemma being its EX; the guard each binder type gets (`set`, `function`, none) and its discharge ("Reify — S1 at the site"). No pass of its own: the logic pass's walk calls its code ("Reify called from Logic's walk") | Logic's replacement walk, Tuple |
| **Lambda** | a wrapper: a λ in a class slot is named by its definition where it stands, Reify's naming; Lambda's own are an instance at a class type, β as proof, and the λ's class existence, which EX's prover cites | Reify |
| **Tuple** | the tuple's lemmas at every arity — the reference's, kept | base |
| **Fol** | every isa binder and variable becomes fol-zfc's: a binder with the guard Reify gives its type, an instance and the guard of a variable discharged by that variable's guard; then `legalize` | Reify, for guards |

**The registry is no component**: it hands each lemma to the prover of the component that states it (`Provers`), knows
no type, and holds no lemma; the unit does.

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
   | after the last pass | a letter off its spine ("Logic", point 2) | refused, `letterOffSpine`, naming every such pattern |

   Before all three, a pattern two passes own stops the run (`PipelineError.twoOwners`), checked on every pattern a run
   meets. After the last pass, `legalize` checks that each statement is fol-zfc, and `misplacedLetters` that each of
   its letters stands where fol-zfc writes one. How a lemma enters the unit and is checked there: "The unit and its
   citations", below.
4. **A built rule never refuses.** What it cannot handle is either a pattern of its own, still unbuilt, or a lemma it
   cites, which the registry refuses (I2), or a letter it leaves off its spine, which the pipeline refuses after the
   last pass. So `transform` catches nothing and a pass returns node IDs.

**The owner of each of the reader's patterns**, from the division. The rows are coarse; each pass's step states its
own rows exactly.

| patterns | owner |
|---|---|
| a Pure, IFOL or FOL defined constant, or a ZF one at the meta level ("Expand", point 6); a citation of its definition | Logic, `expand` |
| a citation of an IFOL or FOL axiom; Pure's equality steps; Pure's `≡` at a function type; an instance at `o`; a binder, an instance or a `λ` at a type beyond objects other than `o` (a function of propositions or of classes) | Logic |
| an applied constant (a ZF primitive, a ZF definition at the object level, a declared constant, `IFOL.eq`); an applied variable; a `λ` at an object type; an instance at a class type, Lambda's | Reify, in the logic pass |
| a binder, a variable or the guard of a variable at `i`, `iⁿ ⇒ i` or `iⁿ ⇒ o`; an instance at `i`; `∃`-intro and `∃`-elim at an isa binder at `i` | Fol, with the guard Reify gives the type |
| a bound variable at another type | Fol, unbuilt: no such variable outlives its binder's owner |
| the both dialect's connectives, ⟹-intro and ⟹-elim, a hypothesis, a theorem or a lemma cited at no type arguments, and a binder, its intro and its variable at `o`, the schema's letter ("Logic") | none: fol-zfc has them |
| a type variable, `OFCLASS` or a theorem cited at type arguments (decision 4); the hidden variable; a citation of a ZF axiom, a theory axiom or a ZF definition at the object level | **no owner yet**: each is its component's design question, and is refused before the first pass |

**Built.** `Lowering.plan` is the three passes in order — expand, logic, fol — and `Lowering.pipeline` adds the
registry, `Provers`, proving after logic. Reify has no pass: the logic pass's switch asks Reify's for every pattern
Logic's own does not claim, and Reify has no rule. Expand and Logic have their rules ("Expand", "Logic", below). Fol has
the rules for binders, instances, variables and guards of variables at `i`. `Pattern.dialects` replaces `Node.dialects`
and `legalize` reads it. `RulePass` is gone: no rule writes a pattern its pass owns, so one walk is the whole pass.
`forall_elim` takes an isa variable of any type but `o`, as `folPred` does. `lower` counts a statement only when it
reaches fol-zfc.

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

### The unit and its citations — the framework's other half  **[AGREED AND BUILT 2026-10-14 — points 1–3, 5 and 6, the plan, three passes since "Reify called from Logic's walk", and the `@def` since "Reify — S1 at the site"; 4 in its own step — `Sources/IR/Pass.swift`, `Sources/Reader/Reader.swift`, `Sources/Lowering/Provers.swift`, `Fol.swift`]**

The pass-sets interface says which pass lowers what. This says what the reader hands lowering, and how a statement, a
lemma and a citation meet (I2; prerequisite 2 of the pass plan). Every component after Expand meets through it: Reify
states and proves EX and UNIQ, the registry routes each lemma, Tuple provides the tuple's lemmas. Built first, it leaves
no component to invent its own way to request, cite or refuse a lemma.

Today `lower`'s unit holds the named theorems only, `Statement` is `(name, root, proof)`, `Cited` has the reader's four
kinds, and nothing falls with a statement it cites.

**The plan is `expand · logic · fol`, with the registry proving between logic and fol.** Neither the registry nor Reify
is a pass; the logic pass calls Reify's code ("Reify called from Logic's walk"): Reify states and proves EX and UNIQ,
and Fol walks every binder, with the guard Reify gives its type. The guard pass's rules are Fol's
("Fol — binders, guards and variables", below).

**1. The reader provides what its theorems rest on.**
- **Every theorem they cite at no type arguments, transitively.** `read` proves the 200 cited outside the ZF sessions,
  but `lower`'s unit leaves them out, so such a citation names no statement lowering sees. A theorem cited at type
  arguments is decision 4's.
- **Every definition they reach.** A theorem may use `A ↔ B` without citing `IFOL.iff_def`, and Expand must still
  unfold `↔`. The unit holds the definition of each defined constant that occurs in a theorem or in a definition so
  reached, at each type it occurs at: `Definition(constant, type, definiens)`, an IR value, the `b` of `c ≡ b` read at
  that instance by the reader's one reading (I1).
- **A definition is lowered with the statements up to the pass that owns its constant, and read there.** Expand reads
  a Pure, IFOL or FOL definition as read, to unfold its constant; Reify's prover reads a ZF definition as Expand left
  it, to prove EX and UNIQ (point 4). A pattern that a pass before the owner has not built stops the
  definition there, and a lemma whose proof needs it is refused at the registry.
- An axiom a proof cites needs no provision: the citation carries its statement at its types (§4.7). The one Expand
  cites, `Pure.reflexive` at each definition's equation type, comes with the definition ("Expand", point 4).
- Replaces the reference's driver loop, which asked `Expand.instances` and `Reify.constantsToDefine` what to read, then
  expanded, compiled and guarded each ZF definition outside the pipeline.

**2. A citation of a theorem or a lemma names a statement of the unit, and falls with it.** `A` cites `B`, and `B`
stops at logic on a term only its proof holds. `A` holds `B`'s statement but not its proof, so the pipeline lowers
`A`, citing a claim that is never emitted. After the last pass, a statement citing a refused one is refused,
`cites(B)`, transitively (I2). The run stops on a citation naming no statement of the unit, on one whose root is not
its statement's root by ID, and on a cycle of citations.

**3. A lemma is stated and proved by the component that owns its request; the registry routes it.**
- A component cites a lemma by a typed request (I1): `use(.lemma(r), [], root)`. IR holds `r` by an identity and a
  name and never reads it (D3). The pattern is `use(lemma, [], o)`: both dialects, owned by no pass.
- The request's owner states `root` from `r` alone (I2), in the registry's vocabulary: no pattern that a pass before
  the registry owns. So every citer, at any pass, cites one node, and the passes before the registry leave it unchanged.
- After each pass, the pipeline adds every lemma that pass's output cites and the unit lacks, as a statement without a
  proof, in the order the walk meets them (§4.6 R3).
- After logic, the pipeline hands the registry each lemma without a proof. The plan gives the registry one prover per
  component that states lemmas — Reify, Tuple — so the registry never calls one by name. A prover owns its
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
  logic       ●  T's proof now cites L ─────────► added: S, as L's owner states it;   T, L
                 (Reify's code, in logic's walk)  no proof
  registry                                        ● handed to L's prover: a proof     T, L
                                                    of S, or unbuilt: L refused
  fol         ●  S becomes S′ in T's proof        ●  S becomes S′: one node            T, L
  link        kept, or refused: cites(L)
  ```
- Replaces the reference's `Pass.run → (rewrites, added)`; `Provider: Pass`, where the pass that added a lemma proved
  it in a job of its own; `Statement(citedAs:content:)`; `Run.claimed`'s registry of names; and lemmas named by
  strings (`c + "_EX"`).

**4. EX and UNIQ: one walk over a term, recursive through the registry.** A use cites EX of its term ("Reify — S1 at
the site", point 4) and never builds it, so the proof and the uses share no walk. Reify's prover proves it by walking
the term: at each application it cites the head's EX at its arguments, which the registry proves in turn, a
constant's at `c(x⃗)` by the same walk over its definition's body, down to the primitives, whose EX and UNIQ come from
base (S3: a body uses only constants defined before it). It walks the term only: a formula inside, such as a class
argument `λx. φ`, stays with its owner. UNIQ is the same walk, citing each head's UNIQ, the tuple's UNIQ and
membership's congruence (base).

```
EX ⟨succ(x)⟩, succ ≡ λi. cons(i, i): for every set x, some set r with ⟨⟨x⟩, r⟩ in succ's class
  some set r = cons(x, x)            the walk over cons(x, x), as Expand left it:
    the tuple ⟨x, x⟩ exists            Tuple: the tuple's EX at 2
    cons has a value at it             EX ⟨cons(x, y)⟩ at x, x, cited: the registry hands it to Reify, which
                                         walks Upair(a, a) ∪ A the same way, down to the primitives
  ⟨⟨x⟩, r⟩ in succ's class            succ's class definition (decision 5)
```

**5. The guard of a variable.** A proof before fol may need a guard that fol has not written yet: citing base's
`Pow_EX: forall A. (set(A) -> …)` at its own variable `y` needs `set(y)`. It writes `isaGuard(y, G)`, the guard of `y`,
concluding `G`, the guard Reify gives `y`'s type. The step carries its formula, as `hyp` does, so IR knows no guard.
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

Not in this step: emission, the unit in the order its citations and definitions require; and point 4 itself, EX's
and UNIQ's prover, which this one gives the registry, the definitions and the guard of a variable.

**A `@def` is a prover's answer** ("Reify — S1 at the site"). After logic, for each defined constant whose class
predicate a statement names, the registry asks the prover that defines it, unless the constant's definition, read under
its parameters, holds a pattern no pass owns or one a pass up to the registry leaves unbuilt: then the `@def` is
refused there. The unit holds a `@def` as a definition: no proof, its shape checked (R1), linked to every statement
naming the constant as to a citation, and a refusal carried to each.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | each named theorem of the ZF sessions and each theorem they cite at no type arguments, `(statement, proof)`; each definition they reach, at every type, with what Expand cites it by ("Expand", point 4) | an export of one build |
| the pipeline | each pass's input; each definition, as it stands at its owner's input, to that pass and to the provers; each cited lemma added once; the registry asked after logic; every citation linked, every refusal carried to its citers | each pass's `owns`; one registry |
| a citer | `use(.lemma(r), [], root)`, `root` the owner's statement of `r` | the registry proves `r`, or refuses it there |
| the registry | each lemma handed to the one prover that owns its request | the plan's provers |
| a prover | for each request it owns, by one switch: its statement, from the request alone, and a proof of it, or unbuilt | the definitions at their owners' input; the statements of the lemmas it cites |
| Fol | each binder with the guard Reify gives its type; each instance and each guard of a variable discharged by that variable's guard; each variable fol-zfc's | Reify's guards |

**Tests, written first.** `PipelineTests`, on fake passes and a fake registry: a statement citing a refused one is
refused, transitively; a lemma two statements cite is added once, unchanged until the registry, and lowered with both
as one node; the registry hands each lemma to the prover that owns it, and the lemmas its proof cites in turn; a lemma
its prover has not built is refused there, and its citers fall; a pass reads the definitions of the constants it owns
as they stand at its input; the run stops on a citation of no statement, two statements for one lemma, a cycle of
citations, a lemma cited after the registry, a lemma holding a pattern that a pass before the registry owns, and a
lemma named as a theorem. `TableTests`: the guard of a variable concludes its formula. `ReaderTests` (`UnitTests`): the
unit holds each theorem its theorems cite at no type arguments, and the definition of each constant they reach, at
each type, `c ≡ λx. b` and `primrec`'s applied `c(x) ≡ b` alike. `LoweringTests`: the guard's tests, run on Fol, and
the guard of a variable (`FolTests`); the registry hands a lemma to the one prover owning its request, and a request
no prover or two own stops the run (`ProversTests`); the plan is its passes, the registry proving after the
last one before fol, with no prover yet (`PlanTests`).

**Built.**
- IR: `Statement` is a theorem or a lemma (`lemma: Lemma?`, `proof: NodeID?`); `Cited.lemma(Lemma)`, `Lemma` holding a
  `Request` by its identity and name; `Definition(constant, type, definiens)`; `Unit.definitions`; `Pass.run(roots,
  definitions, in:)`; `Registry`, answering `Proved.proof` or `.unbuilt`; `Pipeline(passes:, registry:, provingAfter:)`;
  `isaGuard(x, G)`; `PipelineRefusal` `lemmaUnbuilt`, `cites`, `unread`.
- Reader: `Reader.unit()`. ⚠ **A DEFINITION IS WRITTEN IN TWO FORMS**: `c ≡ λx. b`, and the applied `c(x) ≡ b` that
  `primrec` writes, its arguments the axiom's frees in their order (`ZF.iterates.iterates_nat_def`). Both read as the
  definiens `λx. b`; a third form stops the read, `MalformedExport.notADefinition`.
- Lowering: `Provers` is the registry, routing to `Prover`s; `Lowering.pipeline` has none yet. Fol has the guard's rules,
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
`IFOL.term_class_def` defines the class `IFOL.term`'s membership, which the reader reads as `isaOfClass`, never as the
constant `IFOL.term_class`: Expand unfolds it by that definition, and a citation of it is `reflexive` ("OFCLASS — a
class's membership by its definition", 1 and 2).

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

**Since "A definition read at its terms"** a definition's citation carries the terms its application has, and the rule
is `reflexive` at them, a `⋀`-intro only for a parameter the application leaves.

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

### Logic — a proposition as a schema letter, the logic's rules as the kernel's  **[AGREED AND BUILT 2026-10-14 — `Sources/Lowering/Logic.swift`, `Sources/IR/Legalize.swift`; point 3's reduction and point 4 REMOVED 2026-10-15, "Removed — the rules that consumed a proposition where it stood"]**

**Logic reads Isabelle's `⋀P::o` as the one thing fol-zfc has for it, a schema letter, and makes each axiom of the logic
that binds only propositions the kernel's own step.** It is the Logic component's pass after `expand` ("Lowering's
components"). This step builds the part of Logic that needs neither an equation between functions nor a citation of
base; the rest of its rows are owned and unbuilt: the next step (7).

**What Logic receives** is Expand's row: no Pure, IFOL or FOL defined constant; every axiom's statement unfolded; a
definition's citation as `Pure.reflexive` at its equation's type.

**Where its patterns sit** (a scratch survey of the unit after Expand, not kept):
- A `⋀P::o` the reader writes stands on a statement's top chain: Isabelle's closure over a theorem's propositional
  variables (`conjE`, `ccontr`, `ballE`'s `R`). 672 named theorems bind one at their top, and 6,599 instantiate a cited
  theorem at a proposition. The reader writes one below a top only in four named theorems of `MetaExists` and
  `Inductive`, each with no owner already.
- Expand writes one below a top wherever it unfolds one of the three definitions whose definiens binds a proposition:
  `Pure.conjunction` (`&&&`), `Pure.term` (`TERM`), `MetaExists.ex`.
- The only axioms of the logic named ZF proofs cite are Pure's seven. IFOL's and FOL's are cited by the logic's own
  theorems: `IFOL.conjI`'s proof is the axiom at the theorem's own variables.
- Of the 1,078 named theorems stopping at logic, 520 hold only what this step builds. The other 558 hold Pure's `≡` or
  one of its rules at `i` or at a function type, or a variable of a type beyond objects other than `o`.

**FOUNDATION first.** S4's arity-0 sentence ("there is no such rendering and none is wanted") is replaced by the
reference's paragraph of 2026-10-01 (`kinds-proposal`, `19782f9c`): a schematic `P :: o` is a schema letter; a
statement binding propositions is a schema, proved once with its letters uninterpreted, and each use instantiates it;
the `⋀P::o` of the logic's rules stay the kernel's own steps; a function of propositions has neither rendering. Its
correction box comes with it, and §3b's mapping gains the row "`⋀P :: o` at a statement's top, `AppT` at it | a schema
letter, `schema_inst` (S4)". The rest of the reference's FOUNDATION stays the open decision it is.

**1. A propositional `⋀` is fol-zfc's letter, in Isabelle's own nodes.** The binder `ifolAll(o, φ)`, the ⋀-intro proving
it `isaAllIntro(o, p)` and the bound proposition `isaBound(k, o)` are the schema's letter binder, its proof's letter and
the letter. `Pattern.dialects` reads the three at `o` as both dialects, as it reads a citation at no type arguments: no
pass owns them, and Fol walks a letter binder as an unguarded one. No new kind: §3's "a schema variable becomes a table
node kind then" is superseded.

```
Isabelle    IFOL.conjE: ⟦P ∧ Q; ⟦P; Q⟧ ⟹ R⟧ ⟹ R
read        ⋀P Q R::o. P ∧ Q ⟹ (P ⟹ Q ⟹ R) ⟹ R               ifolAll(o, ifolAll(o, ifolAll(o, …)))
emitted     schema IFOL.conjE [A0, A1, A2]: ((A0 & A1) -> ((A0 -> (A1 -> A2)) -> A2))
```

**2. A letter stands only where fol-zfc writes one.** That is fol-zfc's grammar, so it is `legalize`'s (IR), the one
place that says what fol-zfc is:
- a letter binder on a root's spine, a statement's or a cited statement's: under `∀` and on the right of `→`. Fol's
  guard keeps it there: `∀x. set(x) → ⋀P. φ`;
- a letter's ⋀-intro on a proof root's spine: under `forall_intro` and `implies_intro`;
- an instantiation on a citation's spine (3).

After the last pass, a statement holding a letter anywhere else is refused, `letterOffSpine`, naming it: FOUNDATION S4's
"no rendering". The emitted schema declares the letters its spine binds, and its proof drops their intros. Of the 520,
68 hold one off its spine: a `⋀C::o` from `&&&`, `TERM` or `ex` unfolded; a box whose propositional parameter follows a
set parameter (3); a proof of a `⋀`-premise.

**3. An elimination at `o` is Logic's rule.** ⚠ **ITS REDUCTION AT A ⋀-INTRO IS REMOVED** ("Removed — the rules that consumed a proposition where it stood"): it read
its premise's shape, standing in for a proposition bound below a top, which FOUNDATION S4 now renders as a truth set.
`isaAllElim(p, A)` at `o` reduced where `p` is a ⋀-intro at `o`, an inlined
box instantiated at once or an axiom's step (4), by `instantiate` at the proof level: the pass plan's box "reduced at
the proof level". It is now `schema_inst` everywhere, a new fol-zfc step `folSchemaInst(p, A)`, concluding the letter at
the top of `p`'s conclusion instantiated at `A`. It is a step per letter, as Isabelle's `AppT` is; emission writes one
`schema_inst` per citation, with every letter its spine instantiates, ahead of the spine's `forall_elim`s. That is sound
because a letter hoists across `∀` and the right of `→`.

```
Isabelle    conjE at A, B, C, applied to h ⊢ A ∧ B and k ⊢ A ⟹ B ⟹ C
read        folImpliesElim(folImpliesElim(isaAllElim(isaAllElim(isaAllElim(use conjE, A), B), C), h), k)
logic       folImpliesElim(folImpliesElim(folSchemaInst(folSchemaInst(folSchemaInst(use conjE, A), B), C), h), k)
emitted     _1 = schema_inst IFOL.conjE {A0: A, A1: B, A2: C}
            _2 = implies_elim _1, h
            _3 = implies_elim _2, k
```

A redex at `i` stays: `forall_intro` then `forall_elim` is fol-zfc. So a box `⋀x::i. ⋀P::o. …` instantiated at once keeps
its `P` behind the redex at `x`, and its letter is off its spine (2). Reducing through a redex at `i` is a shape (D1);
such a box waits for boxes' own design — since "Boxes binding a proposition, read as schemas", a statement of its own. Reading every box at its instance in the reader is not that design: a scratch
run grew the read past 20 GB and 8 minutes before it was stopped, against 4.3 GB and 88 s.

**4. An axiom of the logic binding only propositions is the kernel's step.** ⚠ **REMOVED** ("Removed — the rules that consumed a proposition where it stood"): the
kernel's proof built in place is what point 3's reduction consumed; FOUNDATION S4 reads an application of the rule as the
kernel's step instead, and until then these axioms are Logic's, unbuilt. The 16 instances are Pure's `equal_intr` and
`equal_elim`, and `reflexive`, `symmetric`, `transitive` at `[o]`; IFOL's `impI mp conjI conjunct1 conjunct2 disjI1
disjI2 disjE FalseE iff_reflection`; FOL's `classical`. A citation of one becomes the kernel's proof of its statement: a
⋀-intro at `o` per letter around the kernel's step, built from the `Axiom` alone (I1), never by reading the statement
back. The eliminations above it reduce it (3), so each use is the kernel's own rule at its instance (FOUNDATION §3b),
and the pipeline checks that each proof still concludes its statement, by ID. Since the second step Pure's five are no
axioms but steps, and the instances are IFOL's and FOL's 11.

```
axiom, as read after Expand                     its proof, inside a ⋀-intro per letter
IFOL.conjI       ⋀P Q. P ⟹ Q ⟹ P ∧ Q              implies_intro P (implies_intro Q (and_intro (hyp 1) (hyp 0)))
Pure.equal_elim  ⋀A B. (A ↔ B) ⟹ A ⟹ B           implies_intro (A ↔ B) (implies_intro A (iff_elim_l (hyp 1) (hyp 0)))
FOL.classical    ⋀P. ((P ⟹ ⊥) ⟹ P) ⟹ P            implies_intro h (classical_absurd P [n: ¬P]
                                                    not_elim n (implies_elim h (implies_intro P (not_elim n (hyp 0)))))
```

`impI` and `mp` read alike, since `⟹` and `⟶` are one node: both are the identity on `P ⟹ Q`.

**5. Logic's rows, exactly** — one switch over `Pattern`, dispatching the two rules:

| pattern | answer |
|---|---|
| `use(axiom a, types, o)`, one of the 16 instances (4) | rule |
| `isaAllElim(o, o)` | rule (3) |
| `use(axiom a, types, o)`, any other axiom of the logic at types with no type variable: Pure's `reflexive`, `symmetric`, `transitive` at `i` or at a function type; `combination`; `abstract_rule` | unbuilt (7) |
| `isaConst(primitive Pure.eq, T ⇒ T ⇒ o, …)`, `T` a function type with no type variable | unbuilt (7) |
| `ifolAll`, `ifolEx`, `isaAllIntro` or `isaAllElim` at a type beyond objects other than `o`, with no type variable | unbuilt (7) |
| `ifolAll(o, …)`, `isaAllIntro(o, …)`, `isaBound(o)` | none: fol-zfc's letter (1) |
| `ifolEx(o, …)` | none, and fol-zfc lacks it: refused before the first pass |
| every other pattern | not its own |

"Beyond objects" is neither `i`, `iⁿ ⇒ i` nor `iⁿ ⇒ o` (`isObject`). Fol stops owning `isaBound(o)`: a letter is
fol-zfc's. The coarse table's Logic row changes with it: a binder at `o` is no pass's, but fol-zfc's letter.

**6. What the framework gains.** IR: `Pattern.dialects` reads `ifolAll`, `isaAllIntro` and `isaBound` at `o` as both
dialects; `folSchemaInst(p, A)` is a fol-zfc step whose conclusion is computed at `intern`, `principalConnective` unless
`p` concludes a letter binder; `legalize` checks (2). The pipeline gains a refusal after the last pass,
`letterOffSpine([Pattern])`, which `lower` reports as a group, and the pass-sets table its row. FolDialect renders a
schema and `schema_inst` when emission is built.

**7. Next: Pure's `≡` and rules at a function type.** They wait because an equation between functions of propositions has
no fol-zfc statement. `f ≡ g` at `o ⇒ o` says `⋀P. f P ↔ g P`, a proposition bound below a top. So a proof through
`combination` at `[o, o]`, the simplifier rewriting inside a formula, has no image step by step: what it proves at its
instance, `φ(A) ↔ φ(B)` from `A ↔ B`, is the context's congruence, proved per formula from `base`'s `cong_*` schemas. At
an object function type, `f ≡ g` is pointwise, `∀x. f x ↔ g x`, a statement over classes. That design is the next
step. Pure's rules at `i` wait with it: `≡` at `i` is `IFOL.eq`, and their proofs are base's `eq_refl`, `eq_symm` and
`eq_trans`, cited where Reify names their sides, in the logic pass's walk ("Reify called from Logic's walk").
`IFOL.TrueI`'s own proof rewrites by `combination` at `[o, o]`, so the 51 that fall with it stay.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Logic | every statement, proof and definition it walks free of its two rules' patterns, each proof still concluding its statement by ID; every propositional `⋀`, its intro and its variable left as fol-zfc's letter; each axiom of the logic binding only propositions as the kernel's step at its instance | Expand's row: no Pure, IFOL or FOL defined constant, and every axiom's statement unfolded |
| the pipeline | a statement holding a letter off its spine refused after the last pass, `letterOffSpine`, and its citers with it | `legalize`'s grammar for letters |
| Fol | a letter binder walked as an unguarded binder; a letter left as it stands | — |

**Tests, written first.**
- `PlanTests`: Logic answers `.rule` for the 16 instances and for `isaAllElim(o, o)`; `.unbuilt` for `Pure.reflexive` at
  `[i]` and at `[o ⇒ o]`, for `combination`, for `≡` at `o ⇒ o` and for a binder at `o ⇒ o`. `ifolAll(o, …)`,
  `isaAllIntro(o, …)` and `isaBound(o)` have no owner and are fol-zfc's. No pattern has two owners.
- `LogicTests`, Logic run alone, each proof checked to conclude its statement by ID: a citation of `conjI` eliminated at
  `A` and `B` is `and_intro`'s proof at them; `classical`, likewise; a ⋀-intro at `o` eliminated at once reduces; a
  citation of a theorem binding a proposition, eliminated at `A`, is `folSchemaInst`; a schema's own proof keeps its
  letters' intros; a box at `o` behind a redex at `i` is `folSchemaInst`.
- `TableTests`: `folSchemaInst` concludes its premise's letter at the instance, and refuses a premise that does not
  conclude a letter binder.
- `LegalizeTests`: a letter binder on the left of `→`, a letter's ⋀-intro inside a proof, an instantiation of a hypothesis
  are each off their spine; a letter under Fol's guard is on it.
- `PipelineTests`: a statement holding a letter off its spine is refused `letterOffSpine`, and its citers fall.

**Kept from the reference, and changed.** Kept: FOUNDATION's arity-0 S4; the logic's rules as kernel steps built from the
axiom and checked by ID; a ⋀-intro eliminated at once reduced by `instantiate`; a redex at `i` stays. Changed:
- No schema pass and no statement kind (`.schema(proof:letters:)`, `Schema.letters`, `schemaShape`): the letter is
  Isabelle's own `⋀` at `o`, fol-zfc's by `Pattern.dialects`.
- No refusal by name inside a pass (`partialInstantiation`, `propositionBoundInProof`): where a letter stands is fol-zfc's
  grammar, checked once, at `legalize`.
- No proof put in place for a citation beyond sets and classes: a cited theorem binding a proposition is a schema, and
  its use instantiates it.
- No reduction through redexes at `i` (`reducedUnderRedexesAtI`): it is a shape. Such a box is refused until boxes are
  designed.
- No `evaluate` into `isaCongruence`: it is a shape. The congruence is the next step's, from its primitive.

**Built.**
- IR: `Pattern.dialects` reads `ifolAll`, `isaAllIntro` and `isaBound` at `o` as both dialects; `folSchemaInst(p, A)`,
  its conclusion computed at `intern`; `misplacedLetters`, beside `legalize`, the grammar (2); the pipeline refuses
  `letterOffSpine` after the last pass, and `lower` reports it as a group.
- Lowering: `Logic` owns its rows by one switch (`piece`) dispatching its two rules; the kernel's proofs are built
  from a `Kernel` case, one per instance but `impI` and `mp`, which share the identity. Fol answers `isaBound(o)` not its
  own, reading `Pattern.dialects`. `Anywhere` and `children` moved to `Plan.swift`, one home for Expand, Logic and Fol.
- FolDialect: `render` refuses a letter and `schema_inst`, `RenderError.schema`, until emission writes schemas.

**Measured** (`isa2fol lower data/zf_export`): 3 named theorems are lowered to fol-zfc, the first: `ZF_Base.strip.1`,
`func.basic_monos.2` and `.4`, the logic's `impI`, `imp_refl` and `conj_mono` under ZF's names. 23 theorems cited
outside the ZF sessions lower with them, schemas the kernel's steps prove. Refused: no owner 7,176, logic 558, reify
1,631, and 52 that cite a refused statement: `IFOL.TrueI` 51, `FOL.disj_mono` 1 (`func.basic_monos.3`). Of the 520 that
leave logic, 516 stop at reify; no statement reaches the letter grammar off its spine yet, since every one holding such
a letter holds a pattern Reify owns. Read 65.8 s, lowered 20.5 s.

### Reify called from Logic's walk — the plan of three passes  **[AGREED AND BUILT 2026-10-14 — `Sources/Lowering/Plan.swift`, `Reify.swift`, `Logic.swift`]**

**Reify stops being a pass.** Its code stays Reify's, and the division is unchanged: Reify names a compound term where
it stands (S1) and states and proves EX and UNIQ. Only the plan changes. Reify no longer walks the unit: the logic pass
calls Reify's code at each of Reify's pieces, and wherever a rule of Logic's needs a term as a variable. A component is
how the code is organized, never a framework notion (user, 2026-10-14): the framework knows passes only, and is
unchanged. The registry has no pass either.

```
before      expand · logic · reify · fol      the registry after reify
now         expand · logic · fol              the registry after logic; Reify's code called in logic's walk
```

**The problem, in target text.** With Reify a pass after Logic, no rule of Logic's can name a term, yet every fact Logic
needs about one is stated over variables: base's `eq_symm`, `eq_trans` and `mfun_comb`; Reify's EX and UNIQ; a
constant's argument congruence.

```
Isabelle   symmetric p,   p : f(a) = b                                     ⊢ b = f(a)
wanted     eq_symm at r and b, applied to p, where r names f(a): ⟨⟨a⟩, r⟩ ∈ F
logic      f(a) is still a term, and fol-zfc instantiates only at a variable: eq_symm cannot be cited here
reify      names f(a), but the step is Logic's, and Logic has run
```

The only way through was a copy of each fact in Isabelle's vocabulary, which Logic states, Reify lowers and the registry
proves; its statement would hold Reify's patterns, which point 3 of "The unit and its citations" forbids. With Reify's
code in Logic's walk, the rule has `f(a)` named where it stands and cites `eq_symm` as base states it.

**1. One walk.** The logic pass owns Logic's pieces and Reify's: an applied constant (`IFOL.eq` among them), an applied
variable, a λ at an object type. Its `owns` answers Logic's own pieces and asks Reify's switch for every pattern Logic's
does not claim. Reify's switch, exhaustive over `Pattern` in Reify's file (D3), lists Logic's pieces among those it does
not claim. To the pipeline the logic pass owns patterns by one `owns`, as every pass does.

**2. What Reify provides.**
- Per constant: its class. Per term an instance meets: EX and UNIQ, stated from the term alone and proved once by the
  registry ("Reify — S1 at the site", point 4). A use cites them and never builds one.
- Per site: a term named where it stands (S1), and a statement instantiated at a compound term (FOUNDATION §3b's
  `appt_complex`), citing EX, and UNIQ where two namings of one term meet.
- No state of its own. Naming a term is a function of its site alone, its variable bound where it stands (`P(f(a))`
  is `∃r. ⟨⟨a⟩, r⟩ ∈ F ∧ P(r)`), so interning gives one node per site whoever asks, the walk or a rule of Logic's, and
  every consumer matches its premise by ID. The lemmas it requests are the unit's, added once by the pipeline (I2). A
  cache would be for speed only.

It assumes ZF's definitions as Expand left them: its prover walks a body as a term.

**3. No rule writes an unnamed term.** No pass after logic names one. A rule of Logic's that needs a term as a variable
asks Reify, and an instantiation at a compound term, Logic's β at a box among them, has Reify name the argument first
and instantiates at its variable. "A pass never writes a pattern it owns" now holds Logic to Reify's pieces too.

**4. Logic's rules at objects meet named premises.** In one bottom-up walk a step's premises arrive named, and those
rules need the sides as they stood, `f(a)` rather than its naming, to hand Reify. How they read them is the design of
the step that builds them; reading a named form back would be parsing back (I1).

**5. A λ is named where it is consumed, never at its own node.** That keeps the reason the plan ran logic before reify
("The meta level, lowered", decision 2): an IFOL rule at a λ, reduced by Logic, builds no class. In one walk the λ's node
is reached before the step holding it, so Lambda's rule acts at that step, not at the λ. A λ is divided by its type: at
an object type Reify's, through Lambda; beyond objects, over propositions or over classes, Logic's, a context its Pure
step consumes. Today Reify owns every λ, which works only because Logic consumes its own before Reify runs: in one walk
the 416's `λP. P` would be refused as Reify's unbuilt piece.

**6. The registry proves after logic.** A lemma's statement still holds no pattern of a pass before the registry, now
expand and logic, Reify's pieces included. EX and UNIQ are stated over variables, as before.

**The agreed text changed with it.**
- "Lowering's components": the plan; the owner table, Reify's pieces owned by the logic pass and dispatched to Reify's
  code, a λ beyond objects Logic's.
- "The unit and its citations": the plan line and the diagram, the registry after logic; point 1, Reify's prover reads
  a ZF definition as Expand left it; point 4 loses "the walk Reify makes wherever Isabelle instantiates at a compound
  term": a use cites EX, EX's proof walks the definition, and the two share no walk.
- "Logic", point 7: base's `eq_*` are cited where Reify names their sides, not by the first step that cites base.
- "The meta level, lowered": the passes table and decision 2.
- `CLAUDE.md`: the plan.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reify | per constant, its class; per term an instance meets, EX and UNIQ, proved once by the registry; per site, a term named where it stands and an instance at a compound term, one node per site | the logic pass asks it at each of its pieces; ZF's definitions as Expand left them |
| Logic | its rules; a term it needs as a variable asked of Reify, never written | Reify's provisions |
| the logic pass | Logic's pieces to Logic's rules, every other pattern to Reify's switch | Logic's switch and Reify's claiming no pattern in common |
| the pipeline | the registry asked after logic | — |

**Tests, written first.**
- `PlanTests`: the plan is expand, logic, fol, the registry proving after logic; each of Reify's pieces is the logic
  pass's, as Reify's switch answers it, and Reify's switch claims none of Logic's; a λ at an object type and one
  beyond objects are both the logic pass's.
- Reify's own step adds its tests: a site named twice is one node, whoever asks; a use cites EX and builds no chain.

**Built.** `Reify` is no `Pass`: a struct holding its switch, which `Logic.owns` asks for every pattern Logic's own
switch does not claim. A λ at an object type is Reify's, a λ beyond objects Logic's, unbuilt. `Lowering.plan` is
`[Expand(), Logic(), Fol()]`, the registry proving after `logic`. Reify has no rule yet: a statement holding one of its
pieces is refused before the logic pass. The framework is unchanged.

**Measured** (`isa2fol lower data/zf_export`), as deduced from each statement being refused where it first stops: 3
lowered, and 23 theorems cited outside; no owner 7,176; logic 2,189, the 558 and the 1,631 that stopped at reify,
naming 277 patterns, Reify's among them (`isaConst(defined zf object, (i => i), args: [i])` 1,268, the most frequent);
52 cite a refused statement. Read 64.9 s, lowered 20.9 s.

**Kept from the reference, and changed.** The reference ran reify as a pass after logic, and carried Logic's congruence
across it in a node, `isaCongruence`, for its reify to expand. Kept: S1 at the site; an instance at a compound term by
EX (`appt_complex`); UNIQ where two namings meet. Changed: no reify pass and no node crossing one; Reify's code is called
where its piece stands.

### Reify and Typing as one component; the registry apart  **[AGREED AND BUILT 2026-10-14 — `Sources/Lowering/Provers.swift`, `Reify.swift`, `Fol.swift`]**

**The problem: one fact proved twice, one concept in two homes (D3).** The division gives Typing "the typing lemmas" and
the guard each type gets, and Reify EX and UNIQ:
- A constant's typing lemma, its value at sets a set (the reference's `Typing.statement`, `∀x. set(x) → ∃y. set(y) ∧
  y = c(x)`), is its EX, in the class form `∃r. set(r) ∧ ⟨⟨x⟩, r⟩ ∈ F`. Both components would walk the constant's
  definition to prove it.
- The guard of a variable at `iⁿ ⇒ i` is `mfun`, a class that is a function on the tuples; a constant's EX and UNIQ are
  its class's `mfun` ("The meta level, lowered", decision 5). Typing's discharge of that guard at a constant's class
  would cite Reify's lemmas.
- Naming a term needs EX, and the guard `set(r)` of the variable that names it: Reify would call Typing for the guard.

**The replacing rule: Reify is the one component for terms and their types.**

| Reify | provides |
|---|---|
| per site | a term named where it stands (S1); a statement instantiated at a compound term (§3b's `appt_complex`) |
| per constant | its class, stated by its `@def` |
| per term | EX and UNIQ of each term an instance meets, stated from the term ("Reify — S1 at the site", point 4) and proved from the definitions, cited by every use |
| per type | the guard: `set(x)` at `i`, `function(F)` at `iⁿ ⇒ i` (single-valued, no arity: a function variable's application is base's `apply`), none at `iⁿ ⇒ o`; and its discharge: at a variable by its binder's hypothesis (Fol's), at a named term by S1's `∃`, at a constant's class by EX and UNIQ of `c(x⃗)` |

It keeps no state of its own ("Reify called from Logic's walk", point 2).

**The registry stays apart.** It routes a lemma request to the one prover owning it, Reify's or Tuple's, knows no type
and holds no lemma, the unit does. That is the pipeline's plumbing, not a component's business, so it is named
for what it is. In code `Typing`, the `Registry` the pipeline asks, becomes `Provers`, and `TypingError` becomes
`ProversError`; `Typing.guarded` moves to Reify, which Fol asks for a binder's guard.

**The agreed text changed with it.**
- "Lowering's components": the division table loses Typing's row; Reify's gains the guards and their discharge, and the
  typing lemma as its EX; Fol "calls Reify, for guards"; the registry gets a line of its own. The owner table's Fol
  row: "with the guard Reify gives the type".
- "The unit and its citations": "Typing's registry" becomes "the registry", and the provers per component are Reify's
  and Tuple's; point 5, "the guard Reify gives `y`'s type"; the contracts.
- "Fol": `Reify.guarded`; "Reify has no guard for the type yet".
- §1 and `CLAUDE.md`: Typing's registry becomes the registry.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reify | per site, per constant, per term and per type, as above | ZF's definitions as Expand left them; Tuple's lemmas; base |
| the registry | each lemma handed to the one prover owning its request | the plan's provers |
| Fol | each binder with the guard Reify gives its type; each instance and each guard of a variable discharged by that variable's guard | Reify's guards |

**Tests, written first.** `TypingTests` become `ProversTests`, unchanged in what they check: one owner proves, none or
two stop the run, an unbuilt prover refuses the lemma. `FolTests` unchanged: Fol's guard is now asked of Reify.

**Built.** `Typing.swift` is `Provers.swift`: `Provers`, the registry, routes to the plan's `Prover`s and throws
`ProversError.owners` when none or two own a request. `Reify.guarded` gives the guard at `i`, which Fol asks for. No
pattern changes owner.

**Measured** (`isa2fol lower data/zf_export`): unchanged, 3 lowered; no owner 7,176; logic 2,189; 52 cite a refused
statement.

**Kept from the reference, and changed.** The reference's `Typing` built the statements of per-constant lemmas
(`statement`, `argumentCongruence`) that its reify proved and its other passes cited. Here the component that walks a
definition states and proves the constant's facts, and the router is not named for a type.

### Logic's second step — Pure's equality read as the kernel's steps; the congruence at a function of propositions  **[AGREED AND BUILT 2026-10-14 — `Sources/Reader/Reader.swift`, `Sources/IR/Table.swift`, `Sources/FolDialect/Parse.swift`, `Sources/Lowering/Logic.swift`, `Base.swift`; the congruence at a function of propositions REMOVED 2026-10-15, "Removed — the rules that consumed a proposition where it stood"]**

**Logic's 558 are Pure's equality: `≡` at a function type, and Pure's rules at `i` and at a function type** ("Logic",
point 7). This step takes the bulk, Pure's rules at `o` and at a function of propositions, which 416 of the 558 hold.
It needs one change upstream first: Pure's equality rules read as steps.

**The problem, in target text.** The simplifier rewrites `fact ⊢ B` by a rule `q ⊢ A ≡ B` as `equal_elim (symmetric
(combination (reflexive Trueprop) q)) fact`. The reader erases `Trueprop` and reads `≡` at `o` as `↔`:

```
R = isaAllElim(use(axiom Pure.reflexive, [o ⇒ o], …), λP. P)                   ⊢ (λP. P) ≡ (λP. P)
C = isaAllElim⁴(use(axiom Pure.combination, [o, o], …), λP. P, λP. P, A, B)    ⊢ (λP. P) ≡ (λP. P) ⟹ (A ↔ B) ⟹ (A ↔ B)
    folImpliesElim(folImpliesElim(C, R), q)                                     ⊢ A ↔ B
```

`R` concludes an equation between functions of propositions, which has no fol-zfc formula: FOUNDATION S4 gives a
function of propositions no rendering. An equation between object functions has one, pointwise ("The meta level,
lowered"); beyond objects, at a function of propositions or of classes, there is none. Yet `R` reaches `combination`
through `⟹`-elim, fol-zfc's own step, which needs its antecedent as a formula. A rule local to `use combination` sees
neither `R` nor the `λ` it is instantiated at: both stand above it. So `combination` at a function of propositions has
no local translation in today's reading (D1: design work, raised). The reference evaluated the chain below a base-type
conclusion into `isaCongruence`: a walk down the chain's shape.

**The replacing rule: Pure's equality rules are read as Pure's own inference steps**, as the reader reads Pure's `⟹` and
`⋀` (§4.7) and as Isabelle's kernel has them (`Thm.reflexive` … `Thm.equal_elim`). An application is one node whose
premises are its children, so each rule meets its premises where it stands:

| Pure's rule | read as |
|---|---|
| `equal_intr`, `equal_elim` | `folIffIntro(p, q)`, `folIffElimL(p, q)`: `≡` at `o` is `↔`, so they are fol-zfc's own steps, read downstream-first |
| `reflexive` at `t` | `isaReflexive(t)`, concluding `t ≡ t` |
| `symmetric`, `transitive` at `T` | `isaSymmetric(T, p)`, `isaTransitive(T, p, q)` |
| `combination` at `[T, U]` | `isaCombination(T ⇒ U, p, q)`: from `f ≡ g` and `x ≡ y`, `f x ≡ g y`, β-reduced |
| `abstract_rule` at `[T, U]` | `isaAbstract(T ⇒ U, p)`: from `⋀x. f x ≡ g x`, `(λx. f x) ≡ (λx. g x)` |

The reading of `≡` (`↔` at `o`, `IFOL.eq` at `i`, `Pure.eq` elsewhere) moves from the reader to IR, one home for the
reader and for the table, which computes these steps' conclusions. Every application in the unit's proofs is complete
(`combination` 107,827, `transitive` 38,541, `symmetric` 34,953, `reflexive` 19,783, `abstract_rule` 4,069,
`equal_intr` 51), but for 14 of `equal_elim`'s 45,005, which lack its last premise; those are η-expanded at read (a
scratch count, not kept). §4.3b changes with it: Pure contributes its equality as inference rules, not axioms; the
`Axiom.pure` cases and the previous step's kernel proofs of them go.

**A proof of an equation between functions of propositions becomes the congruence it carries.** ⚠ **REMOVED** ("Removed — the rules that consumed a proposition where it stood"):
the form stood only where its consumer reduced it, reading its premise's shape; FOUNDATION S4 renders `f ≡ g` at `o ⇒ o`
as `∀E. E ⊆ {∅} → (f*(E) ↔ g*(E))`, and until then these steps are Logic's, unbuilt. At `o⃗ ⇒ o`, Logic wrote
it as

```
ΛP₁ Q₁ … Pₙ Qₙ. (P₁ ↔ Q₁) ⟹ … ⟹ (Pₙ ↔ Qₙ) ⟹ (f P⃗ ↔ g Q⃗)
```

the letters first, then the hypotheses. It is no reading: the equation is never stated, and this proof stands only
where its consumer reduces it in the same walk — a `combination`, or a `symmetric` or `transitive` that builds another.
A stated equation between functions of propositions (a theorem's, a hypothesis's, a cited statement's) has no rule;
Logic owns it unbuilt, since a definition's citation carries one in its statement, which Expand replaces.

- `isaReflexive(λP⃗. φ)`: φ's congruence, by a walk over φ. A hole is its hypothesis; a subformula with no hole is base's
  `iff_refl`; a connective is base's `cong_and`, `cong_or`, `cong_imp`, `cong_iff` or `cong_not` at its sides; a `⋀` at
  `o` is the letter's own steps, whose letters then stand off their spine and are refused after the last pass, as
  Expand's `&&&` makes them. Any other node above a hole stops the run, `LogicError.context`: no refusal, but a reading
  missing upstream. A context of propositions is a head: `Trueprop`'s identity, a connective or a partial application of
  one (its fixed arguments hold no hole), or the body Expand unfolds of one of the logic's constants taking
  propositions — `prop`, `&&&`, `TERM`, `Not`, `iff`, FOL's `induct_implies` and `induct_conj` — each holding its
  arguments only under connectives and a `⋀` at `o`. A hole under a binder or inside an argument comes through
  `abstract_rule` or a `combination` at a class or term type. Measured over the 416: a hole is the whole context, the
  identity `Trueprop` erases to, 407 times; it stands under connectives 314 times, under a `⋀` at `o` 59 times, and
  nowhere else.
- `isaCombination(o ⇒ U, E, q)`: `E`'s first letter pair instantiated at `x`, `y` (β), and `q` applied as its first
  hypothesis below the letters that remain. At `U = o` the result is fol-zfc.
- `isaSymmetric`, `isaTransitive` at `o⃗ ⇒ o`: the same form, built from `E`'s with base's `iff_symm` and `iff_trans`,
  applied through `⟹`-elim, so no proof moves under a new hypothesis.
- At `o`: `isaReflexive` is base's `iff_refl`, `isaSymmetric` its `iff_symm`, `isaTransitive` its `iff_trans`.

```
Isabelle   equal_elim (symmetric (combination (reflexive Trueprop) q)) fact
read       folIffElimL(isaSymmetric(o, isaCombination(o ⇒ o, isaReflexive(λP. P), q)), fact)
logic      folIffElimL(⟨iff_symm at A, B⟩ applied to ⟨(ΛP Q. λh. h) at A, B⟩ applied to q, fact)
emitted    _1 = schema_inst iff_symm {A: A, B: B}
           _2 = implies_elim _1, ⟨(A ↔ B) ⟹ (A ↔ B) by its hypothesis, applied to q⟩
           _3 = iff_elim_l _2, fact
```

**Base, cited by its own text** (point 6 of "The unit and its citations"): this step is the first to cite base, so it
builds point 6. FolDialect parses a base schema from its line, so `schema cong_and [A(0), A2(0), B(0), B2(0)]: …` becomes
`⋀A A2 B B2::o. …`, the letters' own binders. `Cited.base(name)` cites it at no type arguments: fol-zfc's, and linked to
no statement of the unit, since base is checked on its own. Its letters are instantiated by `folSchemaInst`. The parser
reads letters of arity 0 only: a predicate letter (`cong_forall`'s `P(1)`) has no binder in the table, and the step that
first cites one gives it one.

**Expand: a definition's citation becomes `isaReflexive` at its definiens**, under a `⋀`-intro per parameter for Pure's
applied form. `Definition.reflexive`, `Pure.reflexive` read at the equation's type, goes.

**Logic's rows after this step:**

| pattern | answer |
|---|---|
| `use(axiom a, [], o)`, IFOL's and FOL's 11 propositional instances; `isaAllElim(o, o)` | rule, unchanged |
| `isaReflexive(T)`, `isaSymmetric(T, o)`, `isaTransitive(T, o, o)`, `T` = `o` or `o⃗ ⇒ o` | rule |
| `isaCombination(o ⇒ U, o, o)`, `U` = `o` or `o⃗ ⇒ o` | rule |
| `isaAbs` at a function of propositions | rule: the context its `reflexive` step consumes, never translated at its own node |
| the same at `i`, at a function of sets or of classes; `isaAbstract`; a `λ` over classes; any other axiom of the logic | unbuilt |
| `isaConst(primitive Pure.eq, …)` at a function type | unbuilt, unchanged. At an object function type pointwise ("The meta level, lowered"); beyond objects no rule translates a stated one, yet Logic owns it: a definition's citation carries one in its statement, which Expand replaces, and only an owner refuses after Expand |
| a binder or an instance beyond objects other than `o` | unbuilt, unchanged |

**Unbuilt, for the next step: equality at objects.** At `i` and at an object function type `≡` is first-order, and
Pure's rules there are theorems base proves from NBG ("The meta level, lowered"): at `i`, `eq_refl`, `eq_symm` and
`eq_trans`; at a function type, `↔` reasoning under `∀t r`, and `combination` is `mfun_comb`, then β as proof. IFOL's
`refl` at `[i]` is `eq_refl`, and its `subst` is membership's congruence at the λ's class, then β as proof. Each is
stated over variables, so a rule citing one needs its sides named, `f(a)` as `r`, in the walk that translates it:
"Reify called from Logic's walk", above, which this step does not need. Beyond objects, at a function of classes, a hole
needs a constant's argument congruence, Reify's lemma per constant. IFOL's quantifier rules at `[i]` (`allI`, `spec`,
`exI`, `exE`) are the kernel's steps, and `eq_reflection` the identity, as the reference had them. The 142 of the 558
that hold no congruence of propositions stay.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | Pure's equality rules as steps, their partial applications η-expanded | an export of one build |
| FolDialect | a base schema parsed from its text, at the letters' binders | base's files |
| Expand | a definition's citation as `isaReflexive` at its definiens | the definitions it is handed |
| Logic | every Pure step at `o` and at a function of propositions as base's schemas and fol-zfc steps; a proof of an equation between functions of propositions in the congruence form, always consumed in the same walk | the reader's row; Expand's; base's `iff_*` and `cong_*` |

**Tests, written first.**
- `ProofReaderTests`: `combination`, `reflexive`, `symmetric`, `transitive`, `abstract_rule` read as their steps;
  `equal_intr` and `equal_elim` as `iff_intro` and `iff_elim_l`; an `equal_elim` lacking its last premise η-expanded.
- `TableTests`: each step concludes by the reading of `≡`, at `o`, at `i` and at a function type; `isaCombination`
  β-reduces.
- `ParseTests` (FolDialect): `cong_and`'s line parses to its letters' binders; a malformed line is refused.
- `LogicTests`: the `Trueprop` identity, so that `equal_elim (symmetric (combination (reflexive Trueprop) q)) fact`
  concludes as Isabelle's; a section of `∧` taking two equations, through `cong_and`; `symmetric` and `transitive` at
  `o ⇒ o`; a hole under a `⋀` at `o`, its letters left off their spine; a hole under a constant, `LogicError.context`.
- `ExpandTests`: a definition's citation is `isaReflexive` at its definiens, and Pure's applied form the same under its
  parameters' `⋀`-intros.
- `PlanTests`: the rows above. `PipelineTests`: a base citation is linked to no statement.

**Kept from the reference, and changed** (`kinds-proposal`: `Sources/Lowering/Logic.swift`,
`Sources/Walk/Congruence.swift`). Kept, the mathematics:
- `equal_intr` and `equal_elim` are the kernel's `iff_intro` and `iff_elim_l` (its `KernelRule`).
- `reflexive`, `symmetric` and `transitive` are `↔`'s at `o`, and at `i` base's `eq_refl`, `eq_symm` and `eq_trans`,
  proved from NBG. The reference proved those at `o` by hand, and reached `symmetric` and `transitive` at `i` through the
  congruence of `λz. z = a` and of `λz. a = z`; base's own are one citation each.
- A congruence at a context of propositions is a replacement walk (its `Replacement`): a hole is its equation, a part
  holding none `iff_refl`, a connective base's `cong_*`.
- A class hole is `abstract_rule`'s premise with the constant's argument congruence (its `ClassHoles`, `c_ARG_CONG`); an
  argument whose equation has one node for both sides is substituted, not a hole (its `headCongruence`), for the step
  that builds arguments beyond `o`.

Changed, the code:
- No walk down a chain of `⟹`-eliminations from a conclusion at a base type (`application`, `evaluate`): a shape (D1).
  Pure's rules are steps whose premises are their children, each translated where it stands.
- No `isaCongruence` node carried across a pass for Reify to expand: the congruence is Logic's, built in its walk, and
  where it meets a term Reify names the term in the same walk ("Reify called from Logic's walk").
- Base is cited by its own text, parsed, never by `Base.claims` built by hand.
- No `LogicRefusal.functionEquality`: a stated equation between functions is Logic's, unbuilt; one between object
  functions is pointwise.

**Built.**
- Reader: Pure's seven rules are read as steps, each taking as many premises as the rule has, never as its instance's
  statement peels (`equal_elim` at `B := C ⟹ D` takes two), and each checked against the rule's statement at its
  instances, by ID. `equal_intr` and `equal_elim` are `iff_intro` and `iff_elim_l`; a rule missing premises is its
  closed proof applied to those it has.
- IR: `isaReflexive`, `isaSymmetric`, `isaTransitive`, `isaCombination`, `isaAbstract`, their conclusions by
  `Table.equation`, the reading of `≡` at a type, and `sides(ofEquation:)`, its inverse; `iff_intro` and `iff_elim_l`
  both dialects; `Cited.base`, linked to no statement. `Axiom.pure` and `Definition.reflexive` are gone.
- FolDialect: `parse(schema:in:)` reads a schema of letters of arity 0 over the connectives; `parse(schemas:from:in:)`
  finds base's lines by name; `baseTexts` reads base's files.
- Lowering: `Base`, the schemas Logic cites as a typed enum, `BaseSchema`; `plan(_:)` and `pipeline(_:)` take it.
  Logic's equality rules at `o` and at a function of propositions; Expand's citation of a definition the `reflexive`
  step.
- CLI: `lower` parses base's schemas into the unit's table before the pipeline runs.

**Measured** (`isa2fol lower data/zf_export`): 55 named theorems lowered to fol-zfc, 3 before, and 27 theorems cited
outside; refused at no owner 7,176, logic 2,188; 1 cites a refused statement (`FOL.disj_mono`). `IFOL.TrueI` and the 51
citing it lower. The table holds 6.55M nodes, 7.22M before; read 70.5 s, lowered 13.9 s. `isa2fol read` proves all
9,420. `SOURCE_SURFACE.md` and `CLOSURE.md` are regenerated: Pure's rules are steps there, no axioms.

### Reify — S1 at the site  **[AGREED 2026-10-14 (user), decision by decision: the scope, the `@def`, `Rule.after`, the guard with no arity; EX and UNIQ per term, UNIQ in chain form, 2026-10-15 (user), on review of the build; BUILT 2026-10-14 — `Sources/Lowering/Reify.swift`, `Instance.swift`, `Chain.swift`, `Tuple.swift`, `Scope.swift`, `Logic.swift`, `Fol.swift`, `Sources/IR/Pass.swift`, `Node.swift`, `Table.swift`, `base/tiers/metafun`, `inf`, `zf`]**

**Reify's provisions as their consumers see them** ("Reify and Typing as one component"): a term named where it stands
(S1), a constant's class and its `@def`, EX and UNIQ as the lemmas every use cites, the guard per type. Their provers —
class existence per formula (FOUNDATION §3, R5) — are the next step: consumers cite the lemmas now and the registry
refuses them until then (I2, D2). Three facts fix the scope:
- **Every constant beyond the primitives reaches a λ.** `Upair ≡ Replace(Pow(Pow(0)), λx y. …)`, and `cons`, `succ`,
  `Pair`, `∪` rest on `Upair`; `⊆` is `Ball(A, λx. x ∈ B)`. No constant's class is stated unless a λ in a class slot is
  named, so this step names it (FOUNDATION S1, "a λ is a wrapper"). An instance at a class type stays Lambda's.
- **An instance at a compound term has the pattern of an instance at a variable**, `isaAllElim(o, i)`. It cannot stay
  unbuilt while terms are named at atoms, so this step builds it, citing EX and UNIQ.
- **The surface is the reason, the survey only the order** (a scratch survey of the 2,188 refused at logic, not kept):
  1,894 hold Reify's pieces and no row of Logic's; 1,132 hold only constants applied to sets, `mem` and `eq`, and of these
  3 hold primitives alone. 421 of the 1,894 instantiate at a compound term.

**The problem, in target text.** The signature has no function symbols: a term becomes a variable at its atom, and an
instance at a term has no variable to instantiate at.

```
Isabelle   x ∈ succ(y)
fol-zfc    ∃S. ZF_Base.succ(S) ∧ ∃t. set(t) ∧ (⟨y⟩ = t ∧ ∃r. set(r) ∧ (pmem(t, r, S) ∧ elem(x, r)))
@def       ZF_Base.succ(S) ↔ ∀t. set(t) → ∀r. set(r) → (pmem(t, r, S) ↔ ∃i. set(i) ∧ (⟨i⟩ = t ∧ ⟦r = cons(i, i)⟧))

Isabelle   p ⊢ ⋀x. x ∈ A ⟹ x ∈ B,  p at succ(a)       ⊢ succ(a) ∈ A ⟹ succ(a) ∈ B
wanted     ⟦succ(a) ∈ A⟧ → ⟦succ(a) ∈ B⟧               each atom naming succ(a) itself
proof      EX ⟨succ(x)⟩ at a: ∃y. set(y) ∧ ⟦y = succ(a)⟧; ∃-elim y; p at y ⊢ y ∈ A → y ∈ B;
           y ∈ A ↔ ⟦succ(a) ∈ A⟧ — → by EX's naming, ← by UNIQ ⟨succ(x)⟩ — and at B the same; joined by cong_imp
```

`⟨y⟩ = t` is Tuple's formula, `∃e. set(e) ∧ (zero(e) ∧ snoc(e, e, y, t))`: a 1-tuple at arity 1 (decision 1).

**1. A term is named where it stands** (FOUNDATION S1; decision 3; decision 5 as the user refined it on the reference,
2026-09-30: "a constant is named where it appears, like any term"). One rule per piece:

| piece | named where it stands |
|---|---|
| `mem(a, b)` · `IFOL.eq(a, b)` at `i` | `elem(a, b)` · `eq(a, b)` |
| a predicate constant applied, `c(a⃗, P⃗)` | `∃C. c(C, P⃗) ∧ ∃t. ⟨a⃗⟩ = t ∧ elem(t, C)` |
| a predicate variable applied, `P(a⃗)` | `∃t. ⟨a⃗⟩ = t ∧ elem(t, P)` |
| a set constant `c` | `∃v. c(v) ∧ …v…` |
| a function constant applied, `c(a⃗, P⃗)` | `∃C. c(C, P⃗) ∧ ∃t. ⟨a⃗⟩ = t ∧ ∃r. pmem(t, r, C) ∧ …r…` |
| a function variable applied, `f(a⃗)` | `∃t. ⟨a⃗⟩ = t ∧ ∃r. apply(t, r, f) ∧ …r…` (5) |
| a λ in a class slot, `λx⃗. φ` · `λx⃗. b` | `∃K. (∀t. elem(t, K) ↔ ∃x⃗. ⟨x⃗⟩ = t ∧ ⟦φ⟧) ∧ …K…` · `∃K. (∀t r. pmem(t, r, K) ↔ ∃x⃗. ⟨x⃗⟩ = t ∧ ⟦r = b⟧) ∧ …K…` |

`a⃗` are the set arguments, each named first, left to right; `P⃗` the class arguments, named next and kept outside the
tuple (R4). `c(C, …)` is `c`'s `@def` predicate under Isabelle's name (rule 5); a ZF primitive's is base's. The table
elides the set guards, which Fol writes (R3).
- **A term is named at the node holding it, never at its own**: the walk reaches it first and leaves it. That node is
  Reify's own piece (an atom, a term, a class slot), or an instance at `i` (3).
- **A value, a tuple and its indices are sets**: Reify binds them by isa binders at `i`, and Fol guards them (R3, "the
  ones S1 invents"). **A class Reify names, a constant's or a λ's, is bound by fol-zfc's own `∃`, bare**: it translates
  no Isabelle variable, and a guard on it is false or redundant.
- ⚠ **ONE VARIABLE PER OCCURRENCE, NEVER PER DISTINCT TERM** (the reference's): shared per term, instantiating
  `⋀y. f(y) ∈ f(x)` at `x` makes the instance of the translation differ from the translation of the instance.

**2. A constant's class: its `@def`** (decision 5: `@def` is the checker's one global naming form).

```
a function     ∀C P⃗. c(C, P⃗) ↔ ∀t. set(t) → ∀r. set(r) → (pmem(t, r, C) ↔ ∃x⃗. set(x⃗) ∧ (⟨x⃗⟩ = t ∧ ⟦r = b⟧))
a predicate    ∀C P⃗. c(C, P⃗) ↔ ∀t. set(t) → (elem(t, C) ↔ ∃x⃗. set(x⃗) ∧ (⟨x⃗⟩ = t ∧ ⟦φ⟧))
a set          ∀v. c(v) ↔ ⟦v = b⟧
```

Reify states it from `c`'s definition as Expand left it ("The unit and its citations", point 1), its body named by the
rules of 1: one translation wherever a formula stands. Its own variables are the target's `∀`, unguarded: they translate
no Isabelle variable. It is named as Reify's lemmas are, by the constant and a suffix the export never uses,
`ZF_Base.succ_DEF`. Isabelle's definition axiom cannot name it: 346 of the 999 are a package's, registered as a theorem
of the same name too (the reference's ⚠). A body uses only earlier constants (S3), so `@def`s nest without a cycle.

**What the framework gains** — each a change to agree:
- **`folPred`'s predicate is typed** (I1: it crosses Reify, the pipeline and FolDialect). `Predicate.base(String)` is
  one of base's own (`set`, `elem`, `eq`, `pmem`, `zero`, `nsucc`, `snoc`, …); `Predicate.constant(Constant)` is a
  constant's class. A primitive's class is base's (`base/tiers/zf`) and linked to no statement; a defined constant's is
  its `@def`, a statement of the unit.
- **The registry states a `@def`** ("a `@def` as a prover's answer", "The unit and its citations"). After logic, for
  each defined constant an output names and the unit lacks, the prover owning it answers its statement, or unbuilt.
  That prover is Reify's, reading the definition as Expand left it. The `@def` joins the unit as a definition: it has no
  proof and is never proved. The pipeline checks it as a lemma's statement (no pattern a pass up to the registry owns)
  and checks its shape: `∀v⃗. c(v⃗) ↔ body`, `c` absent from the body (R1, which the checker does not check). Its
  body names earlier constants, whose `@def`s are stated in turn until none is new.
- **A statement naming a constant is linked to its `@def` as to a citation**: one the prover leaves unbuilt refuses every
  statement naming the constant, transitively. A `@def`'s own left side is no link.
- **`Rule.after` receives the node as it stood**, beside the node rebuilt from its rewritten children:
  `after(_ n: Node, was id: NodeID, context:, in:)`, the `id` the traversal holds where it calls `after`. An instance
  reads Isabelle's formula there and never reads a named form back (I1). Point 4 of "Reify called from Logic's walk" left
  this reading to the step that needs it; its consumers are Reify's instance here and Logic's equality steps at objects
  next. Every other rule ignores it.

**3. An instance at a compound term** (FOUNDATION §3b's `appt_complex`). Isabelle instantiates `p ⊢ ⋀x. φ(x)` at `t`, and
the step after it expects `⟦φ(t)⟧`, with `t` named at each atom.
- **EX of `t`** (4), at `t`'s variables, gives `y` with `⟦y = t⟧`.
- **`∃`-elim `y`**; `p` at `y` concludes `⟦φ(y)⟧`, an instance at a variable: Fol's.
- **`⟦φ(y)⟧ ↔ ⟦φ(t)⟧` by replacement of equivalents over Isabelle's `φ`**: Logic's walk, its `Context` today, made the
  one home for it, with holes the caller gives (⚠ REIFY NEVER HANDLES A CONGRUENCE). A hole is an atom where `x` stood:
  `α(y) ↔ ⟦α(t)⟧`, `→` by EX's naming, `←` by UNIQ of `t` (4), and membership's congruence at the atom (base's
  `cong_elem_*`, `cong_eq_*`, `cong_snoc_v`). Where `x` stands inside a λ argument, the λ's definition is walked the
  same way and its class is kept.

**4. EX and UNIQ per term: its value and the value's uniqueness** (user, 2026-10-15, over per constant): built from
the term alone (I2), `a` closed over its variables `v⃗` in the order they first occur, so `succ(succ(a))` and
`succ(succ(b))` share one pair. EX is Isabelle's statement named by 1; UNIQ is in chain form (user, 2026-10-15, over
Isabelle's `⋀v⃗ y y′. y = a ⟹ y′ = a ⟹ y = y′`): two namings of `a`, their binders `b⃗`, `b⃗′` the lemma's variables
and their constraints `c⃗`, `c⃗′` its premises, concluding that their values `r`, `r′` are equal.

```
EX ⟨a⟩     ∀v⃗. ∃y. ⟦y = a⟧                                a set constant c: ∃y. ⟦y = c⟧
UNIQ ⟨a⟩   ∀v⃗. ∀b⃗. c⃗ → ∀b⃗′. c⃗′ → eq(r, r′)
```

⚠ **EVERY CONSUMER OF UNIQ HOLDS BOTH NAMINGS OPEN** — the instance (3) and UNIQ's prover at an inner term — and the
chain form takes them as they stand. Isabelle's form would make each consumer rebuild a naming around its own value,
which `exists_intro` cannot do directly: it abstracts every occurrence of its witness (fol-zfc's `translate_term`, the
IR's `isaExIntro`), so `⟦r′ = a⟧` closed at `r′` concludes `eq(r, r)`; only a detour through a fresh variable equal to
`r′` reaches it.

Each assumes the guard of each of `v⃗` (5). At `c(x⃗)` they are the constant's own typing and its value's uniqueness,
the two facts base's `apply_EX` and `apply_UNIQ` give a function variable (5). Their prover walks `a` inner first,
citing each head's facts at its arguments' values — a constant's at `c(x⃗)`, proved by the same walk over its
definition's body ("The unit and its citations", point 4); `apply_EX` and `apply_UNIQ` at a function variable; for a λ
argument its class, Lambda's lemma, closed over the λ's free variables (user, 2026-10-14): `∀v⃗. ∃K. def(K)`, cited at
the variables the λ mentions, where it concludes the λ's naming in its class slot by ID. UNIQ's two namings name each λ
argument by its own class, and the two agree by their definitions. So one walk proves a term's facts, once however many
instances cite them, and no instance walks a term: the reference's `lambda_<fp>_typing` for a λ's body, made
systematic (proved at every use, `Acc.acc_FUNC` held five copies of one 8.1k-step proof). They are Reify's requests,
named `EX_` and `UNIQ_` and a 64-bit FNV-1a fingerprint of the closed term (`Table.fingerprint`): a fol-zfc name cannot
spell a term and rule 5 forbids mangling, and Swift's `Hasher` is seeded per process while a name must be the same
every run. Two terms sharing a fingerprint stop the run (`duplicateName`). The price is that a name, and a refusal,
says nothing of its term. The prover is the next step, so the registry refuses them and their citers fall. A
predicate's application is no term and needs neither.

**5. The guard per type: one atom, with lemmas on it** (user, 2026-10-14: the guard is an atom chosen by the type, base's
lemmas on it keep its uses short, and it carries no arity — a function is its pairs).

| type | its guard | discharged at an instance |
|---|---|---|
| `i` | `set(x)` | at a variable, its binder's hypothesis (Fol); at a compound term, EX's `∃y. set(y) ∧ …` |
| `iⁿ ⇒ o` | none | — |
| `iⁿ ⇒ i` | `function(F)`: `F` single-valued, Isabelle/ZF's `function` of a class | at a variable, its binder's hypothesis (Fol); at a λ, Lambda's |

**A function variable's application is read as Isabelle/ZF reads `f`a ≡ ⋃(f``{a})`**: its value where `F` has one, `∅`
where it has none. Base defines it, so totality leaves the guard and the guard needs no arity:

```
function(F)    ↔ ∀t r s. pmem(t, r, F) → pmem(t, s, F) → eq(r, s)
apply(t, r, F) ↔ pmem(t, r, F) ∨ (¬(∃s. pmem(t, s, F)) ∧ zero(r))
apply_EX       ∀F t. ∃r. set(r) ∧ apply(t, r, F)                                       a value, with no guard
apply_UNIQ     ∀F. function(F) → ∀t r s. apply(t, r, F) → apply(t, s, F) → eq(r, s)     and only one
```

Base proves the two lemmas once, for every arity. They state of a variable what EX and UNIQ of `c(x⃗)` state of a
constant: EX's prover cites them at `f(a⃗)` where it cites `c`'s at `c(a⃗)`. A constant's application stays `pmem`, since a
constant is total by its definition; at an instance of `∀F` at a λ (Lambda's step) the λ's class is total, and one base
lemma reads `apply` as `pmem` there. Faithful (N2): every single-valued `F`, read through `apply`, is a total function
on sets, and every Isabelle function is such an `F`.

⚠ **`function` REPLACES `mfun` AT `iⁿ ⇒ i`** ("Reify and Typing as one component"). `mfun(F, D)`, like the reference's
`Func(F, n)`, promises totality, so it needs the domain at every binder: a class `D` of the n-tuples, or the numeral `n`.
The reference's binder guard (`functionVariableGuard`) wrote its two clauses out instead, over the arguments.

Fol gains its rows: a binder, an intro and a variable at `iⁿ ⇒ o` (bare) and at `iⁿ ⇒ i` (with Reify's guard); an
`∃`-intro and an `∃`-elim at an isa binder at `i`, which Reify's proofs write. The witness's guard goes into the `∧`, and
the hypothesis becomes `set(y) ∧ φ` (prerequisite 1's open item). An instance at a class type moves from Fol to the logic
pass, where it is Lambda's and unbuilt; its argument is always a λ.

**Owned, unbuilt — each its own step:** an instance at a class type (Lambda: the λ's class and β as proof); a proposition
in a class slot (`If`'s) and a constant at `o` (FOUNDATION S4's class of the empty tuple, the reference's paragraph); a
declared constant (no definition, so no `@def`); the provers of EX and UNIQ, and of the λ's class and guard (class
existence per formula, R5's opening, R4's lift).

**FOUNDATION first.** This step rests on two of the reference's paragraphs, from the open docs commit: S1's "a λ is a
wrapper" (the stash's text, 2026-10-13), and S5 changed: a function variable owes single-valuedness, its application
read as Isabelle/ZF's `f`a`. From base it
needs the reference's `zf` tier (the primitives' class predicates `ZF_Base.zero`, `Pow`, `Union`, `PrimReplace` and
`Inf`), the `inf` tier `zf` rests on, which replaces `skolem`'s admitted `Inf`, and `tuples`' `cong_snoc_v`; and new,
`function`, `apply`, `apply_EX` and `apply_UNIQ`.

**The agreed text changes with it.** "Lowering's components": Reify's row and Lambda's (a λ in a class slot is named
here); Logic's replacement walk, which Reify calls; the owner table (an instance at a class type goes to the logic
pass). "Reify and Typing as one component": `function` at `iⁿ ⇒ i`, and `apply`. "The unit and its citations": a `@def` cited by a
predicate. "The meta level, lowered": decision 5. "Fol": its rows. §4.5: `Rule.after`. `CLAUDE.md`.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reify | every term named where it stands; each constant's `@def`; EX and UNIQ requests built from the term; an instance at a compound term concluding Isabelle's formula named, by ID; the guard per type | Expand's row; Tuple's formula; base's predicates for the primitives, `function` and `apply` with their lemmas; Logic's replacement walk; its requests proved by its prover or refused there |
| Logic | replacement of equivalents over a formula, its holes the caller's | — |
| Fol | binders, intros and variables at every object type, with the guard Reify gives; `∃` at `i`, guarded | Reify's guards |
| the pipeline | each named defined constant's `@def`, stated by the registry after logic and linked to every statement naming it | a typed predicate; the registry's `define` |

**Tests, written first.**
- `ReifyTests`: each row of 1 named where it stands, by ID; one term twice is two variables; naming commutes with an
  instance at a variable, by ID; a constant's `@def` from its definition, a set constant's, a class argument as a
  parameter.
- `ReifyTests`: an instance at `succ(0)` concludes Isabelle's formula named, by ID, citing EX and UNIQ of `succ(0)`;
  one at an applied function variable cites the term's, closed over the variable, discharging its guard; one with `x` inside a λ argument keeps
  the λ's class.
- `PipelineTests`: a statement naming a constant is linked to its `@def`; a `@def` that cannot be stated refuses its
  users; a `@def` of the wrong shape stops the run; a `@def` naming itself is no cycle.
- `FolTests`: a binder at `i ⇒ o` is bare and one at `i ⇒ i` guarded; `∃`-intro and `∃`-elim at `i` are guarded.
- `PlanTests`: Reify's rows; an instance at a class type is the logic pass's, unbuilt; a constant at `o` or with an `o`
  slot, and a declared constant, are unbuilt.
- `TraversalTests`: `after` sees the node as it stood. `LogicTests`: the replacement walk with a caller's holes, and
  Logic's own uses unchanged.

**Kept from the reference, and changed** (`kinds-proposal`: `Sources/Encoding/Spelling.swift`,
`Sources/Lowering/Reify.swift`, `Value.swift`; DESIGN "Reify — first cut", "The constant chain's `@def`s", decisions
5–7). Kept: a constant named where it appears, by its `@def` predicate; one variable per occurrence; the spelling
(`Chain`: arguments, class, tuple, value); a set constant as a predicate of its value; class arguments as the `@def`'s
parameters; an instance at a term by EX, `∃`-elim and UNIQ; the primitives' classes in base. Changed:
- A function variable owes single-valuedness alone, and its application reads Isabelle/ZF's `f`a`: the reference's guard
  promised totality (`Func(F, n)`, its two clauses written out from 2026-10-04).
- The `@def` is `c_DEF`, not named by Isabelle's axiom, which a package also gives a theorem.
- No `IRType.cls` and no `sorts` pass: a class Reify names is fol-zfc's own binder (the root of "One class, one form").
- No guard pass opening terms, no `isaCongruence` node, no value walk of Reify's own: the instance is Reify's rule where
  the term stands, and the lifting is Logic's walk.
- No driver adding `@def`s (`constantsToDefine`): the pipeline adds one where a predicate first names it, and a refusal
  reaches the users.
- Two lemmas per term an instance meets, built from the term and named by 1, where the reference cited five per
  constant (`c_EX`, `c_UNIQ`, `c_FUNC`, `c_typing`, `c_value_UNIQ`), opening a term one constant at a time at every
  use, and only a λ's body's per term (`lambda_<fp>_typing`).
- A λ in a class slot is named at its site by its definition (the stash's wrapper), never as a constant `L` (Step (4)).

**Built.** Reify's switch gives its pieces rules: a ZF primitive, a ZF definition at the object level of a type whose
slots are objects and whose value is a set or, given an argument, a proposition; an applied variable of an object head;
a λ at an object type. A constant at `o`, a proposition slot (`If`'s) and a declared constant stay unbuilt, and so does
an instance at a class type, now the logic pass's. The logic pass's walk asks Reify at every node Logic's switch
leaves: an atom is named where it stands (`Naming`: one `Chain` per atom, set binders isa `∃` at `i`, classes
fol-zfc's own), and an instance at a compound term is `TermInstance`'s proof. `ReifyProver` states each `@def` from the
definition Expand left; the pipeline asks it after logic for each defined constant a statement names, and links them.
Fol writes every binder, intro and variable at an object type with the guard `Reify.guarded` gives it; its context
holds, for each entry of its output, a variable with its isa type, an assumption, or a hypothesis Fol inserted (a
guard, or the `∧` an `∃` at `i` opens to). Base's `function`, `apply`, `apply_EX`, `apply_UNIQ`, `cong_snoc_v` and the
reference's `inf` and `zf` tiers are kernel-checked (`scripts/check-base.sh`); `skolem` is gone.

**Refinements made in the build** (no checker change; delegated, for review):
- **A lemma's variables** are `∀ᵢ` at `i`, which Fol guards, and fol-zfc's `∀` at a class type, the variable a typed isa
  one and a function variable's guard written out ("EX and UNIQ — their prover", 4, changed from fol-zfc's `∀` at every
  type, under which a prover could not close an isa `∃` at its own variable). A use eliminates a set variable by an
  instance, a class variable by `forall_elim`, its guard by `isaGuard`, which Fol resolves to the variable's own. An isa
  `⋀` at a class type could not be eliminated at a variable: the table admits only a λ there.
- **`∃` at an isa binder is a step of its own, `isaExIntro` and `isaExElim`** (IR nodes, isa only, Fol's at `i`). The
  fol-zfc steps bind fol-zfc's `∃` only: `Pattern` cannot tell an isa `∃` at `i` from fol-zfc's, and Fol dispatches
  by `Pattern` (I3). IFOL's `exI` and `exE` are these steps when Logic builds them.
- **The conversion** `⟦φ(y)⟧ ↔ ⟦φ(a)⟧` is Logic's replacement walk (`Replacement`, its `Context` made one home, with
  quantifiers at `i` and a hole the caller gives) over Isabelle's `φ`. At an atom where `x` stood it converts one unit
  at a time: `x` itself, or a λ argument holding it. For `x` itself, each side's chain is opened and the other closed at
  the same witnesses (`Scope`, `opening`, `closing`; a `Chain` opened names at given variables): `→` with `⟦y = a⟧`'s
  witnesses in the unit's place, `←` with UNIQ, `eq_trans` and `eq_symm`; the one constraint where `y` and `a`'s value
  meet is converted by membership's congruence (`cong_elem_*`, `cong_eq_*`, `cong_snoc_v`), the same walk with the
  differing atom as its hole. For a λ, its class is kept and its definition converted by the walk over the definition
  with Isabelle's body. The λ's lemma is EX's prover's: the instance cites none.
- **A `@def` whose definition holds a pattern no pass owns, or one a pass up to the registry leaves unbuilt, is refused
  before the registry is asked**, read from the definition's body under its parameters: an abstraction over a class
  parameter is the `@def`'s own variable, no λ of its body. The pipeline checks a `@def`'s shape by its arguments'
  indices, a class parameter staying a typed isa variable until Fol.

**Measured** (`isa2fol lower data/zf_export`): 59 lowered; 451 `@def`s stated and 107 refused, of which 22 hold a
piece not built (12 `If`'s proposition slot, 9 a declared constant) and 85 cite one of them; 400 lemma requests, EX and
UNIQ, refused as their prover is the next step's. Of the named, refused where each first stops: no owner 7,176; logic
924 (`isaAllElim(o, (i => i))` 458, Lambda's instance at a class type, the most frequent); a letter off its spine 94;
1,167 cite a refused statement, a `@def` or a lemma. No statement stops at Fol. Read 70.5 s, lowered 25.5 s.

### EX and UNIQ — their prover  **[DELEGATED 2026-10-15 (user: "go autonomous on this feature"); BUILT 2026-10-15, its decisions reviewed by the user — `Sources/Lowering/Terms.swift`, `Graph.swift`, `Facts.swift`, `Tuple.swift`, `Congruence.swift`, `Scope.swift`, `Reify.swift`, `Logic.swift`, `Sources/IR/Index.swift`, `Pass.swift`, `Constant.swift`, `Pattern.swift`, `Sources/FolDialect/Parse.swift`, `Render.swift`, `base/tiers/tuples`, `metafun`]**

**The step.** Reify's requests EX ⟨a⟩ and UNIQ ⟨a⟩ ("Reify — S1 at the site", point 4) get their prover. A term's naming is
a chain of binders, each standing for one piece of the term, and the prover walks it: **one fact per piece, for EX its
witness, for UNIQ its agreement across two namings** (D1). The class a function constant or a λ names exists by class
existence per formula (FOUNDATION §3, R5's opening, R4's lift): that is the next step, so its facts are cited here and
refused at their prover (D2) — EX of a term holding a function constant or a λ falls there, and UNIQ does not need it.

**1. The pieces of a naming, and their facts.** `∀ᵢ`, `∃ᵢ` are isa binders at `i`, which Fol guards; `∀`, `∃` fol-zfc's,
bare, over classes. `P⃗` are a constant's class parameters, `x⃗` its set arguments, `≈` agreement of two classes on their
tuples (`∀ᵢt. elem(t,K) ↔ elem(t,K′)` at a predicate, `∀ᵢt r. pmem(t,r,K) ↔ pmem(t,r,K′)` at a function).

| binder, its constraint | EX: a witness | UNIQ: two namings agree |
|---|---|---|
| `v`: `c(v)`, a set constant | `c_EX: ∃ᵢv. c(v)` | `c_UNIQ: ∀ᵢv w. c(v) → c(w) → eq(v,w)` |
| `C`: `c(C, K⃗)` | `c_CLASS: ∀P⃗. ∃C. c(C,P⃗)` (next step) | `c_AGREE: ∀P⃗ P⃗′. P⃗ ≈ P⃗′ → ∀C C′. c(C,P⃗) → c(C′,P⃗′) → C ≈ C′` |
| `K`: a λ's definition | `CLASS_⟨λ⟩: ∀v⃗. ∃K. def(K)` (next step) | the two definitions are one formula |
| `τ`: `⟨x⃗⟩ = τ` | `TUPLE_EX_n: ∀ᵢx⃗. ∃ᵢτ. ⟨x⃗⟩ = τ` | `TUPLE_UNIQ_n: ∀ᵢx⃗ x⃗′. eq(x⃗,x⃗′) → ∀ᵢτ τ′. ⟨x⃗⟩ = τ → ⟨x⃗′⟩ = τ′ → eq(τ,τ′)` |
| `r`: `pmem(τ, r, C)` | `c_TOTAL: ∀C P⃗. c(C,P⃗) → ∀ᵢx⃗ τ. ⟨x⃗⟩ = τ → ∃ᵢr. pmem(τ,r,C)` | `c_FUNC: ∀C P⃗. function(P_f) → c(C,P⃗) → function(C)`, and base's `func_at` |
| `r`: `apply(τ, r, f)` | base's `apply_EX` | base's `apply_at`, under `f`'s guard |

At a set constant or a function constant the facts are per constant, named by it and a suffix the export never uses (a
clash stops the run, `duplicateName`); a primitive's are base's where base has them (`ZF_Base.zero_EX`, `Inf_UNIQ`, …).
At a λ they are per closed λ, named by its fingerprint; at a tuple, per arity. `FUNC_⟨λ⟩: ∀v⃗. ∀K. def(K) →
function(K)` is a function λ's guard, which `c_FUNC` owes at a λ in a function slot.

**2. EX ⟨a⟩ and UNIQ ⟨a⟩ walk the chain.** EX opens each binder's witness in order, by its fact at the refs its
constraint names, then closes `⟦z = a⟧` at the witnesses for a fresh `z` with `eq(z, r)` and instantiates `z` at the value
`r` (⚠ "Reify — S1 at the site", point 4: a naming is never closed around its own value). UNIQ fixes both namings and
derives each binder's agreement from the earlier ones; the last is `eq(r, r′)`. Neither reads a constraint back (I1):
the naming records, for each binder, the piece it stands for.

**3. A class given by a graph definition is total and single-valued — one rule, for a constant and a λ.** A function
constant's `@def` and a function λ's definition are one shape, `∀ᵢt r. pmem(t,r,K) ↔ ∃ᵢx⃗. ⟨x⃗⟩ = t ∧ member(x⃗, r)`:
- **total**: the tuple's entries are `x⃗` themselves, and `member` has a value there;
- **single-valued**: two values at one `t` come from entries equal by the tuple's injectivity (`TUPLE_INJ_n`), the second
  member moved to the first's entries by membership's congruence, then `member`'s uniqueness.
`member` is a defined constant's `⟦r = b⟧` — its value by EX ⟨b⟩, its uniqueness by UNIQ ⟨b⟩, its congruence the
replacement walk at atoms (`cong_elem_*`, `cong_eq_*`, `cong_snoc_v`) — or a primitive's base relation: `Pow`, `Union` by
their `_EX`, `_UNIQ`, `_CONG`; `PrimReplace`'s by extensionality and `zero_UNIQ` in its two branches, its value the next
step's (its image is a class of Kuratowski pairs, built by class existence). `c_AGREE` is the replacement walk over the
definition at the atoms on `P⃗`. A defined set constant's `c_EX` and `c_UNIQ` are its `@def` with EX ⟨b⟩ and UNIQ ⟨b⟩.

**4. What the framework gains** — each for review:
- **Base's guarded quantifiers parse as set binders.** `forall x. (set(x) -> φ)` is `∀ᵢx. φ` and `exists x. (set(x) &
  φ)` is `∃ᵢx. φ`, `x` a variable at `i`; Fol writes the guard back, so a parsed claim lowered by Fol is its text. Base
  and lowering then name a set variable alike: parsed as fol-zfc's, a base existential's witness never met a naming's
  constraint by ID before Fol, nor could Fol discharge its guard.
- **A lemma's set variables are `∀ᵢ`** ("Reify — S1 at the site", refinement "A lemma's variables", changed): Fol
  guards them, so a prover's proof closes an isa `∃` at its own variables. Class variables stay fol-zfc's `∀`, a
  function variable's guard written out. EX assumes no function guard: an application has a value under none
  (`apply_EX`).
- **A proof cites a `@def`**: `Cited.definition(c)`, named `c_DEF`, linked to the `@def` by ID as a lemma is.
- **A lemma naming a constant whose `@def` is refused is refused before its prover is asked** (`cites(c_DEF)`): its
  prover would state facts about a body no rule names.

**5. Base gains** (kernel-checked, `scripts/check-base.sh`): in `tuples`, `nsucc_UNIQ`, `nsucc_CONG` and `snoc_res_cong`
(the reference's proofs); in `metafun`, `func_at` — a function class's values at equal tuples are equal across agreeing
classes —, `apply_at` — the same for an application under `function(F)` — and `apply_class_cong` — `apply` respects
agreement of its class.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reify's prover | EX ⟨a⟩, UNIQ ⟨a⟩; each constant's and λ's facts of 1 but `_CLASS`; the graph rule of 3 | class existence's `_CLASS` facts, stated here and refused by it until built; Tuple's facts; base |
| Tuple's prover | `TUPLE_EX_n`, `TUPLE_UNIQ_n`, `TUPLE_INJ_n` at every arity | base's `zero`, `nsucc`, `snoc` and `tuple` lemmas |
| the pipeline | a `@def` cited by ID; a lemma refused with the `@def`s it names | — |
| FolDialect | base's statements in lowering's vocabulary | — |

**Tests, written first.** `ParseTests`: a guarded quantifier parses as a set binder, and Fol gives back the text.
`TupleTests`: each tuple fact at arities 0–3, its proof concluding its statement by ID through Fol. `ReifyTests`: EX ⟨0⟩
and UNIQ ⟨0⟩ proved from base; UNIQ ⟨succ(x)⟩, and of an applied function variable, proved; EX ⟨succ(x)⟩ cites
`ZF_Base.succ_CLASS`; a constant's `_TOTAL`, `_FUNC`, `_AGREE` and a set constant's `_EX`, `_UNIQ` proved from small
definitions. `PipelineTests`: a `@def` citation links by ID; a lemma naming a refused `@def` is refused unasked.

**Built.** `TermProofs` walks a term's naming for EX and UNIQ (`Terms.swift`); `GraphProofs` proves a constant's and a λ's
facts by the graph rule, its member a defined term, `Pow`'s or `Union`'s base relation, or `PrimReplace`'s two branches
(`Graph.swift`); `TupleProver` proves the tuple's facts at every arity along its numerals (`Tuple.swift`). The naming
records each binder's piece (`NamedPiece`). Proofs are built in a `Frame`, which records each binder and wraps them at
the end; `have` cuts a derived fact into a hypothesis, which a deeper scope rebuilds from its level (⚠ the table checks
no hypothesis against its binder). Logic's replacement walk takes fol-zfc's `∃` and `∀`, and one congruence step
(`congruent`, membership's at every differing position) serves the instance and the provers. `_CLASS` and
`CLASS ⟨λ⟩` are owned and unbuilt, and so is `PrimReplace`'s `_TOTAL`: its image is a class of Kuratowski pairs, which
class existence builds. Tests: every lemma the tests prove whose citations close is checked by the real checker
(`kernelChecks`, `Tests/LoweringTests/ProofChecks.swift`), FolDialect now rendering a base schema's instance as one
`schema_inst` step; a test helper checks each hypothesis against its binder (`misscoped`).

**Measured** (`isa2fol lower data/zf_export`): 59 lowered, as before — every EX of a term holding a function constant
or a λ cites its class, class existence's; 1,122 statements of the unit beside them reach fol-zfc (478 before). Of the
lemmas refused at their prover, 225 (400 before): 117 constants' `_CLASS`, 107 λs' `CLASS ⟨λ⟩`, `PrimReplace_TOTAL`.
Proved and kept: 333 UNIQ ⟨a⟩, 105 `_AGREE`, 105 `_FUNC`, 71 `FUNC ⟨λ⟩`, 14 tuple facts, 13 set constants' `_UNIQ`,
2 `_TOTAL`, 1 EX. The named refusals are as before: no owner 7,176, logic 924, a letter off its spine 94, 1,167 citing a
refused statement. Read 70.5 s, lowered 31.4 s.

**Decisions made in the build**, reviewed by the user 2026-10-15 (no checker change):
1. **Scope.** The prover is complete against its contract; class existence's facts are cited and refused there (D2),
   so no instance at a compound term holding a function constant or a λ lowers until class existence is built.
2. **One fact per piece**, per constant (`c_EX`, `c_UNIQ`, `c_CLASS`, `c_AGREE`, `c_TOTAL`, `c_FUNC`), per closed λ
   (`CLASS_`, `FUNC_` and its fingerprint), per arity (`TUPLE_EX_n`, `TUPLE_UNIQ_n`, `TUPLE_INJ_n`); a primitive's from
   base where base has it. A constant's are named by it, readable in a refusal.
3. **One graph rule** for a function constant's `@def` and a function λ's definition, its member's facts per kind.
4. **Base's guarded quantifiers parse as set binders** (4, first bullet).
5. **A lemma's set variables are `∀ᵢ`; EX assumes no function guard** (4, second bullet; "Reify — S1 at the site",
   refinement "A lemma's variables" changed).
6. **A proof cites a `@def`**: `Cited.definition`, linked by ID.
7. **A lemma naming a refused `@def` is refused unasked.**
8. **A fol-zfc variable is untyped in an instance** (`Sources/IR/Index.swift`): it takes any term variable, and any
   variable is instantiated at it, the node substituted as it is — retyped, one variable would stand in two forms.
9. **Base gains** six lemmas, kernel-checked (5).
10. **FolDialect renders a schema instance**, its letters named as base's schema line declares them (`schemaLetters`).

### Class existence — its prover  **[AGREED 2026-10-15 (user), all nine decisions one by one; BUILT 2026-10-15, its decisions in the build reviewed by the user — `Sources/Lowering/Comprehension.swift`, `Classes.swift`, `Facts.swift`, `Graph.swift`, `Reify.swift`, `Plan.swift`, `Sources/IR/Node.swift`, `Pattern.swift`, `Table.swift`, `Index.swift`, `Legalize.swift`, `Sources/FolDialect/Parse.swift`, `Render.swift`, `base/tiers/tuples`, `classes`, `metafun`, `zf`]**

**The step.** Class existence's facts, which EX ⟨a⟩ cites and the registry refuses unbuilt today: `c_CLASS` of a
constant, `CLASS ⟨λ⟩` of a closed λ, and PrimReplace's value under its `_TOTAL` — 225 lemmas in the last run ("EX and
UNIQ — their prover", Measured). FOUNDATION §3: a formula's class is built from base's rows as a class of RECORDS —
assignments, tuples on the variables in scope — and read back exactly on them; R5: a constant's class in a body is a
parameter, its body never unfolded; R4: a class-taking constant at a λ that varies with the formula's variables has its
class built for that site.

**How the reference builds it** (`kinds-proposal`: `Sources/Classes/Comprehension.swift`, `Open.swift`, `Lift.swift`,
`Sources/Constants/Replaced.swift`, `base/tiers/classes`; its DESIGN, step 6):
- *Comprehension* builds a class of records per subformula from base's rows. An atom is read as membership of its
  entries in a witness class (`B1`'s, `cls_diag`, `cls_zero`, `cls_nsucc`, `cls_snoc4`) by one row per width (`read1`,
  `read2`, `read4`), so congruence is membership's, proved once; `∃` by `row_ex`; the class is read back exact on
  records, and two schemas (`member_class`, `graph_class`) take exactness to the class.
- *The Opener* runs first and proves the body equivalent to a class-free one: a class-free constant's binder opened by
  its class (`c_EX`) and `c_UNIQ`; a λ's class a BUNDLE, the λ closed over the walk-bound sets it mentions; a
  class-taking constant at bundles by `c_lift_p`, one lemma per constant AND context size `p`; bundles of different
  contexts WIDENED to their union; a dry pass lays out the classes before the real pass proves.
- PrimReplace's value is hand-coded (`Replaced.swift`): Replacement at the class of Kuratowski pairs built from `P`.
- Measured there: EX and UNIQ for 223 constants; a per-arity tuple row cut the steps by 47%.

**1. One construction: a formula's class of records, then its section.** Every class this step names is one
formula's: `CLASS ⟨λ⟩` the λ's definition at its free variables, a function or predicate constant's `c_CLASS` the
`@def`'s at the class parameters, a lift (4) the `@def`'s read at a context. A set constant's `c_CLASS` is no
construction: it is the singleton of its value, a set (decision 5). The generator, *Comprehension*, builds the class
of records of each subformula from its children's by base's rows and proves it EXACT: for every record `b` on `k` whose
entries are `e⃗`, `elem(b, A_ψ) ↔ ψ(e⃗)`. The class named is the top class's section at the context, `c` the tuple of
the free variables — `∅` for a constant — by one of two schemas proved once in base, `member_class [Q(1)]` and
`graph_class [Q(2)]`: if `A` is exact at every extension of `c` by `t` (and `r`), a class `K` with
`elem(t, K) ↔ Q(t)` (`pmem(t, r, K) ↔ Q(t, r)`) exists. Each is proved from `lam_pred` or `lam_class`
(`{t : c ++ [t] ∈ A}`, `{⟨t, r⟩ : c ++ [t, r] ∈ A}`) and `snoc_EX`, uniform in the context's length.

**2. The pieces, each one rule** (D1). The generator walks the naming of the formula's atoms and reads each binder's
`NamedPiece` — never a constraint back (I1):

| piece, or atom | its class at the record |
|---|---|
| `∧ ∨ ¬ → ↔` | `B2`, `B_or`, `B3`, `imp_as_nand`, `B_iff`; exact by the connective's congruence |
| `∃ᵢ`, Isabelle's or a naming's (`τ`, `r`, `v`) | `row_ex` at the scope's length; exact by `snoc_read`. `∀ᵢ` as `¬∃¬` |
| `elem`, `eq`, `zero`, `nsucc`, `snoc` on entries | `read2`, `read1` or `read4` into the atom's witness class |
| an atom on a fixed class: a class parameter, an opened class, a function variable | `read1` or `read2` into it; `apply(τ, r, F)` into `F`'s application class, `cls_apply` |
| `.setConstant(c)`: `∃ᵢv. c(v)` | `v` an entry; `c(v)` read into the singleton of `c`'s value (`c_CLASS`), opened |
| `.constantClass(c)`, no class argument | OPENED: `C₀` from `c_CLASS`; the atom on `C` read at `C₀`, joined there by `c_AGREE` |
| `.constantClass(c, classes: K⃗)` | LIFTED: `U` from `c_LIFT` at the λs' bundles; the atom on `C` read at `U` |
| `.lambdaClass(λ)` | its definition's right side built at the extended scope: the BUNDLE its constant's lift takes |

**3. A class binder is a hypothesis of what lies under it.** A class is never an entry (R4), so a naming's class
binder adds no row: the subformula under `∃C. c(C, K⃗)` is built once, an atom on `C` read through a FIXED class — the
opened `C₀` or the lift's `U` — and its exactness holds for EVERY `C` and `K⃗` meeting the binders' constraints at the
record's entries, proved at the atom (by `c_AGREE`, or by `c_LIFT`). The binder's exactness then needs only witnesses:
`←` instantiates that exactness, `→` takes `C₀`, or the bundles' sections at the record and `c_CLASS` at them. One walk,
bottom-up, each class proved where it is built; no formula rewritten whole, nothing laid out before the walk.

**4. The lift: one per class-taking constant, uniform in the context.** A site's context is its record itself — a set,
a tuple on its length — so the lift is stated once, the length a variable:
```
c_LIFT: ∀ᵢp p1. nsucc(p, p1) → ∀A⃗. ∃U. ∀ᵢa. tuple(a, p) → ∀K⃗. K⃗ ≈ₐ A⃗ → ∀C. c(C, K⃗) → C ≈ₐ U
```
`K ≈ₐ A` says `K` is `A`'s section at `a`, `lam_pred`'s or `lam_class`'s right side: `∀ᵢu. elem(u, K) ↔ ∃ᵢb.
snoc(a, p, u, b) ∧ elem(b, A)` at a predicate, `∀ᵢu w. pmem(u, w, K) ↔ ∃ᵢb. snoc(a, p, u, b) ∧ ∃ᵢb′. snoc(b, p1, w, b′)
∧ elem(b′, A)` at a function. At a site on `k` entries the record is the context and the bundles are `A⃗`; `τ` and `r`
are the next two entries, so `pmem(τ, r, C)`'s record is `a ++ [τ, r]` and its class is `U` itself. The proof: `c`'s
`@def` at `C`, its member with each `K_j` read through `A_j` at `a` (Logic's replacement walk, its holes `K⃗ ≈ₐ A⃗`),
built by the generator with `p`, `p1`, `a` as entries, then re-keyed from records `⟨p, p1, a, t, r⟩` to `a ++ [t, r]`
by `snoc`'s injectivity on tuples — a lemma proved once. A class-taking constant in `c`'s body at a λ that mentions `a`
is lifted in turn, its lift cited, earlier in definitional order.

**5. The primitives** go through the same rules from base's definitions (`base/tiers/zf`): the classes of
`ZF_Base.Pow`, `Union` and `PrimReplace`, PrimReplace's lift included, are built from their class predicates'
definitions, `Pow(A, r)` and `Union(A, r)` read through base's own — the primitives being the one thing a rule may name
(D1); `zero`'s and `Inf`'s are singletons (decision 5), from base's `ZF_Base.zero_EX`, `Inf_EX` and their `_UNIQ`.
PrimReplace's VALUE is not a class: it is Replacement at the class of Kuratowski pairs `{⟨u, v⟩ : u ∈ A ∧ ⟨u, v⟩ ∈ P}`,
which `read1`, `B2` and `lam_class` build — a base lemma, so its `_TOTAL` is the graph rule's as `Pow`'s is, and
`Graph.swift`'s `primReplace` member stops refusing.

**6. Base gains**, each kernel-checked before the code. Ported with the reference's proofs: `read1`, `read2`, `read4`,
`cls_zero`, `cls_nsucc`, `cls_snoc4`, `rs_key`, `snoc_read`, `snoc_keep` and the tuple facts the read-back takes
(`first_in`, `next_in`, `tuple_first`, `tuple_last`). New: `cls_apply: ∀F. ∃W. ∀ᵢt r. pmem(t, r, W) ↔ apply(t, r, F)`,
`cls_tuple` (the re-keying's `tuple(a, p)` read as membership — not built, `tuples_class` serves: build decision 4),
PrimReplace's value, and the schemas `member_class` and
`graph_class` (1). FOUNDATION §3 gains, first, the witness-class reading of an atom.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Classes' prover (new, `Sources/Lowering`) | `c_CLASS` of every constant, a set constant's `∃S. ∀ᵢv. elem(v, S) ↔ c(v)` included; `CLASS ⟨λ⟩`; `c_LIFT` of a class-taking constant | `c_DEF`; `c_AGREE`; a set constant's `c_EX` and `c_UNIQ` and base's Pairing (`upair_ex`); Tuple's `TUPLE_EX_n` for a context; the base gains (6) |
| Reify's prover | as before, and `ZF_Base.PrimReplace_TOTAL` by the graph rule | base's PrimReplace value |
| Facts | the statements of a set constant's `c_CLASS` and of `c_LIFT`, from the request alone (I2) | — |

**Tests, written first**, each proof concluding its statement by ID through Fol, `misscoped`, and kernel-checked:
`CLASS ⟨λx. x ∈ y⟩` (rows, `∃`, the section at `⟨y⟩`); `CLASS ⟨λx. f(x)⟩` (`cls_apply`); `ZF_Base.Pow_CLASS` and
`Union_CLASS` from base's definitions; `T.s ≡ λx. Pow(x)`: `T.s_CLASS`, opening `Pow`'s class, and EX ⟨T.s(x)⟩ PROVED
end to end; `T.e ≡ Pow(0)`: a set constant's class; `sub ≡ λA B. ball(A, λx. x ∈ B)`: `ball_LIFT` and `sub_CLASS`, the
λ depending on `sub`'s own argument; two λs at different arguments, ONE lift and no widening; a lift inside a lift's
body (PrimReplace's from base); EX ⟨PrimReplace(a, λx y. x = y)⟩ PROVED. Then the corpus, measured, nothing predicted.

**Not in this step:** a `@def` holding `If`'s proposition slot or a declared constant, refused before the registry (the
reference read a proposition argument as a class of the empty tuple); a class quantifier in a body (FOUNDATION S4: §3 has
no case for one) — the generator throws there (`ComprehensionError.unread`), and no lemma the corpus requests reaches
one; refusing it by name, unbuilt, needs the prover to see the definition before it proves, an interface question raised
when a statement does; a per-arity tuple row, the reference's measured optimization.

**Built.** *Comprehension* (`Comprehension.swift`) walks a definition's raw body and, at each Isabelle atom, its naming's
chain with its pieces (8), opening in the top frame the class of each piece by its row, each row once per key; *Reading*
reads it back exact in a frame fixing a record:
- `∃ᵢ` by `row_ex`, its exactness at every extension `b` by `snoc(a, n_k, v, b)` taken to the record by `snoc_some` and
  `cong_exists`; `∧ ∨ ¬ ↔` by `B2`, `B_or`, `B3`, `B_iff` and their congruence; `∀ᵢ` as `¬∃¬` (`forall_as_nexists`), `→`
  as `¬(A ∧ ¬B)` (`imp_as_nand`); `⊥` as the numeral `0`, empty by `zero_def`;
- an atom by its read row (`read1`, `read2`, `read4`) and its witness's property: `B1`'s, `cls_diag`, `cls_zero`,
  `cls_nsucc`, `cls_snoc4` with `rs_key`, `cls_apply` at a function variable, a set constant's singleton, a fixed class
  itself; `Pow(A, r)` and `Union(A, r)` through `Pow_def`, `Union_def`;
- a record is built by `snoc` from the empty one, `tuple_snoc`, `snoc_new` and `snoc_keep` each `have`d once per
  extension, an older entry read through the chain of `keep`s;
- a class binder: its body read in a frame fixing the class and assuming its constraint; `←` instantiates that, `→` takes
  a witness — `C₀` from `c_CLASS` (opened), the λ's section at the record by `lam_pred` or `lam_class` (a λ), `c_CLASS` at
  the sections (lifted); an atom on a lifted `C` is `U`'s membership at the record two (one) `snoc`s on, by `C ≈ₐ U`,
  `snoc_some` and `snoc_EQ`.

*ClassProver* (`Classes.swift`) owns `c_CLASS`, `CLASS ⟨λ⟩`, `c_LIFT` and `REKEY_m`, `.unbuilt` at a declared constant:
- `CLASS ⟨λ⟩` and a constant's `c_CLASS`: the section by `member_class` or `graph_class` at the context's record — `⟨⟩` for
  a constant — then, for a constant, its definition, a defined constant's `@def` or a primitive's base's;
- `c_LIFT`: the class `W` of records `⟨p, p1, a, t (, r)⟩` at which the definition holds, each class parameter read
  through its section at `a`, its `K ≈ₐ A` a hypothesis at the atom; `U` is `W` re-keyed by `REKEY_1` or `REKEY_2`;
- `REKEY_m`: `U = {a ++ [t (, r)] : tuple(a, p), ⟨p, p1, a, t (, r)⟩ ∈ W}`, built by the generator at the record
  `⟨p, p1⟩`, `tuple(a, p)` read through `tuples_class` at the lemma's fixed `p`; read back by `snoc_inj` on tuples, the
  entries carried along by `cong_snoc_v`;
- a set constant's class: the singleton of its value, Pairing from `c_EX`; `c(v) → v = v₀` by `c_UNIQ`; back by its
  definition carried along the equation — a defined constant's `@def` at its core `eq(v, r)`, `0`'s and `Inf`'s base's,
  unfolded through `zero_def`, `Inf_def` and `ind_def` to membership.

**Decisions made in the build** (no checker change; reviewed by the user, 2026-10-15):
1. **Schema letters with arguments** (the user, 2026-10-15: "go with option 1"): `folLetterAll(n)`, `folLetter`,
   `folLetterAbs`, fol-zfc only (`Sources/IR/Node.swift`); `schema_inst` instantiates one at an n-fold λ, β-reduced, and
   renders it `Q: \b1 b2. φ`. `member_class [Q(1)]`, `graph_class [Q(2)]`, `snoc_some [X(1), P(0)]`, `cong_exists` and
   `forall_as_nexists` are cited at letters with arguments.
2. **`snoc_some`** (`base/tiers/tuples`): the step from an extension's exactness to the record's — the reference's
   `snoc_read`, its class a letter, so a function λ's two-level section is one schema, twice.
3. **A class parameter of a lift's body is read through its section** at the lift's record, `K ≈ₐ A` a hypothesis at
   the atom — decision 2's transport, at a parameter; its `apply` through `apply_def`.
4. **`REKEY_1` and `REKEY_2`**, by the extension's width, the class prover's; `tuples_class` at the lemma's fixed `p`
   reads `tuple(a, p)`, so `cls_tuple` (6) is not needed.
5. **A set constant's class binds a set**, `∃ᵢS. ∀ᵢv. elem(v, S) ↔ c(v)`: its witness is one.
6. **`0` and `Inf` take the singleton rule** with base's EX, UNIQ and definitions — no base lemma per primitive.
7. **`⊥`'s class is the numeral `0`.**
8. **A predicate constant's `_AGREE` is membership's agreement**, `elem(t, C) ↔ elem(t, C′)`: the statement wrote `pmem`
   for every constant, and nothing had cited a predicate's.
9. **PrimReplace's `_TOTAL` by the graph rule**, from `ZF_Base.PrimReplace_value` (7b).
10. **The renderer refuses a reserved word in any segment of a name**: `T.use` lexes as `T`, `.`, `use`.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export`: 2 min 11 s, peak 13.0 GB): every
lemma requested is proved — 0 refused unbuilt, against 225 — and beside the named theorems 1,866 statements reach
fol-zfc, against 1,122: 165 `_CLASS`, 99 `CLASS ⟨λ⟩`, 27 `_LIFT`, both `REKEY`s, 278 EX, 338 UNIQ, 451 `@def`s, and
Reify's and Tuple's other facts (by name, a throwaway count of the unit's statements, not kept). **The named theorems
lowered stay 59**: the 1,167 refused for citing a refused statement each still cite one, none an EX now — `Formula.satisfies_DEF`
heads the list, then theorems refused for no owner — so no named theorem waited on class existence alone. The table holds
15.6M nodes, against 9.5M; lowering takes 60 s, against 25 s. The proofs are kernel-checked in the tests; their rendered
size is unmeasured, emission being unbuilt.

**Decisions**, each agreed by the user, 2026-10-15. **Order of work:** the EX and UNIQ build reviewed and committed
first, as one step; FOUNDATION §3's witness-class line (6) before any code; base's gains (1, 6, 7b) kernel-checked
before any code cites them; then the prover, its tests first.
1. **One construction** (1): every class a formula's class of records and its section. **AGREED 2026-10-15 (user),
   refined**: the step from the class of records to the class named is one of two schemas, `member_class [Q(1)]` and
   `graph_class [Q(2)]`, proved once in base from `lam_pred`/`lam_class` and `snoc_EX` and uniform in the context's
   length — the reference's bridge proved once (`member_class`, `graph_class`, `lambda_class_n` per λ arity) without
   its family; argued inline instead, every class proof would repeat it.
2. **A class binder is a hypothesis of the exactness under it** (3), its transport local to the atom — the reference's
   Opener (a whole-formula equivalence, a dry pass, a spine of classes) has no counterpart. **AGREED 2026-10-15
   (user)**: both build the same classes from the same rows and differ only in where the class is replaced by its
   stand-in — the reference rewrites the whole formula and proves the rewrite; ours replaces it at the one atom that
   mentions it and states everything above that atom for every class meeting the binder.
3. **The context is the record** (2, 4): a λ in a class slot is built in place — no bundle per closed λ, no widening.
   **AGREED 2026-10-15 (user)**: the reference gives each bundle its own context, the variables its λ mentions, so two
   bundles at one binder can differ and are widened, and its rewritten atom spells its context's tuple; ours gives every
   bundle at a binder the same context, the record there, and with decision 2 the atom on the lifted class is read at
   `U` itself.
4. **One lift per class-taking constant, uniform in the context's length** (4), against the reference's `c_lift_p` per
   context size, a family (FOUNDATION §3: families go); the cost is one re-keying per lift. **AGREED 2026-10-15
   (user)**: the lift replaces a class that changes with the formula's sets — Replace's graph at Upair's λ, one per
   `(a, b)` — by one class whose members carry those sets; each class-taking constant states it once, its extra
   arguments one tuple of any length.
5. **Every constant piece opened by its class** (2): a set constant gains a class lemma; the reference linked none.
   **AGREED 2026-10-15 (user), corrected**: a set constant's class is the singleton of its value, a SET — by Pairing
   from `c_EX`, its defining property from `c_UNIQ` and `c_DEF` — not a construction; the atom `c(v)` is read as
   membership in it, a variable in a fixed class, so `v` stays a variable wherever else it occurs. Opened by its value
   instead, the value would stand where no row reads a fixed set (left of `∈`, in `=`, in a tuple).
6. **Atoms read through witness classes, one row per width** (2, 6): kept from the reference. **AGREED 2026-10-15
   (user)**, over one row per atom kind (our base's `row_mem`, `row_eq`, …): every atom is first membership of its
   entries in its witness class, so an atom's exactness is two citations and congruence is membership's, proved once
   in `read1`, `read2`, `read4`; the cost is FOUNDATION §3's line and the port.
7. **The primitives from base's definitions; PrimReplace's value a base lemma** (5). **AGREED 2026-10-15 (user)**:
   `Pow`'s, `Union`'s and `PrimReplace`'s classes and PrimReplace's lift are the general rule's — the class of a
   definition — so the generator builds them from `base/tiers/zf`, `Pow(A, r)` and `Union(A, r)` read through base's
   definitions; PrimReplace's value is an instance of no rule, one fact about one primitive, so base proves it by hand
   (cases on functionality, Replacement at the class of Kuratowski pairs) beside `PrimReplace_EX`.
8. **Dispatch by the naming's pieces** (2, I1): the reference parsed definitions back into λs (`definitionOf`,
   `definedLambda`) and recognized a tuple formula by rebuilding it (`tupleSlots`). **AGREED 2026-10-15 (user)**: the
   generator names the λ's or `@def`'s Isabelle body itself and reads each class and set-constant binder's
   `NamedPiece`, as the EX and UNIQ prover does; its formula equals the stated one by ID, checked, a mismatch thrown.
   Tuple formations need no piece: their atoms are rows.
9. **A new prover owns class existence**: Reify's prover no longer owns `_CLASS` or `CLASS ⟨λ⟩`. **AGREED 2026-10-15
   (user)**: `ClassProver`, a third entry in the plan, owns every `c_CLASS` (a set constant's singleton included),
   `CLASS ⟨λ⟩`, `c_LIFT` and the re-keying lemma; Reify's keeps the rest and proves `ZF_Base.PrimReplace_TOTAL` by the
   graph rule. The boundary is already in the lemmas: EX cites `c_CLASS` and calls none of its code.

### The steps after class existence, in order  **[AGREED 2026-10-15 (user)]**

Dependencies first; the reference's order where it had one, left in two places. After each step `lower` is run again,
and its refusals order 5–8, none of which needs another.

⚠ **FROM STEP 2 ON, THE ORDER IS AGREED AGAIN AROUND FOUNDATION S4** (decided 2026-10-15): "Removed — the rules that
consumed a proposition where it stood" took out what steps 1 and 2 built on a proposition with no object. Step 1's reading
at `i` and step 2's equality at `i` and `class_subst` stand; the rest of 2–4 is designed again from its pieces. Agreed
since, in order: **2′, the logic's rules read as steps** ("The logic's rules read as steps", below), **BUILT 2026-10-16**;
then **boxes binding a proposition, read as schemas** ("Boxes binding a proposition, read as schemas", below), **BUILT
2026-10-16**; then **functions of propositions and the bound `⋀P`** ("Functions of propositions and the bound `⋀P` — S4's truth
set, applied", below), **BUILT 2026-10-16**; then **a definition read at its terms** ("A definition read at its terms",
below), **BUILT 2026-10-16**; then **`OFCLASS`, and a generic theorem in place** ("OFCLASS — a class's membership by its
definition", below), **BUILT 2026-10-16**; then **step 3, an instance at a class type** ("Step 3 — an instance at a class
type", below), **BUILT 2026-10-16**; then **step 4, Pure's equality between functions** ("Step 4 — Pure's equality
between functions", below), **BUILT 2026-10-17**. From 2026-10-17 every run is the ZF session alone
until it is fully translated (user), so each step's scope is measured there.

0. **Emission** (below): no statement of the corpus has met the checker, and class existence's proofs are unmeasured.
1. **Decision 4** (§4a): a theorem cited at a type instance. Restricted to `term`, it is read at `i` and `OFCLASS(i,
   term)` is dropped. **BUILT 2026-10-15** ("Step 1", below): the reader reads it, Logic drops the class fact.
2. **IFOL's own rules at `[i]`**: `allI`, `spec`, `exI`, `exE` the kernel's steps, `refl` base's `eq_refl`, `subst`
   base's claim, `eq_reflection` the identity. Every citation of one discharges `OFCLASS(i, term)`, so none is
   reached before 1. **BUILT 2026-10-15** ("Step 2", below), with Pure's equality at `i` folded in and base's claim
   renamed `class_subst`.
3. **An instance at a class type**, Lambda's: the λ's class (`CLASS ⟨λ⟩`) and β as proof. `spec` and `subst` at a λ need
   it; the function λ at `i`, the reference's largest refusal, is designed in.
4. **Pure's equality between functions**: read pointwise at every function type whose arguments are objects, the
   function of classes included — not each function's class and `mfun_comb`, as first planned ("Step 4", decision 1).
   The reference walked these chains before it had a λ's class; here β comes first (3).
5. **A ZF definition cited**: pointwise, from the `@def` and EX, most often at a chain's leaf (4).
6. **A proposition argument**, `If` and `bool_of_o`: a class of the empty tuple (FOUNDATION S4), as the reference read it.
7. **The hidden variable**, `Pure.dummy_pattern`: the reference refused it, so its design is new.
8. **ZF's axioms**: base derives `extension`, `Pow_iff`, `Union_iff`, `replacement` and `infinity` from NBG;
   `foundation` and `AC.AC` wait for FOUNDATION to pin Regularity and Choice, which `base/axioms` leaves out.
9. **Later**: a declared constant; a binder over classes, and a λ over classes anywhere but an equation (4 reads it
   there); a proposition quantified below a statement's top; an unrestricted type variable.

### Emission — the unit as text, checked by the kernel  **[AGREED 2026-10-15 (user), the three decisions one by one; BUILT 2026-10-15, its decisions in the build for the user's review — `Sources/FolDialect/Emit.swift`, `Render.swift`, `Declaration.swift`, `Parse.swift`, `Sources/IR/Pass.swift`, `Sources/Reader/Reader.swift`, `Sources/Lowering/Logic.swift`, `Base.swift`, `Facts.swift`, `Sources/isa2fol/Lower.swift`, `scripts/check-base.sh`, `check-unit.sh`, `base/tiers/cong`; the checker's changes in fol-zfc-comb, 340e700 and the quoted segment]**

**The step.** Nothing writes the unit. `render` writes one declaration and one proof, a base schema's instance among
its steps, and the tests' `kernelChecks` writes the claims each test proves and runs the checker on them, chained on
base. The corpus's 59 theorems and 1,866 other statements conclude their statements by ID and no more: none has met the
checker, and one whose spine binds a letter cannot be written at all (`RenderError.schema`). Their size is unknown: the
table holds 15.6M nodes, and `render` writes a subproof again at each use (§4.7).

**How the reference builds it** (`kinds-proposal`: `Sources/FolDialect/Emit.swift`, `scripts/check-unit.sh`,
`Sources/IR/Measure.swift`, `Compress.swift`; its DESIGN §4.9):
- `emit` writes every statement as a claim, a schema or a `@def` and a proof for each claim and schema, in citation
  order. A name the checker cannot spell is left out with every statement citing it (`open`); a name base declares
  stops it (`declaredByBase`). `lower --emit DIR`, then `check-unit.sh DIR`: exit 0 and empty stderr.
- `compress` proves each repeated fact once, at the outermost scope its binders allow (`share`, one analysis and one
  rebuild), then by a greedy in rounds where two proofs of one fact compete: 1,765,403 steps to 1,382,428.

**1. Parts, each checked once against the libraries of what it cites.** **AGREED 2026-10-15 (user)**, over one unit
checked whole. Checked whole, a unit is held whole: `proof_checker` read its proof file into one string and parsed every
proof before running one, 687 MB of memory for a 21 MB proof file (base's `classes` tier, 100 times). So the unit is
written as parts. Each part is checked once, against the compiled libraries (`.fol.lib`) of the parts it cites and of
base, and the same run writes its own library (`proof_checker --lib`). A part citing it loads its declarations, never
its proofs. A check therefore holds one part's proofs, one block at a time, and the declarations below it; parts that
cite each other in neither direction check in parallel, and base is compiled once. A part holds its statements in the
unit's order:
- a `@def` as `@def(c) axiom c_DEF: φ`;
- a theorem or a lemma as `claim N: φ` and `proof N:`;
- one whose spine binds letters as `schema N [A0(0), …]: φ`, its proof without their intros, and a citation of it as one
  `schema_inst N { A0: ψ, … }` ahead of the spine's `forall_elim`s ("Logic", 2 and 3). A letter is named by its place on
  the spine.

Within a part the checker loads every header before it runs a proof, resolves `use` against all of them, and decides
Proved once every proof has run (`proof_checker.cpp`), so it is owed no order; the unit's is deterministic (§4.6). A
name base declares stops the run: base is never declared again (G1). **What a part is**, proposed: one Isabelle
theory's theorems. A generated lemma cites only lemmas and base, never a theorem; it goes in the part of the first
statement citing it in the unit's order, so citations point only backwards. A part over a size bound is split.

**The checker's three changes** (`~/repos/fol-zfc-comb` 340e700, branch `libraries-and-streaming`, reviewed by the user 2026-10-15):
- `fol_compiler` builds with `-c opt`: GCC 11's false `-Wstringop-overflow` in `src/library/library.cpp` is gone.
- A library holds the sentences of its new named entries only. A running proof registers each quantified formula it
  builds, one over an outer fixed variable among them, and base's `classes` tier could not be saved ("FixedVar in
  stored formula"). A claim interned to a dependency's sentence was dropped from its library, silently.
  `test/library_test.cpp`, never wired into the build, now runs: two new tests fail on the old writer.
- `proof_checker --lib OUT` writes the library after a check that exits 0.
- `proof_checker` reads a proof file one block at a time (`stream_proofs`): 687 MB to 56 MB on the file above, the
  same report. A proof file holds proof blocks only, as its format says; another statement is now an error.

Verified with the new binary: the checker's 30 tests, base's 13 tiers and this repository's tests; base's chain built
by `--lib`, each tier checked against the libraries below it. ⚠ **THE FORMULA ARENA STILL GROWS WITH EVERY DISTINCT
FORMULA OF A PART**: streaming bounds the text and the parse, the part bounds the arena.

**2. A subproof is written once while its step is in scope.** **AGREED 2026-10-15 (user).** Emission only: the table
and the passes are unchanged, and a step is cited by its local handle (`_1`), never a new claim. `render` writes the proof's tree: a node the table shares
is written at each use, k uses k copies, and nesting multiplies. The renderer keeps each step it writes, keyed by its
node and by the names its loose indices resolve to (⚠ a node is not a fact: `hyp(0, set(#0))` under two `fix`es is two
facts), and forgets it when its scope closes; a node found there is cited by its step's name. The text is then linear in
the proof's DAG per scope and never longer than the tree, with no checker change. Not the reference's `share`: a repeat in
two sibling scopes, or one fact proved two ways, stays — that is compress, decided on this step's measurement.

**3. The check is the checker's report, part by part, by a script.** **AGREED 2026-10-15 (user).** Today `check-base.sh` checks each tier against
the text of the tiers below, re-running every one of their proofs, the tests' `kernelChecks` re-run all of base at each
call, and nothing checks an emitted unit or measures what it writes.
- `isa2fol lower EXPORT --emit DIR` writes `DIR/P.fol.def` and `DIR/P.fol.proof` for each part `P`, and `DIR/parts`:
  one line per part in citation order, naming the parts whose libraries it loads, in loading order. It prints what it
  wrote — claims, schemas and `@def`s per part — and the steps written beside the tree's, by statement kind (a theorem,
  a lemma by its suffix): decision 2's measurement, and compress's input.
- `scripts/check-base.sh` compiles base once: each tier checked with `--lib` against the libraries of the tiers below
  it. The same libraries serve every unit and the tests.
- `scripts/check-unit.sh DIR` checks the parts in `DIR/parts`' order with `--lib`, each against base's libraries and
  those its line names. A part is valid only when the checker exits 0, stderr is empty, Proved lists every claim and
  Schemas proved every schema; `Conditional`, `Unproved`, `Failed` or `Missing` is a failure, never a count beside
  Proved. A part naming an invalid part is not checked, and is reported with the part it waits on, so no check ever
  loads an invalid part's library. That also keeps out the checker's known gap: an `UNPROVED` schema saved to a library
  loads back as proven (fol-zfc-comb 94c5db9). The script exits 0 only when every part is valid.

**Tests, written first** (`FolDialectTests`), each unit kernel-checked by the real checker: a unit's statements are
written in its order, a `@def`, a claim and a schema each as its declaration; a schema's proof has no intro for its
letters, and a citation of it is one `schema_inst` naming them; a subproof used twice in one scope is written once, in
two sibling scopes twice, and under two binders of one name as two facts; a name base declares stops emission; a
statement goes in its part and a lemma in its first citer's, and two parts are checked in order, the second against the
first's library. Then `kernelChecks` writes its units through `emit`, against base's libraries (rule 4: one way to
write a unit).

**Not in this step:** compress, the reference's `share` and rounds, decided on decision 2's measurement; checking parts
in parallel; lowering by part, for the table's own ceiling (13.0 GB at 15.6M nodes).

**Built.**
- `Render.swift`: the writer keeps the steps it wrote, keyed by node and by the names its loose indices resolve to, and
  a closing scope drops only those naming its variable or its assumption (decision 2, build decision 2). A letter on a
  statement's spine is the schema's, `A0, A1, …` by place, its intro writing no line; a citation of a schema is one
  `schema_inst` with every letter, then the spine's eliminations in order. `Declaration.schema(letters:)`.
- `Emit.swift`: `emit(unit, to:, base:, partBytes:)` — a theorem in its theory's part; a lemma or a `@def` in the first
  part among its citers', or `_uncited`; theories ordered by their theorems' citations; in a part a cited statement
  before its citers; a part over `partBytes` (64 MiB) split, `P.2`, `P.3`; `DIR/parts`, each part with the parts whose
  libraries it loads, transitively, in loading order; each statement streamed to its part's files; per statement the
  steps written, its tree's and its DAG's. A name base declares stops it.
- IR: `Statement.theory`, the reader's; `cited(by:in:)`, the unit's citation graph, on the helpers `linked` uses.
- `lower EXPORT --emit DIR`, its report by kind from Lowering's typed requests (`kind(of:)`).
- `scripts/check-base.sh [LIBDIR]` checks each tier once with `--lib`, against the libraries of the tiers it lists;
  `scripts/check-unit.sh DIR [BASE_LIBS]` checks each part of `DIR/parts` in order, against base's and its parts'
  libraries, and does not check a part naming an invalid one.
- Tests: `EmissionTests`; `kernelChecks` writes through `emit` and checks through `check-unit.sh`; `WalkTests` pins
  the walk's linearity.

**Decisions made in the build** (no checker change unless said; for the user's review):
1. **A lemma or a `@def` no statement cites goes in a last part, `_uncited`.** The registry proves a statement's lemmas
   before the statement is refused for a letter off its spine or at link, so the unit holds lemmas nothing cites; they
   are proved, so they are emitted and checked, after every theory.
2. **A step stays citable until a scope it depends on closes** — decision 2's scope made the checker's: a closing scope
   drops only the steps naming its variable or its assumption (`cleanup_scope`, `src/proof/nd/stack.cpp`; a step's
   name is the proof's). Per block, `WF.wfrec_on_AGREE` wrote 6.0M steps for its 453 distinct.
3. **The replacement walk proves a binder's equivalence once and carries it by the binder's schema** (`Logic.swift`,
   `quantified`): `cong_forall`, `cong_exists`, `cong_exists_bare`, and `cong_forall_bare`, added to `base/tiers/cong`.
   It proved both directions, each under its own witness, from one node the checker derived twice per binder:
   `WF_absolute.rtrancl_alt_FUNC` was 1,238 distinct steps and 3.4·10¹² as a tree, `Limit.cf_FUNC` 1,714 and
   3.6·10¹², `ZF_Base.Pair_FUNC` 3.6M written. `WalkTests`: through n nested `∃`, 48, 118, 258, 538, 1,098, 2,218
   steps before; a constant step per binder now. A `∀` over a proposition's letter keeps both directions: no
   first-order schema quantifies over a letter.
4. **A reserved word as a segment after the first is written quoted**, `Com.bexp."false"` (the user, 2026-10-15: a
   checker change, `qualified_name DOT STRING_LITERAL` in `src/parser/formula.y`): a keyword token carries no spelling
   (`false` and `bottom` are both `BOTTOM`), so the grammar could not take the word itself, and a lexer that did would
   read `forall x.false` by its whitespace. The export's seven: `Bool.and`, `Bool.not`, `Bool.or`, `Com.bexp.false`,
   `Com.evalb.false`, `FOL.excluded_middle`, `IFOL.iff` (Expand's). ⚠ An earlier count named the three `Bool` ones
   alone — it read one session's constants, not the export's names.
5. **A theorem's part is the reader's theory**, `Statement.theory`: a name's first segment can be a locale's.
6. **The report's kinds are Lowering's typed requests** (`kind(of:)`), not the names' suffixes.
7. **Base is checked once, by libraries**: `check-base.sh` checks each tier against its listed tiers' libraries; the
   text chain re-ran every lower tier's proofs.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`, 303 s, peak 13.4 GB, the
emission 169 s; then `scripts/check-unit.sh DIR`, 9.9 s, peak 551 MB): every statement the pipeline leaves is emitted
and **every one is Proved by the kernel** — 39 parts, 1,445 claims of 1,445 and 29 schemas of 29, exit 0 and empty
stderr in each, base checked first; 451 `@def`s. 72 MB of text, 1,033,187 steps written against 1,107,750 in the
proofs' trees and 879,656 distinct. By kind, written: a constant's class 483,045 (165), a λ's class 259,536 (99), a
lift 123,625 (27), UNIQ of a term 48,717 (338), a constant's function 43,491 (106), EX of a term 28,924 (278), a λ's
function 22,595 (73), the rest under 10,000 each; the 86 theorems, the 59 named and the 27 they cite outside, 609. The
named theorems lie in 33 theories' parts; 1,388 lemmas, cited by refused statements alone, in `_uncited`.

### Step 1 — a theorem cited at a type instance (§4a, decision 4)  **[AGREED 2026-10-15 (user), the two decisions one by one; BUILT 2026-10-15, its decisions in the build for the user's review — `Sources/Reader/Reader.swift`, `Sources/Lowering/Logic.swift`, `Sources/IR/Index.swift`, `docs/SOURCE_SURFACE.md`; decision 2 REMOVED 2026-10-15, "Removed — the rules that consumed a proposition where it stood"]**

**The step.** IFOL and FOL state their rules once, for every type of class `term`, and the export makes the class a
premise (`unconstrainT`, §4.3a 5): `IFOL.sym` is `OFCLASS('a, term) ⟹ a = b ⟹ b = a`, and a ZF proof cites it at `i`,
discharging the premise with a box that cites `ZF_Base.arity_term_i : OFCLASS(i, term)`. The reader keeps both as
written, `use(theorem, [i], o)` and `isaOfClass(i)`; no pass owns either, so a statement holding one is refused before
the first pass. The unit holds no theorem read at `i`: `Reader.unit()` takes a cited theorem only when it is cited with
no type arguments. `i :: term` is the export's only arity (`ZF.ZF_Base/theory/arities`; every other theory's is
empty), so a theorem restricted to `term` has one instance, at `i`.

**How the reference builds it** (`kinds-proposal`, its §4a decision 4, built 2026-10-05): its reader reads a theorem
whose every type variable carries `OFCLASS(α, term)` at `i` (`Reader.typeVariables`), cited by name; Logic first drops
`OFCLASS(i, term)` in a walk of its own (`ClassRule`) — the premise, its discharge, its hypothesis — and a hypothesis
still used refuses (`classHypothesisUsed`). It records two warnings: its drop could not share a walk with its Logic's
rule, whose `before` hooks left a replacement's subtree for the next round; and Isabelle registers each axiom as a fact
of the same name (`IFOL.subst`), which, read at `i`, declared base's claim again (`declaresAxiom`).

**1. The reader reads a theorem at `i` when every one of its type variables is restricted to `term`.** **AGREED
2026-10-15 (user).** Under its own name, a theorem a ZF proof cites at `i` (`IFOL.sym`) and a named ZF theorem generic
over `term` alike, so a name is one statement; it is read by `prove(key, at:)`, as an unnamed box is read at its
citation's types (§4.3a 3). `Reader.unit()` takes it when cited, and the citation is written `use(.theorem(name), [],
root)`: it cites the unit's statement, `root` exactly. The reader makes no translation choice: the citation names `i`,
the only type in `term`. `OFCLASS(i, term)` is then an ordinary premise, hypothesis and discharge (§4.3a 5b). A theorem
with a type variable not restricted to `term` is read at its variables and stays refused: decision 4's deferred half.

**2. Logic drops `OFCLASS(i, term)` where the reader reads it as an ordinary construct.** **AGREED 2026-10-15 (user).**
⚠ **REMOVED** ("Removed — the rules that consumed a proposition where it stood"): the drop is a rule on the implication around the class fact, not on the fact; FOUNDATION
S4 renders `OFCLASS(i, term)` by its definition, `⋀P::prop. P ⟹ P`, and until then `isaOfClass(i)` has no owner.
The class fact `isaOfClass(i)` is Logic's piece and has no formula: the implication it stands in removes it, at the three
places §4.3a 5b names.

| where | before | after |
|---|---|---|
| a premise | `isaOfClass(i) → φ` | `φ` |
| an assumption | `folImpliesIntro(isaOfClass(i), body)` | `body`, its hypotheses renumbered |
| a discharge | `folImpliesElim(p, q)`, `q` concluding `isaOfClass(i)` | `p` |

`piece(_:)` maps `isaOfClass(i)` to `.classFact`, owned, and the implication's three kinds to `.implication`, not owned:
fol-zfc's own. The drop is a walk of its own, `ClassFacts`, before Logic's rules' walk, `Steps`: bottom-up, `after`
alone, so a discharge is gone before its assumption closes, and a citation's root loses its premise by the rule its
statement does — the same ID. ⚠ **THE DROP CANNOT SHARE `Steps`' WALK**, as proposed: Reify's instance at a compound
term, called there, reads the formulas the walk was given (`was: id`) and expects only its own naming to change them.
Sharing the walk, a class-premised theorem cited at `Pow(0)` met the class fact on one side only, and the corpus's run
stopped (`LogicError.context`; `aClassPremiseIsDroppedBeforeAnInstanceAtACompoundTerm`). Every other rule of `Steps`
keeps a formula; the drop is the first that removes one. The proof behind a discharge, `arity_term_i`, is never lowered: its own proof cites
`IFOL.term_class.intro` at `[i]`, whose `'a` is unrestricted, so it stays refused, and nothing cites it once the
discharges are gone. `isaOfClass` at a type variable has no owner; a class fact anywhere else has no rule and stops the
run (`PipelineError.survived`).
- **The contract.** The reader provides a class fact at `i` only where it is true — Isabelle proved it, or the reader
  read at `i` a theorem restricted to `term` — so Logic drops one without naming its class.
- **The framework's one addition.** `unshift` takes the namespace: over hypotheses it renumbers what a removed assumption
  leaves, and throws if the removed hypothesis is still used.

**Built** (`Sources/Reader/Reader.swift`, `Sources/Lowering/Logic.swift`, `Sources/IR/Index.swift`). The reader's
`types(of:)` gives a theorem's instance once: `i` for each type variable when the statement's leading premises, under its
`∀`-closure, restrict every one to `IFOL.term`, else its own variables; `read` proves it there, and a citation at that
instance is written with no types. Logic's `piece(_:)` answers `.classFact` and `.implication`; `ClassFacts`, run ahead
of `Steps`, applies `dropped(_:in:)`, the table above. Tests: `aTheoremRestrictedToTermIsReadAtI`,
`aTheoremWithATypeVariableNotRestrictedToTermIsReadAsStated`, `aCitationAtIOfATheoremReadAtICitesItsStatement`,
`theUnitHoldsATheoremRestrictedToTermReadAtI`, `unshiftOverHypothesesRenumbersWhatARemovedAssumptionLeaves`,
`aClassPremiseItsAssumptionAndItsDischargesAreDropped` and `aClassPremiseIsDroppedBeforeAnInstanceAtACompoundTerm`, the
kernel proving each one's unit; the census counts `T.P` at `i`.

**Decisions made in the build**, for the user's review:
1. **The restriction is read from the statement at its own variables**, read once more for a theorem with a type variable:
   the leading `OFCLASS` premises under the `∀`-closure, where `unconstrainT` puts them. A leading class premise other
   than `IFOL.term` at a type variable restricts nothing, so the theorem is read as stated.
2. **The reader alone names `IFOL.term`**; Logic drops a class fact at `i` of any class, as the contract allows.
3. **`kernelChecks(_:)` takes a lowered unit**, emitted and checked whole; the claims form builds one and calls it.
- ⚠ **`IFOL.subst` IS BOTH BASE'S CLAIM AND ISABELLE'S FACT OF ITS AXIOM**: read at `i` it is a statement of the unit,
  refused at Logic while the axiom at `[i]` is unbuilt. Lowered, it would declare base's name again, which emission
  refuses (`EmitError.declaredByBase`): step 2's, which renames base's claim `class_subst`.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`: 5:18, peak 14.6 GB; read
71.4 s, lowered 74.1 s, emitted 171.2 s; 17,340,411 nodes. Then `scripts/check-unit.sh DIR`: 10.5 s, peak 520 MB):
- **The kernel proves the unit**: 39 parts, each exit 0 and empty stderr; claims 2,179 of 2,179, schemas 30 of 30;
  451 `@def`s; 81 MB, 1,208,747 steps written against 1,273,349 as trees and 1,025,066 distinct.
- **Named theorems lowered: 59, as before.** The unit gains 61 theorems cited outside the ZF sessions (194) and 735
  statements reaching fol-zfc (2,601 beside the 59). Refused named theorems move from no owner (7,176 → 4,003) to
  Logic's unbuilt (924 → 3,822), a letter off its spine (94 → 222) and a refused citation (1,167 → 1,314).
- **What no pass owns now** is led by `use(theorem, [i], o)`, 1,731: a theorem whose type variable is not restricted to
  `term`, cited at `i` — `FOL.meta_simps.1`, `(⋀x::'a. PROP P) ≡ PROP P`, by 1,662 named theorems at `[i]` and 309 at
  `[i ⇒ o]`; `Inductive.def_trans` at `[i, i]`, 126; `ZF_Base.split_def` and `pair.split` at `i`, `o`, `i ⇒ i` and
  `i ⇒ o`; `Pure.meta_spec` at `[i]`, 14 (a count over the read unit, not kept). Then `use(definition zf object, [],
  o)` 1,542 and `isaFree(i)` 1,489.
- **What Logic leaves unbuilt** is an instance at a class type — `isaAllElim(o, (i ⇒ o))` 2,859 (step 3) — and Pure's
  equality at an object function type — `isaCombination((i ⇒ o), o, o)` 2,308, `isaReflexive(i)` 2,147,
  `isaAbstract((i ⇒ o), o)` 2,133 (step 4); `isaAbs((i ⇒ o), body: o)`, a `λ` over a class, 2,044. No citation of an
  axiom stops a named theorem there: IFOL's rules at `[i]` (step 2) stand in the proofs of the IFOL theorems ZF cites
  by name, so they surface only once those theorems' citers pass Logic.
- `docs/SOURCE_SURFACE.md`, regenerated, still counts `isaOfClass('a)` in 7,965 closures: the census walks the closure as
  read, where every discharge reaches `arity_term_i` and through it `IFOL.term_class.intro` at its own `'a`. Logic's
  drop takes both out of every lowered proof. `docs/CLOSURE.md` regenerates unchanged.

### Step 2 — IFOL's rules and Pure's equality at `i`  **[AGREED 2026-10-15 (user), the three decisions one by one; BUILT 2026-10-15, its decisions in the build for the user's review — `Sources/Lowering/Logic.swift`, `Reify.swift`, `Base.swift`, `base/tiers/zf`; decision 1 REMOVED 2026-10-15, "Removed — the rules that consumed a proposition where it stood"]**

**The step.** IFOL states its quantifier and equality rules once, over a type in `term`; read at `i` (step 1), a
citation of one is `use(axiom IFOL.spec, [i], o)`, which Logic owns unbuilt, and every IFOL theorem built on it falls
with every ZF theorem citing those. Pure's `reflexive`, `symmetric` and `transitive` at `i` (`x ≡ x`, read `x = x`) are
unbuilt too: in step 1's run 2,147, 986 and 88 named theorems hold them. `⋀` and `∀` read as one node, `ifolAll`, and
`≡` at `i` as `=`. Isabelle registers each axiom as a fact of its name (`IFOL.subst`, proved through a box citing the
axiom), and base already states one claim under an Isabelle name: `IFOL.subst`, the axiom as the pipeline renders it at
`i`. Folded in at the user's agreement (2026-10-15): Pure's equality at `i`, which no step of the order named. Step 2
alone lowers few named theorems: a citation of `spec` mostly instantiates `P` at a λ, step 3's.

**How the reference builds it** (`kinds-proposal`, `Sources/Lowering/Logic.swift`): a table of kernel rules, each a
core over the citation's premises, `kernelProof(name, rule, root)` taking the binders and premises off the cited
statement; `allI` and `eq_reflection` the identity, `spec` an instance, `exI` and `exE` the kernel's `∃` rules; Pure's
`reflexive`, `symmetric`, `transitive` at `[i]` base's `eq_refl`, `eq_symm`, `eq_trans`, in its walk's `before`. It
records that an axiom and its fact share a name (`IFOL.exE`): a citation is paired with a proof by ID.

**1. IFOL's quantifier rules and `eq_reflection` at `[i]` are the kernel's steps, built from the statement.** **AGREED
2026-10-15 (user).** ⚠ **REMOVED** ("Removed — the rules that consumed a proposition where it stood"): built in place, each proof stood to be reduced by an elimination at
`o` reading it; IFOL's `refl` goes with it, its proof the same construction. `allI` and `eq_reflection` read as `A → A`, the identity; `spec` is `λh. h x`, a `forall_elim`;
`exI` is `λh. ∃-intro(h, x)`; `exE` is `λh k. ∃-elim(h, λy hy. k y hy)`. Every kernel proof, the propositional rules'
included, is built from the citation's statement as the walk hands it: its binders and premises taken off, the rule's
core inside. That statement carries Reify's naming (`P(x)` is `x`'s 1-tuple's membership in `P`), which a proof from a
fixed template would not conclude; one construction for every rule is rule 4. Nothing is admitted: each of these
statements is a theorem of first-order logic, proved by the checker's own inference rules.

**2. `refl`, and Pure's `reflexive`, `symmetric` and `transitive` at `i`, are base's `eq_refl`, `eq_symm` and
`eq_trans`.** **AGREED 2026-10-15 (user).** At variables, one base citation each — claims base proves from
`extensionality`. A side is mostly a compound term, and fol-zfc has none: Reify names each side of an equation where it
stands, so `f(x) = f(x)` needs `f(x)`'s uniqueness, and a predicate at a non-variable is refused by the table. The rule
at variables (`∀y. y = y`, `∀y z. y = z → z = y`, …) is instantiated at the sides by the instance Reify proves at a
compound term (`TermInstance`, EX and UNIQ of the term); at a variable it is a `forall_elim`. `equality(_:_:)` builds
`i` as it builds `o`; the sides are read off the step the walk was given, as Reify's instance reads its node. IFOL's
`refl`, `∀a. a = a`, is decision 1's construction with `eq_refl` at the bound variable as its core.

**3. `subst` is base's claim, under a base name.** **AGREED 2026-10-15 (user).** Base's `IFOL.subst` is renamed
`class_subst`, its statement and proof unchanged: Isabelle's fact `IFOL.subst`, read at `i` since step 1, lowers to a
claim of the unit, which emission would refuse beside base's (`EmitError.declaredByBase`). Of base's 11 qualified names
it is the only one that is also an Isabelle fact or axiom; no base proof cites it and no code names it. Rejected:
skipping the unit's statement at emission (a special case), and reading every axiom's fact as the axiom (a reader change
for all of them, taking the IFOL schemas out of the unit). Both work around the name; the rename removes it.

**Built** (`Sources/Lowering/Logic.swift`, `Reify.swift`, `Base.swift`, `base/tiers/zf`). Logic maps each logic axiom to
its piece in one function, `rule(_:)`: the kernel's step, `.kernel`, or base's claim, `.claimed`. A kernel step's proof
takes its binders and as many premises as its core uses (`Kernel.premises`) off the cited statement. Pure's equality at
`i`, `Equalities.atI`, states the rule at variables twice — the isa step, and base's lemma over Reify's naming — and
instantiates the second at each side by `Reify.instance`, the first standing as the node it reads. Tests:
`ifolsRulesAtIAreTheKernelsStepsAndBasesClaims` (the seven statements, each proved by citing its axiom, `IFOL.subst`
the unit's own claim beside base's), `puresEqualityAtIIsBasesEqualityAtVariablesAndAtACompoundTerm` (at variables and
at `Pow(0)`) and `puresReflexiveAtITakesItsSideAsRead`, the kernel proving each unit; the ownership rows. ⚠ **A SIDE IS
READ OFF THE STEP AS THE WALK WAS GIVEN IT, NEVER OFF THE REBUILT ONE**: a term holding a λ over a formula is rewritten
by the walk, Reify naming the atoms inside the λ, and the λ's class is built from the λ as read. Taking `reflexive`'s
side from the rebuilt step stopped the corpus's run (`ComprehensionError.unread` at `PrimReplace`'s λ).

**Decisions made in the build**, for the user's review:
1. **`subst` is a citation of base's `class_subst` that keeps the statement the walk hands it** — not decision 1's
   construction around a core citing it. Base's statement is fol-zfc and the walk's is isa until Fol (Reify's chain
   writes `∃` at `i` as an isa binder, Fol adds `set(t)`), so a core citing base at Logic would need a bridge between the
   two forms; the statement Fol lowers is base's, as base's comment says and the kernel confirms.
2. **A kernel step takes off as many premises as its core uses**, so `impI`, `mp`, `allI` and `eq_reflection` share the
   identity, as the first two did.
3. **Reify's instance is one function**, `Reify.instance(_:was:base:in:)`, which Reify's walk and the equality at `i` call.
- **Found:** Isabelle's facts of these axioms (`IFOL.spec`, `IFOL.exE`, …) cite their axiom at an η-expanded class
  variable, `λx. P x` — an instance at a class type, step 3's, so they stay refused until then.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`: 5:57, peak 15.1 GB;
read 70.9 s, lowered 75.7 s, emitted 209.3 s; 17,817,150 nodes. Then `scripts/check-unit.sh DIR`: 11.6 s, peak 512 MB):
- **The kernel proves the unit**: 39 parts, each exit 0 and empty stderr; claims 2,221 of 2,221, schemas 30 of 30;
  88 MB, 1,276,817 steps written against 1,345,015 as trees and 1,082,260 distinct.
- **Named theorems lowered: 63**, four more — `DC.DC0_imp.RR_def`, `XX_def`, `DC.imp_DC0.RR_def`, `XX_def` — and
  2,639 other statements. Refused: no owner 4,003, Logic 3,812 (−10), a letter off its spine 222, a refused citation
  1,320 (+6). IFOL's part proves `IFOL.refl` and `IFOL.eq_reflection`; `IFOL.spec`, `exI`, `exE`, `allI` and `subst`
  are not among its claims (the instance at `λx. P x`, step 3).
- `isaReflexive(i)` and `isaTransitive(i, o, o)` leave what stops at Logic; the theorems that held them stop at an
  instance at a class type (`isaAllElim(o, (i ⇒ o))` 2,859) or at Pure's equality at an object function type
  (`isaCombination((i ⇒ o), o, o)` 2,308) — steps 3 and 4.

### Removed — the rules that consumed a proposition where it stood  **[AGREED 2026-10-15 (user); BUILT 2026-10-15 — `Sources/Lowering/Logic.swift`, `Congruence.swift`, `Instance.swift`, `Sources/IR/Index.swift`]**

**The step.** FOUNDATION S4 gave a proposition no object, so a proposition bound below a statement's top, and a function
of propositions, had no rendering. Four rules stood in for one, each reading a node beside its own piece — the intro it
reduced, the form it consumed, the implication around it — which D1 forbids. S4 now makes a proposition an object as its
truth set, so each of those pieces is owed a rule of its own. The four go first, and S4's steps are designed from the
pieces, never reconciled with the rules that consumed them.

| removed | built in | it read | the piece now |
|---|---|---|---|
| an elimination at `o` reduced into a ⋀-intro by `instantiate` | "Logic", point 3 | its premise's shape | `isaAllElim(o, o)` is `schema_inst` wherever it stands; a box's letter is then off its spine, refused `letterOffSpine` |
| the logic's axioms proved in place from the cited statement, a ⋀-intro per letter (`proof(_:of:)`), at `[i]` too | "Logic", point 4; "Step 2", decision 1 | — the intros the reduction consumed | a citation of an axiom of the logic is Logic's, unbuilt; `subst`, base's `class_subst`, stays |
| an equation between functions of propositions as the congruence it carries, `combination`, `symmetric` and `transitive` consuming it, a λ over propositions owned as their context | "Logic's second step" | its premise's shape | `isaReflexive`, `isaSymmetric`, `isaTransitive` and `isaCombination` at a function of propositions, and `isaAbs` there: Logic's, unbuilt |
| `OFCLASS(i, term)` dropped as a premise, an assumption and a discharge (`ClassFacts`), with `unshift` over hypotheses | "Step 1", decision 2 | the implication around the class fact | `isaOfClass(i)`: no owner, as before step 1 |

**Kept.** A letter at a statement's top and `schema_inst` at a citation ("Logic", points 1–3); Pure's rules read as steps;
`≡` at `o` as base's `iff_*` and at `i` as `eq_*` (step 2, decision 2); `subst` as base's `class_subst` (step 2, decision
3); the reader reading a theorem restricted to `term` at `i` (step 1, decision 1); Reify, the registry and emission.

**Moved (D3).** `Replacement`, the congruence walk, leaves `Logic.swift` for `Congruence.swift`: after the removal only
Reify's instance and the provers walk it. Its failure is `CongruenceError.noCongruence`, which `congruent` throws too;
`InstanceError.noCongruence` and `LogicError.context` go.

**Tests.** Deleted with their rules: eight of `LogicTests` (the kernel's proofs, the reduction, a box behind a redex at
`i`, the congruence form and its holes); five of `PlanTests` (`aClassPremiseItsAssumptionAndItsDischargesAreDropped`,
`aClassPremiseIsDroppedBeforeAnInstanceAtACompoundTerm`, `theLogicsOwnTheoremIsLoweredAsASchemaProvedByTheKernelsStep`,
`theSimplifiersRewriteIsLoweredWhole`, `aDefinitionsCitationAtAFunctionOfPropositionsIsLoweredWhole`); `IndexTests`'
`unshift` over hypotheses. Rewritten: `anEliminationAtAPropositionIsSchemaInstAndABoxsLetterIsOffItsSpine`,
`ifolsSubstAtIIsBasesClassSubstAndItsOtherRulesAreUnbuilt` (the kernel proving `IFOL.subst`), and the ownership rows.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`: 5:31, peak 12.9 GB; read
70.9 s, lowered 59.6 s, emitted 199.2 s; 14,701,772 nodes. Then `scripts/check-unit.sh DIR`: 10.0 s, peak 543 MB):
- **The kernel proves the unit**: 4 parts, each exit 0 and empty stderr; claims 1,326 of 1,326, schemas 0 of 0; 437
  `@def`s; 76 MB.
- **Named theorems lowered: 8** (63 before) — `AC_Equiv.AC18_def`, `AC_Equiv.AC18.intro`, `DC.DC0_imp.XX_def`, `RR_def`,
  `DC.imp_DC0.XX_def`, `RR_def`, `allRR_def`, `Group.group.is_group` — and 1,755 other statements (2,639).
- Refused: no owner 7,176 (4,003), `isaOfClass(i)` in 6,046 of them; Logic 1,089 (3,812), led by an instance at a class
  type (`isaAllElim(o, (i ⇒ i))` 458, `(i ⇒ o)` 351) and Pure's equality at `o ⇒ o` (`isaCombination` 416, `isaAbs(o,
  body: o)` 416, `isaReflexive` 412); a letter off its spine 40 (222); a refused citation 1,107 (1,320), led by
  `Formula.satisfies_DEF` 58, `FOL.ccontr` 57 and `IFOL.TrueI` 51.

**Next.** The order from step 2 on is agreed again around FOUNDATION S4 ("The steps after class existence, in order").

### The logic's rules read as steps  **[AGREED 2026-10-16 (user), the five decisions; BUILT 2026-10-16, its decisions in the build for the user's review — `Sources/Reader/Reader.swift`, `Sources/IR/Node.swift`, `Pattern.swift`, `Table.swift`, `Sources/Lowering/Logic.swift`]**

**The step.** FOUNDATION S4: an application of one of IFOL's or FOL's rules is the kernel's step at its premises, never a
substitution into a translated rule. The rules are the 18 axioms of `IFOL.thy` and `FOL.thy` (`Axiom.ifol`, `Axiom.fol`),
natural deduction's: fourteen are introductions and eliminations fol-zfc has as steps, `refl` and `subst` are equality's,
which fol-zfc defines, and `eq_reflection` and `iff_reflection` take IFOL's `=` and `⟷` to Pure's `≡`. Since "Removed", a
citation of one is Logic's, unbuilt (but `subst`), and every statement whose proof applies one falls. Rejected (user,
2026-10-15): each axiom a schema base proves once, cited and instantiated at every use.

**The problem, in target text.** `conjI` at `A` and `B`, applied to `p ⊢ A` and `q ⊢ B`:

```
Isabelle    conjI · A · B ∙ p ∙ q
read        folImpliesElim(folImpliesElim(isaAllElim(isaAllElim(use(axiom IFOL.conjI), A), B), p), q)
wanted      folAndIntro(p, q)                                    emitted   and_intro _p, _q
```

Read, the application is five nodes and the rule stands at the bottom one; a rule there making `and_intro p q` would read
the four above it, which "Removed" took out (D1). In the proof term it is one application, the axiom and its arguments in
order, which the reader decodes as one spine (`decode.proofSpine`) — the one place it is one thing. The reader reads Pure's
seven rules there already (`Reader.pure`, "Logic's second step"), and reads IFOL's `∧`, `∨`, `⟶` and `False` as fol-zfc's
own nodes (§4.3b): a rule fol-zfc has is read as its step on the same ground.

**1. The reader reads an application of a rule fol-zfc has as that rule's step.** As for Pure's: the rule's statement is
instantiated at the application's terms, its premises are taken, the step is built, and it must conclude what the
statement does at those terms, by ID. A rule missing premises is its closed proof applied to those it has; a rule missing
a term stops the read (`MalformedExport.applicationArity`), and `isa2fol read` proving all 9,420 checks that none does.

| rule | read, at its terms | its step |
|---|---|---|
| `conjI` | `P → Q → P ∧ Q` | `folAndIntro(p, q)` |
| `conjunct1`, `conjunct2` | `P ∧ Q → P`, `P ∧ Q → Q` | `folAndElimL(h)`, `folAndElimR(h)` |
| `disjI1`, `disjI2` | `P → P ∨ Q`, `Q → P ∨ Q` | `folOrIntroL(h, Q)`, `folOrIntroR(P, h)` |
| `disjE` | `P ∨ Q → (P → R) → (Q → R) → R` | `folOrElim(h, k, l)` |
| `impI` | `(P → Q) → (P → Q)` | its premise: `⟹` and `⟶` are one node |
| `mp` | `(P → Q) → P → Q` | `folImpliesElim(h, p)` |
| `FalseE` | `⊥ → P` | `folBottomElim(h, P)` |
| `allI` | `(∀x. P x) → (∀x. P x)` | its premise: `⋀` and `∀` are one node |
| `spec` | `(∀y. P y) → P x` | `isaAllElim(h, x)`: Fol's `forall_elim` at a variable, Reify's instance at a compound term |
| `exE` | `(∃x. P x) → (∀x. P x → R) → R` | `isaExElim(i, …)`: the minor premise at the witness, applied to its hypothesis |
| `refl` | `a = a` | `isaReflexive(a)`: Logic's, base's `eq_refl` (step 2) |
| `eq_reflection` | `x = y → x = y` | its premise: `≡` at `i` is `=` |

The steps the reader now writes become both dialects, as `iff_intro` and `iff_elim_l` did for Pure's `equal_intr` and
`equal_elim`: `and_intro`, `and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`, `or_elim`, `bottom_elim`. No pass owns
them. A citation of one of these rules is then never read; Logic keeps its row, unbuilt.

**2. The class premise of a rule at `[i]` is not the step's.** `refl`, `subst`, `allI`, `spec`, `exI`, `exE` and
`eq_reflection` are stated at `'a :: term`, and the export makes the class their first premise, `OFCLASS('a, term) ⟹ …`
(§4.3a 5): an application at `[i]` takes the class's discharge first. The kernel's step takes the logical premises only —
the guard its `forall_elim` needs is Fol's (R3) — so the reader reads the application past its discharge and does not read
the discharge. ⚠ This is not the removed class drop: a theorem's own class premise, its assumption and the discharges of
its citations stay as Isabelle states them, stated by the class's definition since "OFCLASS — a class's membership by
its definition".

**3. `classical` and `iff_reflection` are read as isa steps, Logic's after Expand.** Their statements hold IFOL's `¬` and
`⟷`, which are defined: the reader keeps them and Expand unfolds them, `¬P` to `P ⟶ False` and `P ⟷ Q` to
`(P ⟶ Q) ∧ (Q ⟶ P)`. Their kernel step exists over the unfolded form only, so the reader reads each application as one
isa step, as it reads Pure's `reflexive` — `isaClassical(P, h)` concluding `P`, `isaIffReflection(P, Q, h)` concluding
`P ↔ Q` — and Logic makes it the kernel's step: `classical_absurd` over `h : (P → ⊥) → P`, and `iff_intro` of
`h : (P → Q) ∧ (Q → P)`'s two conjuncts. Alternative: base proves each as a schema, cited as `subst` cites `class_subst`;
S4's "never a substitution into a translated rule" would then need these two as its exception.

**4. `exI` stays a citation, Logic's unbuilt: its step needs its body.** The IR's `isaExIntro(p, x)`, as fol-zfc's
`exists_intro`, abstracts every occurrence of its witness, so `∃y. y = x` from `x = x` is not one step: the step must
take `P`, which the application has. That design waits — an ∃-intro carrying its body, written as base's schema
`ex_intro [P(1)]` at the body, then `forall_elim` at the witness, is one candidate. Nothing is lost meanwhile: `exI`
is stated at `'a :: term`, so its uses stand in theorems over `'a`, read at `i`, whose own class premise holds them back.

**5. `subst` stays base's `class_subst`** (step 2, decision 3): fol-zfc has no step for it, and its application at a λ
is an instance at a class type. Its citation keeps the axiom's statement, class premise included, stated by the class's
definition ("OFCLASS — a class's membership by its definition"); its λ waits on step 3.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | an application of a rule of 1 as its step, of `classical` and `iff_reflection` as their isa step, each concluding the rule's statement at its terms by ID; a rule at `[i]` without its class's discharge | an export of one build |
| Logic | `isaClassical` and `isaIffReflection` as the kernel's steps | Expand's row: `¬` and `⟷` unfolded |
| Fol, Reify | `isaAllElim` and `isaExElim` at `i` as today, at a compound term too | — |

**Tests, written first.**
- `LogicRuleTests` (Reader), over an export stating the rules as `IFOL.thy` and `FOL.thy` do: each propositional rule
  applied is its step, and `conjI` missing its premises is its closed proof, the same node
  (`aPropositionalRuleAppliedIsItsStep`); `allI`, `spec`, `refl` and `eq_reflection` at `[i]` are their steps past a
  discharge the reader would refuse if it read it (`aQuantifierOrEqualityRuleAtIIsItsStepPastItsClassDischarge`); `exE`
  is an `isaExElim` with no citation left; `classical` and `iff_reflection` are their isa steps; `exI` and `subst` stay
  citations; a rule missing a term stops the read.
- `PatternTests`: the seven steps are both dialects; `isaClassical`, `isaIffReflection` are isa. `TableTests`: their
  conclusions, and `classical`'s refusal of a premise concluding something else.
- `LogicTests`: `isaClassical` and `isaIffReflection` after Expand are the kernel's steps, concluding as read.
- `PlanTests`: the ownership rows; `conjI`, `disjE` and `classical` as the reader reads them lower through the plan, and
  the kernel proves the three (`theLogicsRulesReadAsStepsAreLoweredAndProved`).

**Built.** Reader: `Reader.pure` is `applied`, reading Pure's seven (`PureRule`) and the logic's sixteen (`LogicRule`, from
`Axiom` by one exhaustive switch, `nil` for `subst`, `exI` and ZF's) by one construction; `logicStep` builds each step.
IR: `isaClassical(P, h)` and `isaIffReflection(P, Q, h)`, the reader's, their conclusions at `intern`; `and_intro`,
`and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`, `or_elim` and `bottom_elim` in the both-dialects group. Logic:
`classical`'s reductio and `iff_reflection`'s `iff_intro`.

**Decisions made in the build**, for the user's review:
1. **A leading class premise is skipped for every rule**, by one loop over the statement: only the logic's rules at `[i]`
   have one, Pure's none.
2. **`exE` is always its closed proof, applied to its premises**: its minor premise stands under the witness's binder,
   and built at a premise holding hypotheses it would be read under one binder too many. Logic's `classical` is likewise
   closed over `h`'s statement and applied to `h`, its reductio binding `¬A`.
3. **Every step's conclusion is checked against the statement at its terms, by ID, on both routes** — the closed one,
   Pure's included, was not.
4. **The reader's and the census's tests of a cited axiom's class discharge cite a theory axiom, `T.reflAx`**, stated as
   `refl` is: `refl` is now read as a step, so it no longer exercises a citation's discharge.
- ⚠ Rule 13 struck in the build: `concluding(conclusion, try ruleStep(…))` read a copy of the reader taken before the
  step was interned — index out of range on every new step. The step is bound first.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export`: all 9,420 proved, 66.1 s — no rule
misses a term. `lower data/zf_export --emit DIR`: 5:10, peak 12.9 GB; read 65.8 s, lowered 55.2 s, emitted 188.6 s. Then
`scripts/check-unit.sh DIR`: 9.3 s, peak 543 MB):
- **The kernel proves the unit**: 4 parts, each exit 0 and empty stderr; claims 1,326 of 1,326, schemas 0 of 0.
- **Nothing more lowers**: 8 named theorems and 1,755 other statements, refused as before ("Removed", Measured). The
  logic's own facts are proved through unnamed boxes: `IFOL.conjunct1` (`IFOL/proofs/246`) is box 228 at `P` and `Q`, and
  box 228 is the axiom at its terms, now `and_elim_l`. The reader inlines the box, so its `⋀P ⋀Q`, instantiated at once,
  is `schema_inst` on no citation: a letter off its spine — what the removed reduction absorbed. Every citer of a fact
  falls with it (`FOL.ccontr` 57, `IFOL.TrueI` 51, `IFOL.conjunct1` 6 named theorems).
- `SOURCE_SURFACE.md` and `CLOSURE.md` regenerated: the sixteen rules' citations leave the surface (1,503 patterns to
  1,497) and the closure's axioms, their steps entering the surface in their place.
- ⚠ **A BOX IS AN UNNAMED THEOREM**: the `⋀P` at its top, which Isabelle instantiates by substitution, is schematic by
  S4's own test, yet the reader's inlining puts it inside a proof. How a box binding propositions is read is boxes' own
  design ("Logic", point 3) — decided in "Boxes binding a proposition, read as schemas", below.

### Boxes binding a proposition, read as schemas  **[DECIDED 2026-10-16 (user: "make them schema, give them a name"), its three decisions delegated; BUILT 2026-10-16, its decisions for the user's review — `Sources/Reader/Reader.swift`, `Sources/IR/Legalize.swift`, `Table.swift`, `Sources/FolDialect/Emit.swift`, `Sources/Lowering/Facts.swift`, `Sources/isa2fol/main.swift`, `Lower.swift`, `SurfaceReport.swift`]**

**The step.** A box is a theorem a proof cites by its serial, its proof a file of its own (`ZConstp`, §4.3b). `thms` names
some; the rest, the unnamed boxes, the reader inlines: their closed proof, read at the citation's types. A box binding a
proposition is a statement with its `⋀P` at the top, schematic by FOUNDATION S4's own test; inlined, the `⋀P` stands
inside its citer's proof, and its instance is `schema_inst` on no citation — a letter off its spine. The proofs are in
the boxes: 8,934 of the 9,420 named proofs are a box applied, and the 9,420 reach 961 boxes with a free proposition, 939
of them with no type variable (a throwaway count over the export's files). Decided (user, 2026-10-16): such a box is a
schema of the unit, and it has a name.

**The problem, in target text.** `IFOL.conjunct1` is box 228 at `P` and `Q`, and box 228 the axiom at its terms:

```
Isabelle   IFOL.conjunct1 = box228 · P · Q          box228 = conjunct1 · P · Q        P Q :: o, ⋀-closed
read now   ⋀P Q. (⋀P' Q'. λh. and_elim_l h) · P · Q    the box's ⋀ over propositions inside conjunct1's proof
wanted     schema IFOL.BOX_… [A0(0), A1(0)]: ((A0 & A1) -> A0)          proved by and_elim_l
           schema IFOL.conjunct1 [A0(0), A1(0)]: ((A0 & A1) -> A0)      proved by schema_inst IFOL.BOX_… { A0: A0, A1: A1 }
```

**1. A box whose statement binds a proposition on its spine is a statement of the unit, cited as a named theorem is:**
`use(.theorem(name), types, root)`. Its spine is the one emission reads a schema's letters from — one function,
`spineLetters`, IR's, for both — so it is exactly a box emission writes as a `schema`. Every other box is inlined as now:
its `⋀` over objects instantiated at once is `forall_intro` then `forall_elim`, which fol-zfc has.

**2. Its name is `<theory>.BOX_<fingerprint of its proof>`**: its theory's base name, as Isabelle qualifies the theory's
facts, and its proof's content, as `EX_…` and `UNIQ_…` are named — never its serial, which names a box only within one
build (§4.6 R2). The proof concludes its statement by ID, so a name is one content: two such boxes in one theory are one
statement.

**3. It is read as a named theorem is**: at its own type variables, at `i` when each is restricted to `term` (Step 1),
cited at its citation's types. Its theory is its file's: emission places it in that theory's part, a `schema`, cited by
`schema_inst`.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | a box binding a proposition on its spine as a citation of its name and a statement of the unit, proved; every other box inlined at its citation's types | an export of one build |
| Logic, Emit | unchanged: a `⋀P::o` on a statement's spine a schema letter, its instance `schema_inst` on the citation (Logic, 1–3) | — |

**Tests, written first.**
- `ProofReaderTests`: a box binding a proposition is a citation of its name, and the same box at another serial is the
  same name (`aBoxBindingAPropositionIsCitedByItsContentsName`); a box binding none stays inlined (`anUnnamedBoxIsInlined`).
- `UnitTests`: the unit holds such a box as a statement of its theory (`theUnitHoldsABoxBindingAPropositionInItsTheory`).
- `PlanTests`: a theorem proved through such a box lowers to `schema_inst` of the box's schema, and the kernel proves both
  (`aTheoremProvedThroughABoxIsASchemaInstanceOfItsSchema`).

**Built.** Reader: `claim(_:)` names every theorem a proof cites — a named one by `claimName`, a box binding a proposition
by its content, any other box `nil`, inlined; a citation is built the one way from that name. IR: `spineLetters`, from
emission's, and the fingerprint's text, from Lowering's (D3: the reader uses both now). Logic, Fol, Expand and emission
are unchanged.

**Decisions made in the build**, for the user's review:
1. **`prove` is memoised per instance**, replacing the box memo: a box binding a proposition is read to be named, then as
   the unit's statement — once.
2. **A name keeps the first theorem given it** (`citedAs`): two boxes of one content are then one statement that the
   unit and the census read alike. It kept the last, and `cited` the first: one name, two theorems, silently.
3. **`spineLetters` passes `ifolAll` at any type, counting those at `o`**: the reader's statements bind objects with
   `ifolAll`, lowered ones with `folForall`.
4. **`read` and `lower` count the boxes cited apart** from the named theorems cited outside the ZF sessions, and the
   surface's population note says a box binding a proposition is a theorem cited.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export`: all 9,420 proved, and the 200
named theorems and 956 boxes binding a proposition they cite, 76.6 s. `lower data/zf_export --emit DIR`: 5:30, peak
13.2 GB; read 73.6 s, lowered 59.4 s, emitted 195.7 s; two runs emit byte-identical units. Then `scripts/check-unit.sh
DIR`: 9.3 s, peak 543 MB):
- **The kernel proves the unit**: 8 parts, each exit 0 and empty stderr; claims 1,326 of 1,326, **schemas 28 of 28** —
  the first: `IFOL.conjunct1`, `conjunct2`, `conjI`, `disjI1`, `disjI2`, `disjE`, `impI`, `mp`, `FalseE`,
  `iff_reflection`, `strip.1`, `FOL.classical` and `ZF_Base.strip.1`, each through its box, and the boxes.
- **9 named theorems lowered** (8), `ZF_Base.strip.1` the new one; the unit holds 194 theorems cited outside the ZF
  sessions and 951 boxes. A named theorem stops at its box now where it stopped inside its proof: refused at no owner
  6,722 (7,176), logic 1,258 (1,089), a letter off its spine 12 (40), a refused citation 1,419 (1,107).
- **The logic's facts stop at S4's other pieces** (a throwaway diagnostic following each refused citation down): `TrueI`,
  `notE`, `notI`, `iffI`, `iffD1` at a function of propositions, `isaAbs(o, body: o)` and `isaCombination((o => o), o,
  o)`, where a proof rewrites under `¬`, `⟷` or `True`; `FOL.ccontr` through `Pure.protectD` at a letter off its spine,
  the `⋀A` Expand's reflexive step for `Pure.prop_def` binds inside a proof; `spec` and `allE` at `isaOfClass(i)`.
- `SOURCE_SURFACE.md` regenerated: 1,497 patterns to 1,502 — five binders over a function of propositions, now at a
  box's statement's top as well as in its proof (`ifolAll((o => o), body: o)`, 7,819 theorems). `CLOSURE.md` unchanged.

### Functions of propositions and the bound `⋀P` — S4's truth set, applied  **[AGREED 2026-10-16 (user: "Agree to all, include the bound ⋀P"; the reader's kinds in place of position, "yes"); BUILT 2026-10-16, its decisions in the build for the user's review — `base/tiers/truth`, `Sources/Lowering/Truth.swift`, `Logic.swift`, `Base.swift`, `Sources/Reader/Terms.swift`, `Reader.swift`, `Constants.swift`, `Statements.swift`, `Sources/IR/Node.swift`, `Pattern.swift`, `Table.swift`, `scripts/check-base.sh`]**

**The step.** A function of propositions is a value at `o⃗ ⇒ o`. The reader meets one wherever Isabelle rewrites under
a proposition: `Trueprop`, erased where applied, stands unapplied as `λP. P`; `≡` at `o` as `λP Q. P ↔ Q`; a
connective's section as a λ over its open operand. Since "Removed" each piece at such a type is Logic's, unbuilt, and
they stand in nearly every named theorem's closure (`SOURCE_SURFACE.md`): `isaAbs(o, body: o)` 8,828, `isaAbs(o, body:
(o ⇒ o))` 8,409; `isaCombination` at `o ⇒ o` 8,432 and at `o ⇒ (o ⇒ o)` 8,323; `isaReflexive` at the two 8,170 and
8,323; `isaTransitive` 7,819 and 7,841; `Pure.eq` 8,473 and 8,099. FOUNDATION S4 renders `f ≡ g` at `o ⇒ o` as
`∀E. E ⊆ {∅} → (f*(E) ↔ g*(E))`.

**The problem, in target text.** `TrueI`'s proof unfolds `True_def` under `Trueprop`:

```
Isabelle   combination (reflexive Trueprop) True_def        ⊢ Trueprop True ≡ Trueprop (False ⟶ False)
read       R = isaReflexive(λP. P)                          ⊢ (λP. P) ≡ (λP. P)       at o ⇒ o: no formula
           isaCombination(o ⇒ o, R, q)                      ⊢ A ↔ B                   q : A ↔ B, β-reduced
wanted     R = ∀E. set(E) → truth(E) → (holds(E) ↔ holds(E))     iff_refl under the binder and its premises
           A ↔ B: truth_EX at A opened to E; R at E; holds(E) ↔ A, then holds(E) ↔ B by q, under λP. P's body
```

**1. FOUNDATION first.** S4's sentence on a function of propositions gains three and is corrected once:
- applied to truth sets, a function of propositions is its body with each argument read `∅ ∈ Eᵢ`:
  `(λP⃗. φ)*(E⃗) = φ[∅ ∈ E⃗]` — a λ is a wrapper (S1), no class named for an equation;
- at `o⃗ ⇒ o` the equation is pointwise in every argument: `∀E⃗. E⃗ ⊆ {∅} → (f*(E⃗) ↔ g*(E⃗))`;
- `combination` instantiates it at its argument's truth set, then β: `f*(E(a)) ↔ f(a)`, `∅ ∈ E(a)` replaced by `a`
  under `f`'s connectives — the replacement S4 already counts in an instance's twenty steps;
- corrected: "the corpus binds none at a statement's top" held of the named theorems. A box binding a proposition is a
  statement since "Boxes binding a proposition, read as schemas", and seven bind a function of propositions besides —
  those deriving the applied definitions of `IFOL.not_def`, `iff_def`, `FOL.induct_conj_def`, `induct_implies_def`,
  `If`, `bool_of_o` and `is_bool_of_o`, each with its constant as a variable. Bound at a top it is a class variable of
  tuples of truth sets, as at arity ≥ 1 (4).

**2. Base proves the truth set**, a tier `truth` after `primitives` and `pairs`: `holds(E)` (`∅ ∈ E`) and `truth(E)`
(`set(E)` and `E ⊆ {∅}`) by definition, `schema truth_EX [A(0)]: exists E. (truth(E) & (holds(E) <-> A))`, by excluded
middle — `{∅}` if `A`, `∅` if not — from `zero_EX` and `upair_ex`, and `schema weaken [A(0), B(0)]: (A -> (B -> A))`.
It admits nothing. UNIQ waits for a step that meets two namings of one truth set.

**3. Logic's rules, one per piece, at `o⃗ ⇒ o`.** `E⃗` are the pointwise binders, each `∀E` with the premise
`truth(E)` ("The truth set in the target", below). `f*(E⃗)` is `f`'s body at `holds(E⃗)`.

| piece | rule |
|---|---|
| `isaAbs(o, body)` | a wrapper: no node of its own; where it stands it is applied, its body at the argument |
| `Pure.eq` at `o⃗ ⇒ o` | `∀E⃗. truth(E⃗) → (f*(E⃗) ↔ g*(E⃗))` |
| `isaReflexive`, `isaSymmetric`, `isaTransitive` | under `E⃗` and their premises: base's `iff_refl`, `iff_symm`, `iff_trans`, the premises instantiated at `E⃗` |
| `isaCombination(o ⇒ U, p, q)`, `U` = `o⃗′ ⇒ o` | under `U`'s `E⃗′`: `truth_EX` at `a` opened by `exists_elim` (S1 at the site); `p` at `E, E⃗′`; β on each side by the replacement walk, its hole `holds(E)`, its equations `a ↔ holds(E)` and, through `q`, `holds(E) ↔ b`; `iff_trans` |

Each concludes as the table does — `combination` concludes `f(a) ↔ g(b)`, β-reduced — and reads its premises'
conclusions, never their proofs: "Removed" took out the form a consumer reduced by its premise's shape.

**4. Out of scope, each Logic's unbuilt, with what it waits on.**
- A variable at `o⃗ ⇒ o` — the seven boxes' top binder, its application `isaVarApp`, its instance at a λ: the λ's class
  over truth-set records, an instance at a class type (step 3).
- `≡` at `o ⇒ o` used as a function in those boxes, `isaAbs((o ⇒ o), …)` and `isaCombination(((o ⇒ o) ⇒ o), …)`: a λ
  over classes (step 9).
- A function of propositions valued in sets, `If` and `bool_of_o` (step 6).

**5. What it unblocks: the scope, the user's to choose.** By "Boxes…", Measured, `TrueI`, `notI`, `notE`, `iffI` and
`iffD1` hold 3's pieces — but each also cites `Pure.protectD` or `protectI`, both `equal_elim` over `Pure.prop_def · A`,
whose `⋀A` Expand's reflexive step binds inside a proof, refused off its spine; and `notI`, `notE`, `iffI`, `iffD1` cite
`IFOL.not_def` or `iff_def`, whose boxes are 4's. So this step alone moves none of the logic's facts. A `⋀P` bound inside
a proof is S4's other rendering of the same truth set — `∀E. E ⊆ {∅} → θ*(E)`, `P` read `∅ ∈ E`, an instance at `E(φ)`
then β — and built with this step it reuses 2's base and 3's binder and instance: `protectD`, `protectI` and
`FOL.ccontr` would then reach the kernel, and `TrueI` with them (believed from the diagnostic, not run). **Decided
(user): with the bound `⋀P`**, 6.

**6. The bound `⋀P`: Pure's `⋀` over a proposition is a truth set.** A statement's own variables are its letters —
`ifolAll`, `isaAllIntro` and `isaBound` at `o`, as before: its top `⋀`s as Isabelle states them, frees for a theorem
(which the reader closes over), a leading `⋀` chain for an axiom (`IFOL.conjI`: `⋀P Q. P ⟹ Q ⟹ P ∧ Q`, no frees). Pure's
`⋀` over a proposition below that top — `Pure.all` in a formula, `ZAbst` in a proof, and so every `⋀` a definition's body
holds, wherever Expand unfolds it — the reader reads as nodes of its own, and Logic reads them by kind:

| piece | rule |
|---|---|
| `isaPropAll(φ)` | `∀E. truth(E) → φ*`, `φ*` its body with its variable read `holds(E)` |
| `isaPropIntro(p)` | `∀E`-intro of `truth(E) → φ*` from `p*` by base's `weaken` (`A → (B → A)`): no hypothesis is inserted above `p*` |
| `isaPropBound(k)` | `holds(E)` |
| `isaAllElim(p, A)` at `o` | `schema_inst` where `p` concludes a letter — a citation's top; where it concludes a truth set, the instance: `truth_EX` at `A` opened, `p` at `E`, β by the replacement walk, its hole `holds(E)` with equation `holds(E) ↔ A` |

A letter never meets a truth set: every citation instantiates all the propositions among its frees at its head
(358,349 of 358,349 sites, a throwaway count over the export's files; 94 partial ones leave none), and a proof's leading
intros are its statement's letters, the reader closing both over the same frees. ⚠ A citation consumed whole with a
letter left would meet a truth set at its consumer's premise, and the table refuses that step — a stop, named, never a
silent fallback.

**The truth set in the target.** `holds(E)` (`∅ ∈ E`, over base's `zero`) and `truth(E)` (`set(E)` and `E ⊆ {∅}`) are
base's predicates; a truth-set binder is fol-zfc's own `∀E`, its premise `truth(E)` — not a binder at `i` that Fol
guards, as 3 had it: `truth_EX` is base's, fol-zfc, so the `E` it opens has no type of the walk's for Fol to discharge
`set(E)` at. Logic writes the binder, its intro, its instance and `holds` in fol-zfc; Fol meets none of them.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Base | `holds`, `truth`, `truth_EX`, `weaken`, kernel-checked | NBG; `zero_EX`, `upair_ex` |
| Logic | the pieces of 3 and 6 as fol-zfc steps and base's citations, each concluding as the table does; 4's unbuilt | Expand's unfolding; base's `iff_*`, `cong_*`, `truth_EX`, `weaken` |
| Fol | unchanged: it meets no truth-set binder | — |

**Tests, written first.**
- `check-base.sh`: the `truth` tier proves `truth_EX` and `weaken`.
- `ParseTests`: `truth_EX`'s line parses to its letter's binder.
- `LogicTests`: `isaReflexive(λP. P)` concludes `∀E. truth(E) → (holds(E) ↔ holds(E))`; its `combination` with
  `q : A ↔ B` concludes `A ↔ B`; a section of `∧` through two `combination`s at `o ⇒ (o ⇒ o)`; `isaTransitive` at
  `o ⇒ o`; a stated `f ≡ g` at `o ⇒ o` is its pointwise formula.
- `LogicTests` (6): Pure's `⋀` in a premise is `∀E. truth(E) → …`; introduced in a proof and instantiated, the truth
  instance, concluding as read; a citation's letter instance stays `schema_inst`.
- Reader: `Pure.all` and `ZAbst` at `o` below a top are the three kinds, a free proposition the letter
  (`pureAllOverAPropositionIsItsOwnNodeAndAFreeOneTheLetter`, `aMetaQuantifierOverAPropositionIsPuresBoundAll`);
  `TableTests` and `PatternTests` for the three kinds.
- `PlanTests`: `equal_elim (symmetric (combination (reflexive Trueprop) q)) fact` lowers through the plan and the kernel
  proves it; so do Pure's `⋀` introduced and instantiated, in a premise, and `TERM`'s unfolded `⋀C` at one statement's top
  passed to another's premise — the stop's shape; the ownership rows of 3, 4 and 6.

**Built.** Base: the tier `truth` — `holds_def`, `truth_def`, `truth_EX`, `weaken` — kernel-checked, in
`check-base.sh`'s order after `primitives`. Reader: `Pure.all` reads `metaAll`; at `o` below a statement's top it is
`isaPropAll`, `ZAbst` there `isaPropIntro`, their variable `isaPropBound`; the rule reader takes a term at either binder.
IR: the three kinds, isa only, `isaAllElim` eliminating either binder. Lowering: `Truth.swift`'s `Truths` — the pointwise
formula, `reflexive`, `symmetric`, `transitive`, `combination`, the truth instance, and `fill`, a truth variable's
`holds` read as a proposition; Logic's pieces gain `proposition` (the three kinds) and `function` (wrapper, equation,
combination), each read by kind.

**Decisions made in the build**, for the user's review:
1. **The reader decides a letter, never a position after Expand** (agreed in the build, user). Built first by position —
   a `⋀P::o` on its root's leading chain a letter — the corpus run stopped at the table: Expand unfolds `&&&`
   (`⋀C. (A ⟹ B ⟹ C) ⟹ C`) at `FOL.BOX_1e90…`'s top (`PROP (A &&& B)`), putting a `⋀C` on the chain, and a proof passing
   it to `Pure.conjunctionD2`'s premise met both readings of one formula. Position decided one pattern's translation by
   its surroundings (D1); the reader's kinds decide it by the piece.
2. **A statement's top is its leading `⋀` chain as stated**, through `⋀` and nothing else: an axiom's `⋀` after its
   class premise (`exE`'s `R`) is below the top, Pure's, and the rule reader reads a term at it as at a letter.
3. **Expand's per-parameter intros stay letters**: Expand replaces a definition's citation by a proof of the citation's
   own statement, whose binders are the definition's frees. An instance of one inside a proof (`protectD`'s
   `prop_def · A`) stays a letter off its spine until a definition's citation stays a citation — Expand's design, a
   separate step. Built instead as "A definition read at its terms": the definition takes its terms, and no binder
   stands.
4. **`Pure.all` has its own reading, `metaAll`**, apart from `IFOL.All`: no constant's name is compared outside the
   reading table.
5. **Every truth-set construction is built closed over its premises' statements and applied to them**, as `reductio`
   is, its hole's equation a hypothesis rebuilt at each scope (`Frame`): no proof moves under a new binder.
6. **β takes its hole by its two sides** — `holds(E)` and the argument, or the argument and its equal — never by a
   marker in the formula: outside a hole the two sides are one node.
7. **Comprehension's `sides` and `iff` serve Truth too**: one home for an equivalence's sides.

**Measured** (`check-base.sh`: 14 tiers, `truth` Schemas proved 2 of 2. `read`: all 9,420 proved, and the 200 named
theorems and 956 boxes they cite, 73.6 s. `lower data/zf_export --emit DIR`: 5:20, peak 14.4 GB; read 69.6 s, lowered
59.7 s, emitted 189.7 s; two runs emit byte-identical units. Then `scripts/check-unit.sh DIR`: 10.5 s, peak 556 MB):
- **The kernel proves the unit**: 8 parts, each exit 0 and empty stderr; claims 1,433 of 1,433 (1,326), schemas 29 of 29
  (28); 453 `@def`s (439). Newly lowered among the theorems: `IFOL.True_def`, through its box, whose proof rewrites under
  `λP Q. P ↔ Q` at `o ⇒ o ⇒ o` — the first function of propositions in the kernel; the rest are the lemmas of statements
  whose own pieces now pass Logic.
- **Named theorems lowered: 9**, as before. Refused at no owner 6,722 (6,722), logic 1,084 (1,258), a letter off its
  spine 13 (12), a refused citation 1,592 (1,419): a theorem whose own pieces now pass stops at what it cites.
  `IFOL.TrueI` (51 citers) and `FOL.ccontr` wait on decision 3: `protectD` and `protectI` instantiate `prop_def`'s letter
  inside a proof.
- `SOURCE_SURFACE.md` regenerated: 1,502 patterns to 1,505 — the three kinds, in 8,070, 8,070 and 8,067 named theorems'
  closures. `CLOSURE.md` unchanged.

### A definition read at its terms  **[AGREED 2026-10-16 (user), the direction and the node; BUILT 2026-10-16, its decisions in the build for the user's review — `Sources/IR/Node.swift`, `Pattern.swift`, `Table.swift`, `Constant.swift`, `Sources/Reader/Reader.swift`, `Census.swift`, `Sources/Lowering/Expand.swift`, `Sources/isa2fol/SurfaceReport.swift`, `docs/FOUNDATION.md`]**

**The step.** A definition is an axiom, and Expand proves its citation where it stands (Expand, 3). Unfolded it says
`b ≡ b`: Pure's `reflexive`, which Logic already makes base's `iff_refl` at `o`, `eq_refl` at `i`, the pointwise rule at
`o⃗ ⇒ o`. An applied definition's parameters are bound by Expand's `⋀`-intros inside the citer's proof, and at `o` such an
intro is a letter off its spine ("Functions of propositions and the bound `⋀P`", decision 3). Two definitions have one,
both Pure's: `prop_def` (`PROP A ≡ A`) and `conjunction_def` (`A &&& B ≡ ⋀C. (A ⟹ B ⟹ C) ⟹ C`) — of the export's 999
definitions the only ones with a free at `prop` or `o` (a throwaway scan of `theory/axioms`). IFOL's, FOL's and ZF's
meta-level ones are `c ≡ λx⃗. b`, with no parameter. In the proof term the axiom and its terms are one application, as a
rule's are ("The logic's rules read as steps"): read as one piece, nothing is bound.

**The problem, in target text.** `Pure.protectD` is box 18 at `A`, box 18 is box 16 at `A`, and box 16 cites the axiom:

```
Isabelle   box 16 = λA. equal_elim · PROP A · A ∙ (prop_def · A)       ⊢ ⋀A. PROP A ⟹ A
read       isaAllElim(use(definition prop_def), A)                       ⊢ PROP A ≡ A
Expand     isaAllElim(isaAllIntro(o, reflexive(A′)), A)                  prop_def's ⋀A′ inside the box's proof
Logic      schema_inst on an intro, not on a citation                    refused: a letter off its spine
wanted     schema Pure.BOX_… [A0(0)]: (A0 -> A0)
               _0 = assume A0
               _1 = schema_inst iff_refl { A: A0 }
               _2 = iff_elim_l _1, _0
               _3 = implies_intro _2
```

**Decided (user): no schema and no lemma for a definition.** A schema `Pure.prop_def`, derived from the axiom, would
restate base's `iff_refl`; one written into base would key on a name. The definition's citation is `reflexive` at its
terms, whose helpers are base's. One rule for every definition, today's the case of no terms:

| piece | rule |
|---|---|
| a definition at no terms: IFOL's, FOL's, ZF's meta-level | Expand: `reflexive(λx⃗. b)`, as now |
| a definition at its terms: `prop_def · A`, `conjunction_def · A · B` | Expand: `reflexive(b[a⃗])` |
| `isaReflexive` at `o`, `i`, `o⃗ ⇒ o` | Logic, as now: `iff_refl`, `eq_refl`, pointwise |
| a definition at a type variable (`term_def` at `['a]`) | no owner: decision 4 |
| a ZF definition at the object level | read at its terms too, no owner: step 5 |

**1. The node** (agreed). `isaDefinition(String, of: Defined, [IRType], NodeID, args: [NodeID])`: the axiom, its
constant, its type arguments, its statement at them — closed, as `use` holds a statement — and the terms its application
has, in order. It concludes the statement instantiated at the terms, by the table's one instance, which `isaAllElim`
uses; isa only. It replaces `use(.isaDefinition…)`, and `Cited.isaDefinition` goes: every definition's citation is this
node, at no terms for the `λ`-forms.

```
before   PAxm prop_def · A  →  isaAllElim(use(.isaDefinition("Pure.prop_def", of: prop), [], ⋀A. PROP A ≡ A), A)
after    PAxm prop_def · A  →  isaDefinition("Pure.prop_def", of: prop, [], ⋀A. PROP A ≡ A, args: [A])
```

- Its pattern is `isaDefinition(Family, Level, [IRType], args: [IRType])`, owned as the `use(definition …)` rows are now:
  Expand's where `unfolds(family, level)` and no type variable, no owner otherwise.
- Expand's rule: `reflexive(b[a⃗])`, under a `⋀`-intro for each parameter the application leaves.
- The reader, in a proof's spine, gives a definition its leading terms, as `applied` gives a rule its own.
- Not term arguments on `use`: a citation would then have two ways to be instantiated, its arguments and `isaAllElim`
  (rule 4). Not a node around `use(definition …)`: Expand rewrites the inner citation first, and the outer would read a
  rewritten child.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | every definition's citation as `isaDefinition`, with the terms its application has | an export of one build |
| Expand | `reflexive` at the unfolded instance, a `⋀`-intro for each parameter left | its definitions, as now |
| Logic, Fol, emission | unchanged | — |

**FOUNDATION first.** 3b's mapping gains a row: an application of a definition whose constant is unfolded is `reflexive`
at its terms.

**Tests, written first.**
- `TableTests`: the node concludes its statement at its terms, and at no terms the statement; a term of the wrong type
  is refused.
- `ProofReaderTests`: `prop_def · A` reads as the node at `[A]`; `not_def_raw` at no terms; no proof holds a `use` of a
  definition.
- `ExpandTests`: the node at `[A]` becomes `reflexive(A)`; at no terms `reflexive` of the `λ`, as now.
- `PlanTests`: a box citing `prop_def` at its letter lowers to `iff_refl`, and the kernel proves it; the ownership rows.

**Built.** IR: `isaDefinition`, isa only, concluding its statement at its terms by `Table`'s one instance, which
`isaAllElim` shares (a term of its parameter's type, a function-typed one an abstraction); `Cited.isaDefinition` and
`CitedKind.isaDefinition` gone. Reader: a proof's spine headed by a definition gives it its leading terms, beside
`applied`'s rules. Expand: `reflexivity(d, at: args)`. FOUNDATION 3b: the row.

**Decisions made in the build**, for the user's review:
1. **The census counts a definition apart from `Cited`** (`Census.definitions`, keyed by `CitedDefinition`, the axiom's
   name and its constant): `Cited` is what a `use` cites, and a definition is no longer one. `CLOSURE.md` reads it.
2. **The reader takes terms while the statement has a leading binder**: a definition has no premise, so an argument after
   them is applied by the spine's general loop, and the table refuses it (an equation is no implication).
- ⚠ Rule 13 struck in a test: `t.conclusion(of: try t.intern(…))` read a copy of the table taken before the node was
  interned. The node is bound first.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export`: all 9,420 proved, and the 200
named theorems and 956 boxes binding a proposition they cite, 73.4 s; 6,388,887 nodes (6,389,466). `lower data/zf_export
--emit DIR`: 5:40, peak 14.9 GB; read 74.2 s, lowered 64.9 s, emitted 199.5 s. Then `scripts/check-unit.sh DIR`: 10.3 s,
peak 556 MB):
- **The kernel proves the unit**: 38 parts (8), each exit 0 and empty stderr; claims 1,485 of 1,485 (1,433), schemas 104
  of 104 (29); 453 `@def`s.
- **Named theorems lowered: 63** (9). The 54 new: 51 `mutual_induct`s, whose statements and proofs hold `&&&` and
  `PROP`, `Arith.iff_cong2`, `func.basic_monos.2` and `.4`. Of the theorems cited outside the ZF sessions, Pure's
  `protectI`, `protectD`, `conjunctionI`, `conjunctionD1`, `conjunctionD2` and `meta_mp`, IFOL's `TrueI`, `rev_mp`, `impE`,
  `conjE`, `atomize_imp`, `atomize_conj`, FOL's `ccontr`, `imp_elim`, `conj_mono`, `True_implies_equals` reach the kernel.
- Refused at no owner 6,722 (6,722), logic 1,084 (1,084), a letter off its spine 13 (13), a refused citation 1,538
  (1,592), led by `Formula.satisfies_DEF` 63; `IFOL.TrueI` (51) no longer among them. The 13 off their spine are no
  definition's: `DC.imp_DC0.lemma2`, `lemma3`, `simplify_recursion`, `HH.HH_Hartog_is_x`, `Formula.lt_LsetI`,
  `Multiset.irrefl_Memrel`, `PropLog.Imp_Fls`, `Group.subgroup_nonempty`, `Cardinal.cardinal_lt_imp_lt`,
  `Diff_sing_eqpoll`, `OrderType.Ord_iso_implies_eq`, `Univ.VfromI`, `VsetI` (a throwaway print in `lower`, not kept);
  their source is not traced.
- `SOURCE_SURFACE.md` regenerated: 1,505 patterns to 1,553 — the eleven `use(definition …)` rows become `isaDefinition`
  rows at their terms' types: `prop_def` at `[o]` 8,174, `conjunction_def` at `[o, o]` 7,700, ZF's object-level
  definitions at each applied shape; `isaAllElim(o, i)` 8,958 to 8,778. `CLOSURE.md` unchanged.

### OFCLASS — a class's membership by its definition, and a generic theorem in place  **[AGREED 2026-10-16 (user), the three decisions, 2 revised: a definition defines what its left side is; BUILT 2026-10-16, its decisions in the build for the user's review — `Sources/IR/Constant.swift`, `Node.swift`, `Pass.swift`, `IRType.swift`, `Sources/Reader/Reader.swift`, `Statements.swift`, `Terms.swift`, `Export.swift`, `Census.swift`, `Sources/Lowering/Expand.swift`, `Logic.swift`, `Instance.swift`, `Congruence.swift`, `docs/FOUNDATION.md`]**

**The step.** A ZF proof cites the logic's rules and theorems at `i`, each stated over a type of class `term` with the
class its first premise (§4.3a 5), and discharges the premise with `ZF_Base.arity_term_i`. `isaOfClass(i)` has no owner
("Removed"), and 5,601 of the 6,722 named theorems refused at no owner hold it. Two pieces, from the export:

```
IFOL.term_class_def    OFCLASS('a, term) ≡ (⋀P::prop. P ⟹ P)                  the class's definition, an axiom
IFOL.term_class.intro  OFCLASS('a, term)      'a unrestricted                   equal_elim (symmetric term_class_def['a]) (⋀P. λH. H)
ZF_Base.arity_term_i   OFCLASS(i, term)                                         term_class.intro at [i]
a ZF proof             IFOL.sym · a · b ∙ arity_term_i ∙ h                      the class premise, discharged
```

- **(A) The formula.** FOUNDATION S4: `OFCLASS(T, c)` is its definition at `T`, `⋀P::prop. P ⟹ P`, a truth set:
  `∀E. truth(E) → (holds(E) → holds(E))`. Nothing provides the definition: the reader reads `OFCLASS` as `isaOfClass`,
  never as the constant `IFOL.term_class` its definition defines, so it hands Expand no definition of it.
- **(B) What proves it.** `arity_term_i` is `term_class.intro` at `[i]`, a theorem whose `'a` no class restricts:
  `use(theorem, [i], o)`, no owner — decision 4's deferred half. `arity_term_i` stays refused, and every proof
  discharging through it falls with it; (A) alone moves the 5,601 from no owner to a refused citation (expected).

**The problem, in target text.**

```
read now   isaOfClass(i)                                      no owner
           use(theorem IFOL.term_class.intro, [i], o)        no owner: decision 4
wanted     claim ZF_Base.arity_term_i: forall E. (truth(E) -> (holds(E) -> holds(E)))
               iff_symm and iff_refl at the definiens, iff_elim_l of the truth set's intro by weaken
           a premise OFCLASS(i, term) of IFOL.sym, read at i:  (forall E. (truth(E) -> (holds(E) -> holds(E)))) -> …
```

**1. `OFCLASS(T, c)` is unfolded by its class's definition at `T`** (FOUNDATION S4) — Expand's, as the logic's defined
constants are: the definition is IFOL's. `isaOfClass(T)` at a type with no variable has Expand's rule; at a type
variable no owner (decision 4).

**2. A definition defines what its left side is: a constant, or a class's membership.** `Definition` knew only
constants, and the export also defines a class's membership: `IFOL.term_class_def`'s left side is `OFCLASS('a,
IFOL.term)`. Keyed by the constant `theory/constdefs` names, `IFOL.term_class`, the class's definition had two
identities — that constant, which no node holds (§4.3a 5a), and the class, reached through a mark: a bridge, a patch —
and a lossy key: the constant's type, `'a itself ⇒ prop`, reads `o` at every `T`, so `OFCLASS(i, term)` and
`OFCLASS('a, term)` shared one. The reader reads what a definition axiom defines from its left side, never from a name:
`c(x⃗)` the constant `c`'s, `OFCLASS('a, c)` the class `c`'s membership, of no parameter. It is a typed value (I1), on
`Definition` and on the citation `isaDefinition`.

```
before   Definition(constant: Defined, type, axiomTypes, parameters, definiens)
after    Definition(defines: Definiendum, type, axiomTypes, parameters, definiens)
         enum Definiendum { case constant(Defined), ofClass(String) }

term_class_def's left side     OFCLASS('a, IFOL.term)   →  defines .ofClass(IFOL.term), no parameter, type o
isaOfClass(i, IFOL.term)               finds  (.ofClass(IFOL.term), [i])   →  unfolded (1)
term_class_def at [i], cited           finds  (.ofClass(IFOL.term), [i])   →  reflexive, "A definition read at its terms"
```

`IFOL.term_class` is never a node. The reader provides a class's definition at each type its membership occurs at, as
it provides a constant's at each type it is used at: in ZF that is `i` alone — the export's only arity is
`ZF_Base.i :: IFOL.term` (`ZF.ZF_Base/theory/arities`), and once 3 puts `term_class.intro` in place at `[i]`, every
`OFCLASS` lowered is `OFCLASS(i, term)`. A declared class no definition axiom defines is malformed.

**3. A named theorem read at its own type variables, cited at a type instance with no variable, is put in place there:
its proof read at the citation's types, as an unnamed box is** — decision 4's candidate ("The meta level, lowered", 4:
"put a generic proof in place at the type of its use — no new name"). By S4's test, only when it binds no proposition on
its spine at that instance: inlined, a letter would stand in the citer's proof. One that binds one (`FOL.meta_simps.1`,
`(⋀x::'a. PROP P) ≡ PROP P`) stays `use(theorem, [i], o)`, no owner: its instance as a named statement is a later step.
The same rule puts in place `term_class.intro` and the fact `term_class_def` at `[i]`, and, where they bind none,
`Inductive.def_trans`, `ZF_Base.split_def`, `pair.split` and `Pure.meta_spec` at the types they are cited at.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Reader | what a definition axiom defines, read from its left side; a class's definition at each type its membership occurs at; a named theorem read at its variables, cited at a type with none and binding no proposition on its spine there, in place | an export of one build |
| Expand | `isaOfClass(T, c)` unfolded by `c`'s definition at `T`; a citation of the definition, `reflexive` | the class's definition at every `T` it meets |
| Logic, Fol, emission | unchanged: the definiens is a truth set, built | — |

**FOUNDATION first.** S4 renders `OFCLASS` already. §3b's mapping gains a row: a theorem polymorphic in a type no class
restricts, cited at a type, is its proof at that type, in place — the target has no type. Its census note keeps its
meaning — a sort constraint is trivially true in ZF, where `term` holds `i` alone, and needs no guard — and says how:
stated, by its definition (S4), never stripped. §4.3a 5's last paragraph, which had lowering drop `OFCLASS` as
metadata, says the same.

**Tests, written first.**
- `UnitTests`: the unit holds `term`'s definition at `i`, the class's, of no parameter, its definiens `⋀P. P ⟹ P`.
- `ProofReaderTests`: a citation of the class's definition defines the class; a named theorem at an unrestricted `'a`
  cited at `[i]` is its proof at `i`, in place, with no `use` of it; one binding a proposition on its spine there stays
  its citation.
- `ExpandTests`: `isaOfClass(i)` unfolds to the class's definiens; a citation of the class's definition at `[i]` is
  `reflexive`.
- `PlanTests`: `arity_term_i`'s shape lowers and the kernel proves it, and a theorem discharging a class premise with
  it; the ownership rows `isaOfClass(i)` (expand, rule) and `isaOfClass('a)` (none).

**Built.** IR: `Definiendum` — a constant, or a class's membership — on `Definition` and on `isaDefinition`; a class a
typed value, `TypeClass`, in `isaOfClass` too. Reader: what a definition axiom defines, read from its left side
(`definiendum`); a class's definition at each type its membership occurs at (`definition(of:at:)`, the unit's walk); a
named theorem read at its variables and cited at a type with none, binding no proposition on its spine there, its proof
there in place (`head`). Expand: `isaOfClass(T, c)` at a type with no variable unfolds to `c`'s definiens at `T`, keyed
`(.ofClass(c), [T])`. FOUNDATION: §3b's row; the census note and §4.3a 5's last paragraph say stated, never dropped.

**Decisions made in the build**, for the user's review:
1. **A class is a typed value with its family, `TypeClass(family, name)`, in `isaOfClass` and in `Definiendum` alike** —
   agreed as `ofClass(String)`. `isaDefinition`'s pattern carries the family and level of what it defines; a class's
   family is the one whose theory declares it (`theory/classes`), its level meta, a membership being a proposition. So a
   citation of `term_class_def` is `isaDefinition(ifol, meta, [i], args: [])`, a constant's definition's pattern, and its
   rule `reflexive`.
2. **The class's definition axiom is found among the exported definition axioms by its left side**, every one's read
   once when a class's is first asked for (`Reader.axiom(defining:)`); two defining one class are malformed
   (`duplicateDefinition`), none `undefinedClass`. A class membership is never a name: no `_class` suffix is read.
3. **Expand keys a definition by what it defines at its axiom's types**, `(Definiendum, axiomTypes)`; a constant's type
   leads to that key. The key a constant had, its type, read `o` at every `T` for the class.
4. **`mentionsTypeVariable` moved to IR** (D3): the reader's test for "a type with no variable" and Expand's and Logic's
   ownership read one notion.
5. **The census walks a class membership into its class's definition**, as a defined constant into its own.
6. ⚠ **REIFY'S INSTANCE AT A COMPOUND TERM CONCLUDES THE WALK'S OWN REWRITE OF THE INSTANCE, `walked(_:base:in:)`.** It
   concluded `named(formula:)`, the naming alone — a second, partial copy of Logic's rewrite of a formula, right while
   that rewrite was naming alone. Since "Functions of propositions and the bound `⋀P`" Logic also renders Pure's `⋀` over
   a proposition inside a formula as a truth set, so the instance's two sides differed by that rendering, never by
   naming; no instance at a compound term held one until `OFCLASS`'s definiens, `⋀P. P ⟹ P`, stood in every class
   premise, and the corpus's run stopped (`noCongruence`). The congruence walks a truth set's binder as the `∀` it
   renders: `congForallBare` under `truth(E) → body`. Tests: `aClassPremiseCitedAtACompoundTermIsLoweredAndProved`,
   `aTruthSetHoldingTheInstantiatedVariableIsLoweredAndProvedAtACompoundTerm`, each `noCongruence` before.
7. **A box's name moves with the IR's printed payload**: a box is named by its proof's content (R2), and a definition's
   citation now prints its definiendum, a generic theorem its proof in place — 11 box names give way to 15, 70 boxes to
   74, all proved.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export`: all 9,420 proved, and the 195
named theorems (200) and 956 boxes binding a proposition they cite, 73.6 s; 6,391,760 nodes (6,388,887). `lower
data/zf_export --emit DIR`: 5:59, peak 16.0 GB; read 74.9 s, lowered 77.7 s, emitted 205.6 s; 18,069,345 nodes. Then
`scripts/check-unit.sh DIR`: 11.5 s, peak 514 MB):
- **The kernel proves the unit**: 40 parts (38), each exit 0 and empty stderr; claims 2,222 of 2,222 (1,485), schemas
  110 of 110 (104); 453 `@def`s. `ZF_Base.arity_term_i` is `forall b0. (truth(b0) -> (holds(b0) -> holds(b0)))`, by
  `iff_symm`, `iff_refl`, `weaken` and `iff_elim_l`, as wanted; `IFOL.refl` and `IFOL.eq_reflection` reach the kernel
  with their class premise stated.
- **Named theorems lowered: 65** (63): `ZF_Base.arity_term_i` and `Inductive.refl_thin`. 2,720 statements beside them
  reach fol-zfc (1,979).
- **Refused at no owner 3,702** (6,722), **logic 3,955** (1,084), a letter off its spine 13 (13), a refused citation
  1,685 (1,538). `isaOfClass(i)` leads no list: the 5,601 it held stop at their next piece — Logic's instance at a class
  type, `isaAllElim(o, (i ⇒ o))` 2,820 (step 3), and `use(theorem, [i], o)` 1,627 (1,696), a theorem binding a
  proposition on its spine at `[i]` (`FOL.meta_simps.1`).
- `SOURCE_SURFACE.md` regenerated: 1,553 patterns to 1,573. `use(theorem, [i], o)` in 4,929 closures (7,965): every
  `arity_term_i` holds `term_class.intro` in place; `isaDefinition(ifol, meta, ['a], args: [])` gone (7,965),
  `isaDefinition(ifol, meta, [i], args: [])` 7,966 (7,316); the generic theorems' patterns at `'b` gone (2,386 to 1).
  `CLOSURE.md` unchanged.

### Step 3 — an instance at a class type  **[AGREED 2026-10-16 (user), the six decisions one by one, then reviewed against the principles and proof size: 2 refined, 3 revised; BUILT 2026-10-16, its decisions in the build for the user's review — `Sources/IR/IRType.swift`, `Table.swift`, `Sources/Lowering/Lambda.swift`, `Instance.swift`, `Congruence.swift`, `Facts.swift`, `Terms.swift`, `Scope.swift`, `Classes.swift`, `Logic.swift`, `Fol.swift`, `Reify.swift`, `Graph.swift`, `Plan.swift`, `base/tiers/metafun`, `docs/FOUNDATION.md`]**

**The step.** Logic leaves one piece unbuilt above all: `isaAllElim(o, T)` at an object function type, `iⁿ ⇒ o` or
`iⁿ ⇒ i` — a `⋀`-elimination whose argument is a λ, the only argument the table admits at a function type. Of the named
theorems refused at Logic, 2,820 hold it at `i ⇒ o` and 1,692 at `i ⇒ i`; 617 hold no other unbuilt piece (380 at
`i ⇒ o`, 207 at `i ⇒ i`, 30 at `i ⇒ i ⇒ i`; a throwaway print in `lower`, not kept). One rule for the piece covers every
case: what the λ's body holds, and where the class variable stands in the formula, are other pieces' rules.

**The problem, in target text.** fol-zfc has no λ: `forall_elim` puts a class where Isabelle puts `λx. x ∈ A`, and
Isabelle's conclusion holds the λ's body where the class variable was applied — β, which Isabelle's terms do for free.

```
Isabelle   thm: ⋀P a. P(a) ⟹ P(a)          thm · (λx. x ∈ A)  concludes  ⋀a. a ∈ A ⟹ a ∈ A
fol-zfc    claim thm: forall P. (forall a. (set(a) -> (Pa -> Pa)))
               Pa:  exists t. (set(t) & ((exists z. (set(z) & (zero(z) & snoc(z, z, a, t)))) & elem(t, P)))    ⟨a⟩ ∈ P
```

**1. An instance at a λ is `forall_elim` at the λ's class, then β as proof.** **AGREED 2026-10-16 (user).** (FOUNDATION
S1, "a λ is a wrapper"; "The meta level, lowered": "`⋀`-elim at a λ — `forall_elim` at the λ's class, then β as
proof".) The λ's class at its arguments, `LAMBDA_<fp>` (3), at the λ's free variables, opened, gives a class `K` and β
there; the theorem's class binder is eliminated at `K` (2); at each atom where the class variable stood, β as proof —
the atom at `K` against the λ's body there — carried through the formula by Logic's replacement walk; the instance
concludes the walk's own rewrite of Isabelle's conclusion (`walked`). One rule at every object function type. It is
Lambda's, in the logic pass's walk, as Reify's instance at a compound term is — its frame, with the λ's class where
that has the term's value.

```
LAMBDA_<fp> at A   exists K. forall a. (set(a) -> (Ka <-> elem(a, A)))
exists_elim        K, B
forall_elim        thm at K:  forall a. (set(a) -> (Ka -> Ka))
β at each Ka       B at a:  Ka <-> elem(a, A)
iff_elim_l         forall a. (set(a) -> (elem(a, A) -> elem(a, A)))
```

**2. fol-zfc's `forall_elim` takes Isabelle's class binder as Fol writes it.** **AGREED 2026-10-16 (user); refined at
the review.** `K` is fol-zfc's own class, bound by `LAMBDA_<fp>`'s `∃` as Reify's chains bind every class they name
("One class, one form"). The theorem's binder `⋀P` is isa until Fol writes it — `forall P. ψ` at `iⁿ ⇒ o`,
`forall F. (function(F) -> ψ)` at `iⁿ ⇒ i`. The table admits `forall_elim` at `K` on the isa binder and concludes what
it concludes on the binder Fol writes: `ψ(K)`, and `function(K) -> ψ(K)` at `iⁿ ⇒ i`, whose guard Lambda discharges
from `LAMBDA_<fp>` (3; the guard table: "at a λ, Lambda's"). `schema_inst` takes an isa binder at `o` the same way. The
guard per type — `set` at `i`, `function` at `iⁿ ⇒ i`, none at `iⁿ ⇒ o` — moves from Reify to IR, the lowest component
reading it; and ONE IR function writes a binder's guarded body, which Fol's rendering of the binder and the table's
`forall_elim` both call — two computations of it would diverge as `named(formula:)` did from Logic's rewrite.

```
iⁿ ⇒ o    forall_elim thm, K                         ψ(K)
iⁿ ⇒ i    forall_elim thm, K                         function(K) -> ψ(K)
          implies_elim _, LAMBDA_<fp>'s function(K)  ψ(K)
```

| | before | after |
|---|---|---|
| table | `folForallElim(p, v)`: `p` concludes `folForall(φ)` | also `ifolAll(T, φ)` at an object type: `v` in the guarded body |
| IR | — | the guard per type, from `Reify.guardPredicate`; the guarded body of a binder, from Fol |

Not `isaAllElim` at `K`: the table admits only a λ there, and an instance at a variable would share Lambda's pattern,
`isaAllElim(o, T)`. Not an isa `∃` binding `K` so Fol finds its guard in its context: a class would then have two forms.

**3. β at an atom is the λ's class at its arguments, `LAMBDA_<fp>`, proved once per λ.** **AGREED 2026-10-16 (user);
revised at the review** from `BETA_<fp>` beside `CLASS_<fp>`. Its statement is built from the λ alone (I2): there is a
class whose atom at fresh arguments is the walk's rewrite of the body there — and at `iⁿ ⇒ i`, a function, whose value
at a tuple is the body's value there. At an atom `P(t⃗)` with `t⃗` variables, β is the opened hypothesis at `t⃗`, by ID
(naming commutes with an instance at a variable). Its proof cites `CLASS_<fp>`; `CLASS_<fp>` stays the λ's class
existence, which Reify's chains bind.

```
LAMBDA_<fp>   ∀b0. ∃B1. ∀b2. (∃b3 = ⟨b2⟩. b3 ∈ B1) ↔ b2 ∈ b0                          λx. x ∈ A, folview
   at iⁿ ⇒ i  ∀v⃗. ∃K. function(K) ∧ ∀t⃗. ∀τ = ⟨t⃗⟩. ∀r. apply(τ, r, K) ↔ ⟦r = b(t⃗)⟧
its proof     CLASS_<fp>'s K and definition H; -> open ⟨t⃗⟩ ∈ K, H at the tuple, the tuple's injectivity (TUPLE_INJ_n),
              membership's congruence; <- TUPLE_EX_n, H; at iⁿ ⇒ i FUNC_<fp> and apply_pmem (5)
```

Not `BETA_<fp>` beside `CLASS_<fp>`, as agreed first: the instance never needs `K`'s definition, only β at its atoms;
`BETA`'s citation re-eliminates `v⃗`, `K` and the definition at every atom (about 7 steps against 3, about 430k over the
107,588 atoms, before emission's sharing), its statement restates the definition, and `FUNC_<fp>` was a citation per
instance. Not β open-coded at each atom: the same proof at every atom of every instance of one λ. Not a base schema per
arity, `[A(n)]`: its `->` substitutes the tuple's entries into an uninterpreted `A`, Leibniz's law, which base does not
admit.

**4. β at a compound argument is β at its value, then EX and UNIQ where Isabelle's conclusion names the argument
again.** **AGREED 2026-10-16 (user).** (FOUNDATION S1: "where two forms of one term meet — a hypothesis's and a
conclusion's, a λ's body unfolded at its argument — EX and UNIQ convert between them".) Logic names `P(succ(a))` by
naming `succ(a)` where it stands — its class, the tuple of `a`, its value `r` — and applying `P` to `r`. At `K`, β is
`LAMBDA_<fp>` at the variable `r`, under the argument's naming. Isabelle's conclusion holds the body at `succ(a)`, which
the walk names per occurrence: a body holding its variable once, where naming puts the value (`λx. x ∈ A`), gives that
same formula, by ID; otherwise `succ(a)` stands named twice, or not at all — two forms of one term, which EX and UNIQ of
`succ(a)` convert: the conversion Reify's instance at a compound term makes, with the value `r` as its variable.

```
λx. x ∈ A   atom at K           ∀B0 b1. ∃B2. ZF_Base.succ(B2) ∧ ∃b3 = ⟨b1⟩. ∃b4. (b3, b4) ∈ B2 ∧ ∃b5 = ⟨b4⟩. b5 ∈ B0
            β at b4             ∀b0 b1. ∃B2. ZF_Base.succ(B2) ∧ ∃b3 = ⟨b1⟩. ∃b4. (b3, b4) ∈ B2 ∧ b4 ∈ b0       Isabelle's, by ID
λx. x = x   β at b3             ∀b0. ∃B1. ZF_Base.succ(B1) ∧ ∃b2 = ⟨b0⟩. ∃b3. (b2, b3) ∈ B1 ∧ b3 = b3
            Isabelle's          ∀b0. ∃B1. ZF_Base.succ(B1) ∧ ∃b2 = ⟨b0⟩. ∃b3. (b2, b3) ∈ B1 ∧
                                     ∃B4. ZF_Base.succ(B4) ∧ ∃b5 = ⟨b0⟩. ∃b6. (b5, b6) ∈ B4 ∧ b3 = b6
                                EX and UNIQ of succ(a): the second naming's value b6 is b3
```
(`folview`; `(t, r) ∈ C` is `pmem(t, r, C)`, `∃b = ⟨a⟩` the 1-tuple.)

**5. A function λ's β is about its value.** **AGREED 2026-10-16 (user).** At `iⁿ ⇒ i` an application `F(t⃗)` is a
term, named by its value through `apply` (S5, Isabelle/ZF's `f`a`): `∃τ = ⟨t⃗⟩. ∃r. apply(τ, r, F) ∧ …`. At `K`,
`LAMBDA_<fp>` states the application's value against the body's — the λ's class at `t⃗` has the body's value there. Its
proof reads `apply` as `pmem` where `K` has a value — `apply_pmem`, a base claim, new, from `apply`'s definition — and
`K` has one at every tuple of sets, by its definition and the body's EX. At the atom where `F(t⃗)` stood, `r` meets
Isabelle's body named there: two forms of one term, which EX and UNIQ convert, as in 4.

```
apply_pmem       ∀B0 b1. (∃b2. (b1, b2) ∈ B0) → ∀b2. apply(b1, b2, B0) ↔ (b1, b2) ∈ B0
F(a) ∈ B at K    ∀B0 b1 b2. ∃b3 = ⟨b1⟩. ∃b4. apply(b3, b4, B0) ∧ b4 ∈ b2
Isabelle's       ∀b0 b1. ∃B2. ZF_Base.Pow(B2) ∧ ∃b3 = ⟨b0⟩. ∃b4. (b3, b4) ∈ B2 ∧ b4 ∈ b1          Pow(a) ∈ B
```
(`folview`, at `F := λx. Pow(x)`.)

**6. A class variable inside a λ in a constant's class slot: the slot's class is kept and its definition converted.**
**AGREED 2026-10-16 (user).** Logic names the λ in the slot where it stands, by a class and its definition ("a λ is a
wrapper"); the class variable stands inside that definition, applied to the slot λ's own variables. Isabelle's
conclusion holds the slot λ's body reduced, which the walk names by its own class and definition: the two chains agree
but inside the definitions, where β — 3 at variables, 4 at compound arguments — converts one into the other, the slot's
class the same witness on both sides. Reify's instance at a compound term treats a λ argument holding its variable the
same way.

```
Ball(A, λx. P(x)) at K   ∀B0 b1. ∃B2. (∀b3. b3 ∈ B2 ↔ (∃b4. b3 = ⟨b4⟩ ∧ ∃b5 = ⟨b4⟩. b5 ∈ B0)) ∧
                           ∃B3. ZF_Base.Ball(B3, B2) ∧ ∃b4 = ⟨b1⟩. b4 ∈ B3
Isabelle's, at λy. y ∈ B  ∀b0 b1. ∃B2. (∀b3. b3 ∈ B2 ↔ (∃b4. b3 = ⟨b4⟩ ∧ b4 ∈ b0)) ∧
                           ∃B3. ZF_Base.Ball(B3, B2) ∧ ∃b4 = ⟨b1⟩. b4 ∈ B3
                          B2, the slot's class, kept; inside its definition β at b4
```

**The review** (2026-10-16, the user: against the agreed principles, and proof size). Measured over the read unit (a
throwaway print in `lower`, not kept): 46,219 distinct instances at a function type — 29,569 at `i ⇒ o`, 9,817 at
`i ⇒ i` — 11,948 of them (26%) at an η-expanded class variable `λx⃗. Q(x⃗)`; at most 23,081 distinct other λs; 107,588
occurrences of the class variable in the instantiated formulas, about 2.3 atoms per instance. Each decision keeps D1
(one local rule), D2, D3, I2 and FOUNDATION S1; 4–6 have no cheaper form under S1's per-occurrence naming. Trade-offs:
- **1 — an η-expanded variable pays the whole rule**, where `forall_elim` at `Q` would give Isabelle's formula by ID: about
  12k instances pay a citation, an `∃`-elim and their β reads. Kept: one rule, no shape detected — a size optimization is
  never a translation rule (2026-10-15), and the λ's class is `Q`'s tuples, not `Q`; the closed λ `λQ x⃗. Q(x⃗)` is one
  per type, so its lemma is proved once per type.
- **2 — the table knows how Fol writes a guarded binder**: one IR function, which both call (above).
- **3 — `BETA` beside `CLASS`, or the class at its arguments**: revised to `LAMBDA_<fp>` (above).

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| IR | the guard per type; a binder's guarded body; the table's `forall_elim` on an isa binder at an object type | — |
| Lambda (logic's walk) | an instance at a λ at an object function type, concluding the walk's own rewrite of Isabelle's formula, by ID; `LAMBDA_<fp>`, requested from the λ alone | `LAMBDA_<fp>` proved or refused at its prover; Reify's conversion at a compound term; Logic's replacement walk |
| Lambda's prover | `LAMBDA_<fp>` | `CLASS_<fp>` (the class prover), `FUNC_<fp>` (Reify's), `TUPLE_*` (Tuple's), EX of the body, base's `apply_pmem` |
| Fol | the binder's guarded body from IR | — |
| base | `apply_pmem`, proved in `metafun` | — |

**FOUNDATION first.** §3b's mapping: "`AppT` at a λ (a class type) | `forall_elim` at the λ's class at its arguments,
then β: at each atom, the class's against the body's (S1)". S1 and S5 hold the rest.

**Tests, written first.**
- `TableTests`: `forall_elim` on an isa binder at `i ⇒ o` concludes its body at the variable; at `i ⇒ i`, its guard
  first.
- `FolTests`: Fol writes a binder's guarded body by IR's function, as before.
- `LambdaTests` (Lowering): `LAMBDA_<fp>`'s statement at a predicate λ and a function λ, from the λ alone; its proof, the
  kernel checking it.
- `PlanTests`, each kernel-checked: an instance at a λ at variables (`thm · (λx. x ∈ A)`); at a compound argument, the
  body holding its variable once and twice; at a function λ (`F := λx. Pow(x)`); a class variable in a class slot
  (`Ball(A, λx. P(x))`); an η-expanded variable; the ownership rows `isaAllElim(o, (i ⇒ o))` and `(i ⇒ i)` (logic, rule).
- `base`: `apply_pmem` kernel-checked (`check-base.sh`).

**Built.** IR: the guard per type and a binder's guarded body (`guardPredicate`, `guarded`, `guardedBody`), which Fol's
`∀` and the table's `forall_elim` on an isa binder at an object type both call. Lambda (`Sources/Lowering/Lambda.swift`):
the instance at a λ — `R = ⋀P::T. A(P) → (ψ*(P) ↔ wanted)` proved with `P` Isabelle's typed variable, the walk's hole β
at each unit of `P`, then `forall_elim` at the opened `LAMBDA_<fp>`'s class, its guard and `A(K)` discharged; its prover,
`LAMBDA_<fp>` from `CLASS_<fp>`, `TUPLE_INJ_n`, `TUPLE_EX_n`, and at `iⁿ ⇒ i` `FUNC_<fp>`, the body's EX and
`apply_pmem`. The tests above live in `LambdaTests` (thirteen, each kernel-checked or its refusal named), the table's in
`TableTests`, the ownership rows in `PlanTests`.

**Decisions made in the build**, for the user's review:
1. **β is per unit of the class variable, the units Reify's instance walks**: `units` reports an application of the
   variable (η-long, it stands nowhere else) beside a term and a λ argument holding it, an application after its own
   arguments; `converted` chains a step per unit, one loop for both instances. A unit's target is the variable
   instantiated there by the IR's `instantiate`, which β-reduces as Isabelle does.
2. **The slot's conversion is one function, `slotConverted`**, moved out of Reify's instance (decision 6's "the same way"
   made literal): the slot's class kept, its definition walked by the caller's own hole.
3. **At a predicate λ, β at an application is the walk of Isabelle's own β at its arguments**: `⋀x⃗. P(x⃗) ⟷ φ(x⃗)` at
   the hypothesis `A(P)` is the walk's rewrite of, instantiated at `t⃗` and walked — Reify's instance at a compound term
   making decision 4's conversion. **At a function λ, the same through a cut**: the atom's two forms at fresh variables,
   `⋀x⃗. φ[F(x⃗)] ⟷ φ[b(x⃗)]`, proved at its rewrite — `F(x⃗)`'s value `r` is the body's by β, the body's naming standing
   where `F(x⃗)`'s did, `TUPLE_EX_n` for the way back — then instantiated at `t⃗` and walked.
4. **`LAMBDA_<fp>`'s proof shares one piece**: at a tuple `τ = ⟨t⃗⟩`, the class's membership ↔ the body, `K`'s
   definition one way through `TUPLE_INJ_n`, the entries the other. A predicate λ wraps it in the atom's `∃τ`
   (`TUPLE_EX_n` back); a function λ chains it with `apply_pmem`, `K` having a value at `τ` by the body's EX.
5. ⚠ **EX OF A TERM INTRODUCES ITS WITNESS AT THE FRESH `z`, THEN INSTANTIATES `z`.** It introduced it after
   instantiating `z` at the term's value, abstracting every occurrence of the value — which a variable term shares with
   its own term: EX of `a` concluded `∃y. y = y` (`misproved`). A function λ's body may be a variable (`λx. x`,
   `λx y z. y`). Test: `anIdentityFunctionLambdaIsBetaAtItsArgument`.
6. **The congruence walks a class binder by fol-zfc's own `forall_elim` at the bound class, its guard first** (decision
   2's rule): Reify's instance at a compound term met `⋀a b P. a = b ⟹ P(b) ⟹ P(a)` once step 3 let such statements reach
   the walk, and stopped the run (`noCongruence`). Test: `aClassBinderBelowTheInstantiatedVariableIsWalkedAtACompoundTerm`.
7. **A lemma closes over a proposition as a letter at its top (S4)**: a statement's letter as itself; a variable Pure's
   `⋀` binds below a top as a letter too, its citation instantiating it at `holds(E)`, its reading. The closure wrote the
   first as a `∀` (the table refused its citation, `propositionAsTerm`, and the run stopped) and left the second out,
   dangling, silently. The class prover reads no letter: `CLASS_<fp>` of a λ holding one is unbuilt there, and its
   citers fall with it — 382 instances at a λ holding a letter, 24 at one holding a truth-set variable, of 46,219
   (a throwaway count, not kept). Tests: `aLambdaHoldingALetterIsASchemaInIt`,
   `aLambdaHoldingATruthSetVariableIsASchemaCitedAtItsTruth`.
8. **Fol transforms each statement by itself**: one transform over every root kept one cache for all, a key per node and
   context, and passed 32 GB once Logic built these instances. Per statement the cache lives for one; outputs are
   interned, so the unit is the same.
9. ⚠ **AN AXIOM BASE CLAIMS IS BASE'S CLAIM UNDER THE CLASS PREMISES THE AXIOM STATES.** Logic relabelled `subst`'s
   citation whole as base's `class_subst`; since OFCLASS the axiom states its class premise and base's claim none, so
   the IR's citation concluded what base's does not — the table trusts a citation's root, and only the kernel saw it
   (`implies_elim` at `class_subst`). Nothing lowered cited `subst` until its instances at a λ were built. The rule
   introduces the premises the axiom states beyond base's claim, by their count ahead of its first binder, over base's
   citation. Test: `substWithItsClassPremiseStatedIsBasesClassSubstUnderIt`, the kernel refusing it before.

**Measured** (`MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export`: all 9,420 proved, and the 195 named
theorems and 956 boxes they cite, unchanged. `MEM=48G … lower data/zf_export --emit DIR`: 23:54, peak 25.5 GB (16.0 GB);
read 74.6 s, lowered 374.2 s (77.7 s), emitted 982.9 s (205.6 s); 59,158,892 nodes (18,069,345). Then
`scripts/check-unit.sh DIR`: 41.2 s, peak 572 MB):
- **The kernel proves the unit**: 45 parts (40), each exit 0 and empty stderr; claims 4,579 of 4,579 (2,222), schemas
  111 of 111 (110); 541 `@def`s (453).
- **Named theorems lowered: 73** (65): the eight beside them whose proofs cite the instance — `ZF_Base.subst_elem`,
  `ZF_Base.strip.2`, `AC_Equiv.AC18.AC18`, `Normal.cub_family.next_greater_def` and `sup_greater_def`,
  `Reflection.reflection.F0_def`, `M_def` and `Reflects_def`; and of the facts they cite, `IFOL.spec`, `allI`, `subst`,
  `sym`, `trans`, `ssubst`, `forw_subst`, `back_subst` and `strip.2` reach the kernel.
- **Refused at no owner 3,702** (3,702), **logic 3,071** (3,955), a letter off its spine 204 (13), a refused citation
  2,370 (1,685). Logic's list is led by Pure's equality at a function type (step 4: `isaCombination((i => o), o, o)`
  2,274, `isaAbstract((i => o), o)` 1,991); `isaAllElim(o, T)` at an object function type leads it no more. A letter off
  its spine is the instance's own walk under a `⋀` at `o` that the cited theorem binds after the instantiated variable
  ("Logic", point 2's grammar: `ifolAll(o)`, `isaAllIntro(o)`, `folSchemaInst` off a citation's head), as
  `aLetterTheCitedTheoremBindsAfterTheInstantiatedClassIsOffItsSpine` pins; that all 204 are this rests on their three
  patterns alone.
- ⚠ **93% OF THE UNIT IS LEMMAS NOTHING CITES**: 4,242 of its 4,579 claims, 303 of its 326 MB, in the five `_uncited`
  parts — 638 `LAMBDA_` (7 cited), 724 `CLASS_` (30), 771 EX, 823 UNIQ, 196 `FUNC_`. Logic's walk requests them for
  statements that then fall, at a refused citation or a letter off its spine, and the registry proves every request
  before either is known. `λ classExists` alone writes 2.2 of the 4.5 million steps.
- `SOURCE_SURFACE.md` and `CLOSURE.md` regenerated: unchanged.

### Iteration — a run through a stage, a selection of theorems; emission in parallel  **[AGREED 2026-10-16 (user); BUILT 2026-10-16 — `Sources/IR/Pass.swift`, `Sources/Reader/Reader.swift`, `Sources/FolDialect/Emit.swift`, `Sources/isa2fol/`]**

**The need.** Step 3's corpus check took 24 minutes: read 75 s, lowered 374 s, emitted 983 s, checked 41 s. A feature
under construction fails at the earliest stage that sees it — the table refuses a step, a pass's proof stops concluding
its statement — so iteration runs the corpus only up to the stage being built, on the theorems it concerns; the full
run, emitted and kernel-checked, is the CI of a feature believed complete (user, 2026-10-16).

**1. A run through a stage.** A stage is a pass of the plan, or the registry, which proves after `provingAfter`. A run
through a stage stops after it: the unit is its statements as that stage left them, lemmas requested and not yet
proved among them, and the refusals so far; legalize, the letters' grammar and link are not run. Through the last pass
the run is complete. A stage the plan does not name stops the run (`noSuchPass`). Every run reports each stage's
seconds, link included.

**2. A selection of theorems.** The reader builds a unit of any theorems of the population, and everything they cite,
as it builds the population's: `--theorem NAME,…` selects by name, as statements are named (`ZF_Base.subst_elem`);
`--skip SESSION,…` drops whole sessions. A name or a session the export lacks stops the run. A theorem of a skipped
session that a selected one cites comes in as any citation does. The export's load still parses every proof file.

**3. Emission in parallel, the same bytes.** A statement's text depends on the finished table and its declaration
alone: no counter, cache or name passes between statements, and the table is read only. So statements render on
worker threads, each with its own stack as deep as the main thread's need, and the parts are assembled in order as
before; where a part splits depends on the bytes before it, so assembly stays sequential, and the first statement in
order that fails is the error reported. The tree count's memo stays on the sequential pass.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| IR (`Pipeline`) | `run(_:through:)`: the unit as the stage left it, or complete; each stage's seconds | — |
| Reader | `unit(of:)`: the selected theorems and what they cite, as `unit()` the population's | theorems of its population |
| FolDialect (`emit`) | `threads:`: the same bytes at any number of threads | a complete unit |
| CLI | `lower EXPORT [--through STAGE] [--theorem NAME,…] [--skip SESSION,…] [--threads N] [--emit DIR]`; `--emit` with a complete run only | — |

**Tests, written first.**
- `PipelineTests`: a run through a pass stops there, its statements that pass's output and its refusals the ones so
  far; through the registry, its lemmas proved; an unknown stage stops the run.
- `UnitTests` (Reader): a unit of selected theorems holds them and what they cite, and nothing else.
- `EmissionTests`: one unit emitted at one thread and at several, the same bytes in every file.

**Built** (2026-10-16). IR: `Pipeline.run(_:through:)` returns each stage's `Stage(name, seconds)`; a stop returns the
unit as the stage left it, legalization and link run only on a complete run, timed together as `link`. Reader:
`unit(of:)`, `unit()` its population's. FolDialect: `emit(…, threads:)` renders every statement on worker threads with
256 MB stacks, its results in a `Mutex` (`Synchronization`), never `@unchecked Sendable` (SwiftLint's
`no_unchecked_sendable`); one path at any thread count. CLI: `lower`'s options, `--threads` every core by default.

**Measured** (the release build on 48 cores; `lower` under `MEM=48G`, `check-unit.sh` under `MEM=32G`):
- **A complete run, the CI**: 8:36, peak 25.5 GB — read 74.6 s; expand 5.5 s, logic 54.1 s, registry 47.5 s, fol
  237.0 s, link 14.5 s; emitted 69.3 s (982.9 s on one thread). Every file the same bytes as the one-thread
  emission's; the kernel proves 45 parts, claims 4,579 of 4,579, schemas 111 of 111, in 41.1 s.
- **Through the registry**: 3:12, peak 13.6 GB. **The ZF session through logic** (`--skip` the other seven): 56 s, peak
  3.5 GB, 997 of its 3,616 named theorems standing. **Two theorems** (`--theorem ZF_Base.subst_elem,ZF_Base.strip.2`),
  complete: 33 s, the export's load.
- Fol is now the largest stage: 237 of the 369 s lowering takes.

### Step 4 — Pure's equality between functions  **[AGREED 2026-10-17 (user), the two decisions one by one; BUILT 2026-10-17, its decisions in the build for the user's review — `Sources/Lowering/Functions.swift`, `Logic.swift`, `Congruence.swift`, `Instance.swift`, `docs/FOUNDATION.md`]**

**The step.** Logic leaves Pure's equality between functions unbuilt: `≡` stated at a function type, and `reflexive`,
`symmetric`, `transitive`, `combination` and `abstract_rule` there (`isaReflexive`, `isaSymmetric`, `isaTransitive`,
`isaCombination`, `isaAbstract`), with the λ over classes they hold (`isaAbs((i ⇒ o), body: o)`). They are the
simplifier rewriting under a binder. Measured on the ZF session (`lower data/zf_export --through logic --skip` the other
seven, and a throwaway listing of each refusal's patterns, not kept): of the 1,318 named theorems Logic refuses, 1,276
hold one at an object function type, `iⁿ ⇒ o` or `iⁿ ⇒ i`, and 864 one at a function of classes, `(i ⇒ o) ⇒ o` — a
constant's partial application, `Ball(A)`.

**The problem, in target text.** Rewriting under `Ball` by `q : ⋀x. φ x ≡ ψ x`:

```
Isabelle   combination (reflexive (Ball A)) (abstract_rule q)     ⊢ Ball(A, λx. φ x) ≡ Ball(A, λx. ψ x)
read       Q = isaAbstract(i ⇒ o, q)                              ⊢ (λx. φ x) ≡ (λx. ψ x)                 at i ⇒ o
           R = isaReflexive(λP. Ball(A, P))                       ⊢ (λP. Ball(A, P)) ≡ (λP. Ball(A, P))   at (i ⇒ o) ⇒ o
           isaCombination((i ⇒ o) ⇒ o, R, Q)                      ⊢ Ball(A, λx. φ x) ↔ Ball(A, λx. ψ x)
```

`Q` and `R` conclude equations between functions, which have no fol-zfc reading. The plan's, each function's class and
`mfun_comb` for `combination` ("The meta level, lowered", as first written), has none for `R`: `λP. Ball(A, P)` takes a
class, a class is no member of a tuple, so it has no class.

**1. An equation between functions is read pointwise; a λ is reified only where the target needs an object in its
place.** **AGREED 2026-10-17 (user)**, over the classes' equality. At every function type whose arguments are objects —
`i`, `iⁿ ⇒ i`, `iⁿ ⇒ o` — and whose value is `i` or `o`, `f ≡ g` is Isabelle's own `⋀x⃗. f x⃗ ≡ g x⃗`, β-reduced: the λs'
binders become `∀`s, which Fol writes with their guards, and `≡` at the value is `↔` or `=`, as at `o` and at `i`.
FOUNDATION §1 has it already — `f ≡ g` and `⋀x. f x ≡ g x` are one formula — S1 makes a λ a wrapper, and S4 reads
`o⃗ ⇒ o` so.

| equation | fol-zfc |
|---|---|
| `(λx. φ x) ≡ (λx. ψ x)` at `i ⇒ o` | `forall x. (set(x) -> (φ(x) <-> ψ(x)))` |
| `(λP. Ball(A, P)) ≡ (λP. Ball(A, P))` at `(i ⇒ o) ⇒ o` | `forall K. (Ball(A, K) <-> Ball(A, K))`, `K` a class, unguarded |

A λ becomes a class exactly where the target needs an object in its place: a constant's argument, its class in the
slot (R4, S1), and a class variable's instance (step 3). Applied, it is its body: Isabelle's terms are β-reduced, and a
proof's instance is the IR's `instantiate`. In an equation, both sides are applied.

Not the classes' equality: it names a class per side of every equation only for each use to unfold it again —
`abstract_rule` builds them from the bodies, `combination` reads them back by β at both ends — at a `CLASS_` and a
`LAMBDA_` per λ (a λ's class existence writes about 2,900 steps, step 3's unit: 2.18M over 754), and it leaves the
function of classes without a reading, so `≡` would have two. What it would buy — `combination`'s argument equation
crossing one atom, `⟨a⟩ ∈ G` — needs each λ a class first; `combination` substitutes by the walk instead (2).

In ZF no constant takes a function of classes as an argument, in the named theorems or in what they cite. 25 theorems
bind a variable of such a type in their own proofs and instantiate it (`Sum.case_Inl`, `pair.splitI`,
`ZF.iterates_type`, …, at `(i ⇒ i ⇒ i) ⇒ i ⇒ i` and `(i ⇒ o) ⇒ o`), each holding 18–53 other unbuilt pieces: step 9's.
An upper bound on the named theorems that then pass Logic (they may still fall at a citation): 390 of the 1,318 with
equations at `iⁿ ⇒ i|o` alone, 1,061 with the function of classes; the rest wait on `If` (step 6; 245 hold it) and on a
binder over a function of classes (step 9).

**2. `combination` is its premise at the argument, then substitution into the function by Logic's replacement walk,
at the site.** **AGREED 2026-10-17 (user)**, over the function's class with membership's congruence at it, and over a
congruence lemma per function. `combination p q`, from `p ⊢ f ≡ g` and `q ⊢ a ≡ b`, concludes `f a ≡ g b`, its bodies
β-reduced:

1. `f a ≡ g a`: `p` at `a`, by the instance rules — `forall_elim` at a variable, Reify's at a term, Lambda's at a λ.
2. `g a ≡ g b`: the walk (`Replacement`), which compares `g`'s body at `a` with `g`'s body at `b`, both sides at once:
   two identical sides are base's `iff_refl`, and the walk stops; a connective or a binder is base's `cong_*` schema
   over its parts; an atom where `g`'s variable stands is a hole, filled by `q` carried to it. At a set argument `q` is
   `eq(a, b)`, carried by membership's congruence, base's `cong_elem_l`/`cong_elem_r`, `cong_eq_l`/`cong_eq_r` and, for
   a tuple's entry, `cong_snoc_v`. At a class argument `q` is `∀z⃗. φ(z⃗) ↔ ψ(z⃗)`, instantiated at the unit's arguments
   (step 3's units: an application, and inside a class slot's definition the application its λ holds). At a compound
   argument the walk is built at fresh variables and Reify's instance carries it to the terms, as `≡` at `i` already is
   (EX and UNIQ).
3. `iff_trans`, or `eq_trans` at value `i`.

```
q : A = B        combination (combination (reflexive mem) (reflexive a)) q          ⊢ a ∈ A ↔ a ∈ B
                 C1 at A                     elem(a, A) <-> elem(a, A)
                 cong_elem_r at a, A, B, q   elem(a, A) <-> elem(a, B)              the walk: one atom, a hole
                 iff_trans                   elem(a, A) <-> elem(a, B)

Q : ⋀x. φ ↔ ψ    combination (reflexive (Ball A)) (abstract_rule q)                ⊢ Ball(A, λx. φ x) ↔ Ball(A, λx. ψ x)
                 R at λx. φ x                step 3's instance
                 the walk                    ∃B: cong_exists_bare · ∧: cong_and · ∀b: cong_forall · ↔: cong_iff, b ∈ B iff_refl
                                             · ∃y: cong_exists · ∧: cong_and, b = ⟨y⟩ iff_refl · φ(y) vs ψ(y): the hole, Q at y
                                             · ∃C. ZF_Base.Ball(C, B) ∧ ⟨A⟩ ∈ C: iff_refl
                 iff_trans
```

One route for a set and a class argument alike, and the walk never enters the argument's own body: at a class
argument the hole is the whole `φ(y)`. Every fact about objects it cites is base's lemma — membership's congruence at
the holes; base's schemas are the propositional structure between them, whose letters are propositions, which no claim
states but through their truth sets (S4) (the user: "Prefer lemma when possible").

Not the function's class with one congruence for every class — `class_subst`, `apply_at`, every function typed `Func`
(the user, 2026-10-17): `combination` applies λs, the reader reading every function η-long (`mem` is `λx y. x ∈ y`),
so each would be reified first — its class existence, which walks the same body at more cost — then β at both ends at
every site; and a function of classes has no class, so a class argument would need the walk anyway: two routes.
Not a congruence lemma per function, `∀v⃗ x x'. x ≡ x' → g x ≡ g x'`: citing it at a λ argument reifies both arguments
and walks `g`'s body again for β, so it moves the walk without saving it.

**The other pieces, as 1 and 2 decide them.** At a function type over objects — each argument `i`, `iⁿ ⇒ i` or
`iⁿ ⇒ o`, the value `i` or `o` — Logic's rules:

| piece | rule |
|---|---|
| `isaConst(primitive Pure.eq, F ⇒ F ⇒ o, [f, g])` | the λs' bodies under `ifolAll` binders at the arguments' types, `≡` at the value between them: `↔`, or `=` named by Reify |
| `isaAbs` at a function of classes | a wrapper, as at objects and propositions: its body where it is applied |
| `isaReflexive` | under the binders, `iff_refl`; at value `i`, `eq_refl` through Reify's instance, as `≡` at `i` |
| `isaSymmetric`, `isaTransitive` | under the binders, the premises at the bound variables, then `iff_symm`, `iff_trans`; at value `i`, `eq_symm`, `eq_trans` as `≡` at `i` |
| `isaAbstract` | its premise, which concludes the rewritten conclusion by ID |
| `isaCombination` | 2 |

Unbuilt, unchanged: a binder, a variable or an instance at a function of classes (step 9), a function with a
proposition argument among others (step 6), `isaAbstract` at a function of propositions.

**FOUNDATION first.** S1 gains, after "a λ is a wrapper": an equation between functions whose arguments are objects is
pointwise, both sides applied and no class named for it, so `abstract_rule` concludes its premise; a function of
classes has no class, yet its equation is first-order, `∀K. F(K) ↔ G(K)`; `combination` substitutes its argument's
equation into the function by the formula recursion, membership's congruence at each atom where the argument stands, or
at a class argument the equation at the atom's arguments. §3b's proof-term mapping gains Pure's five rules at a function
type.

**The contracts (D2):**

| | provides | assumes |
|---|---|---|
| Logic | each piece above at a function type over objects, concluding the walk's rewrite of the table's conclusion, by ID; the rest unbuilt | the instance rules (`forall_elim` at a variable, Reify's at a term, Lambda's at a λ); base's `iff_*`, `cong_*`, `eq_*`, `cong_elem_*`, `cong_eq_*`, `cong_snoc_v` |
| Fol | unchanged: the pointwise binders are isa binders at object types, written with their guards | — |
| Base | unchanged | — |

**Tests, written first**, each lowering checked to conclude by ID and kernel-checked:
- `LogicTests`: `≡` stated at `i ⇒ o`, `i ⇒ i` and `(i ⇒ o) ⇒ o` is its pointwise formula; `reflexive` at each;
  `symmetric` and `transitive` at `i ⇒ o`; `abstract_rule` concludes its premise; `combination` at a set argument —
  `a ∈ A ↔ a ∈ B` from `A = B` through the curried chain of `mem`, the same at a compound argument
  (`succ(a) ∈ B ↔ succ(b) ∈ B` from `a = b`), and at value `i` (`succ(a) = succ(b)`); at a class argument, the `Ball`
  chain, `combination (reflexive (Ball A)) (abstract_rule q)`.
- `PlanTests`: each piece above at a function type over objects is Logic's rule; a binder or an instance at a function
  of classes is unbuilt; no pattern has two owners.
- The ZF session (`--skip` the other seven): through logic, Logic's refusals and what they name; then emitted and
  kernel-checked.

**Built.** `Sources/Lowering/Functions.swift`: `overObjects`, and `Functions` — the pointwise formula; `reflexive`;
`symmetric` and `transitive` under the binders, closed over their premises' statements and applied to them, as Truths'
are; `abstract`, its premise checked by ID; `combination`, the premise at the argument through the instance rules, then
`atSet` — at fresh variables, membership's congruence at the atoms, Reify's instance at the terms — or `atClass` — the
walk over the function's body with `Y` fixed for it alone, `Substitution` filling `Y`'s units with `q` at their
arguments, a slot converted by `slotConverted` from the template's own slot λ, the variables dropped after
(`unshift`). Logic: the `Pointwise` pieces (equation, wrapper, combination, abstract), `equality` at a function type
over objects, `Equalities.atI` shared. `Replacement` reads a stated equation between functions in its template
pointwise. `slotConverted(template:)`; `chained` shared. FOUNDATION S1 and §3b. Tests: `FunctionEqualityTests`, five,
each lowering kernel-checked but the reading's own; `PlanTests`' rows.

**Decisions made in the build**, for the user's review:
1. **A stated equation between functions inside a walked formula is read pointwise there too.** The ZF run stopped at
   `Bin.bin.case_eqns.1` (`noCongruence`): an instance walked a cited statement holding `≡` at `i ⇒ i`, a node no walk
   met before step 4 let such statements through Logic. `Replacement` unfolds it by the same `isaPointwise` the rule's
   reading walks to: one reading.
2. **At a class argument the units already carried are marked by a second variable, `Z`.** Placed at `a` all at once,
   a unit inside another's arguments loses its path when the outer one β-reduces; renaming a unit's head from `Y` to
   `Z` moves no path, and each step changes one unit, `Y` read at `a` and `Z` at `b`.
3. **An instance rule is handed Isabelle's statement as `hyp(0, φ)`**: Reify's and Lambda's instance read the
   eliminated premise for its conclusion alone, never lowering it; `φ` is `⋀x. Θ(x, x)`, the formula the premise's
   pointwise reading walks to, and `Θ(x, y)` is `f x ≡ g y` unfolded at its value.
4. **`atSet` is shared with a class argument's unit at a function class**: a term `Y(t⃗)` inside an atom is substituted
   as a set argument is, its equation `q` at `t⃗`.

**Measured** (the ZF session alone, `--skip` the other seven; the release build on 48 cores; the lint first):
- **Through logic**: 2:09, peak 6.7 GB (0:56, 3.5 GB). 2,058 of the 3,616 named theorems stand (997): the 1,061 the scope
  count bounded. Logic refuses 257 (1,318): `If` 245 (step 6) and the binders over a function of classes (step 9).
  Logic 80.6 s (7.9 s); 5,296 lemmas requested (759); the table 23.2M nodes (4.4M).
- **Complete, emitted and kernel-checked**: 11:04, peak 34.3 GB — read 41.6 s; expand 1.4 s, logic 75.8 s, registry
  38.0 s, fol 341.2 s, link 21.2 s; emitted 140.8 s, 17 parts, 382 MB; 76.7M nodes. `check-unit.sh`: 49.7 s, every part
  exit 0 and empty stderr, claims 6,057 of 6,057, schemas 100 of 100.
- **Named theorems lowered: 14.** The 1,061 that pass Logic now fall after it: at a letter off its spine 797 — step 3's
  gap, an instance walking under a `⋀` at `o` that the cited theorem binds after the instantiated variable, which their
  three patterns alone say — and at a refused citation, 1,247 in all, led by `IFOL.exI` 21, `ZF_Base.Ball_def` 21,
  `Bool.cond_DEF` 13. No owner 1,301, unchanged. The ZF session alone was not run complete before this step.
- ⚠ **99% OF THE UNIT IS LEMMAS NOTHING CITES**: 6,013 of its 6,057 claims, in the `_uncited` parts; `λ classExists`
  writes 4.3 of its 5.7 million steps.

### Fol — binders, guards and variables  **[BUILT 2026-09-28 as the guard; Fol's 2026-10-14; every object type and `∃` at `i` with "Reify — S1 at the site" — `Sources/Lowering/Fol.swift`]**

**Every isa binder at an object type, its intro, its variable and the guard of its variable become fol-zfc's, with the
guard Reify gives the type** (`Reify.guarded`): `set` at `i`, `function` at `iⁿ ⇒ i`, none at `iⁿ ⇒ o`. The guard
was a pass of its own until 2026-10-14. A variable keeps `isaBound(k, T)`, its type, until Fol: that type is how Fol
tells a set binder from a class binder.

⚠ **A VARIABLE BECOMES `folBound` ONLY IN FOL, THE LAST PASS.** A `folBound` is typed `i`, so a class variable
relabelled while a pass still reads types would look like a set, open to `set(P)`; the guard relabelled before reify
until 2026-09-29. So Fol relabels a variable in the walk that writes its binder, and an instance's or a guard's
discharge reads the binder's entry in the context, never the rewritten child.

⚠ **`set(t)` CANNOT BE WRITTEN FOR A COMPOUND `t`** — `folPred` takes only variables, S1 as a
check. So a compound instantiation is not discharged by a closure lemma over terms
(`set(C) → set(Pow(C))`); the term must first become a variable, FOUNDATION §2's S1 route, whose
EX delivers `set(r)` with it.

| before | after |
|---|---|
| `ifolAll(T, φ)` · `ifolEx(T, φ)`, `T` an object type, `G` its guard | `folForall(folImplies(G(0), φ′))` · `folExists(folAnd(G(0), φ′))`; at `iⁿ ⇒ o`, no guard: `folForall(φ′)` · `folExists(φ′)` |
| `isaAllIntro(T, body)` | `folForallIntro(folImpliesIntro(G(0), body′))`, or `folForallIntro(body′)` — the guard is a hypothesis the fixed variable brings |
| `isaAllElim(p, x)`, `x` a bound variable at `i` | `folImpliesElim(folForallElim(p′, x′), hyp(j, set(x′)))` — discharged by `x`'s own guard |
| `isaGuard(x, G)`, the guard of a variable | `hyp(j, G′)`, the same discharge; `G` not `x`'s guard (`notItsGuard`), or `x`'s binder bringing none (`unguardedBinder`), is malformed |
| `isaExIntro(q, x)`, at `i` | `folExistsIntro(folAndIntro(hyp(j, set(x′)), q′), x′)` — the witness's guard into the `∧` |
| `isaExElim(i, p, body)` | `folExistsElim(p′, implies_elim(implies_elim(implies_intro(set(0), implies_intro(φ′, body′)), and_elim_l(hyp(0, set(0) ∧ φ′))), and_elim_r(hyp(0, …))))` — the `∧` opened to the guard and `φ′` |
| `isaBound(k, T)`, `T` an object type | `folBound(k)` |
| `isaAllElim(p, t)`, `t` a compound term | never reaches Fol: the logic pass proves it (Reify's instance); an instance at anything but a bound variable throws `instanceNotAVariable` |
| `hyp(k, A)` | `hyp(k + g, A′)` — `g` the hypotheses Fol inserted between it and its binder |
| a variable at a type beyond objects other than `o` | Fol's, unbuilt: no such variable outlives its binder's owner |
| an instance at a class type | not Fol's: the logic pass's, Lambda's, unbuilt |
| … at `o`, at a function of propositions, at a type variable; a `λ` | not Fol's: Logic's, no owner's (decision 4), Reify's |

The walk rewrites every `use`'s root too, so a cited statement and the theorem's own lowered
statement are one node.

**Its context is a stack of the output's binder entries**, nearest last:

```swift
enum Entry: Hashable { case fix(IRType?), assume, inserted(guard: Bool) }
```

`enter` pushes what Fol's switch writes at the binder: `.fix(T)` and, where `T` has a guard, `.inserted(guard: true)`
at an intro; `.fix(.i)`, the `∧`, the guard and the input's hypothesis at an isa `∃`-elim; `.fix(nil)` per term and
`.assume` per hypothesis at any other binder. `narrow` keeps the top of the stack down to the deepest binder the node
reaches (`looseBound`, `looseHyps`); a closed node keeps nothing. Reading it, "above" meaning nearer the top:

- **the guard of `x`, bound `k`**: its entry is the `(k+1)`-th `.fix` from the top, its guard the `.inserted(guard:
  true)` between it and the next `.fix`, and `j` = the hypotheses above that guard. An entry with no guard there — a
  binder bringing none — is MALFORMED and throws; it is not a refusal.
- **`hyp(k, A)`**: its binder is the `(k+1)`-th `.assume` from the top, and its index the hypotheses above it.

```
fix x, assume P(x), lem at x              stack [x, gx, h]      above gx: 1     → hyp(1, set(x))
assume C, fix x, assume P(x), hyp(1, C)   stack [c, x, gx, h]   above c: 2      → hyp(2, C)
```

**One walk.** Fol writes fol-zfc's binders and variables, never a pattern it owns, so nothing is left for a second.

**Where it lives:** a module `Lowering`, depending on `IR` — the framework never sees a pass.

**Tests** (`FolTests`): Fol is run alone, each proof checked to conclude its statement BY ID. The pipeline over the plan
lowers `⋀x. ⊥ ⟹ ⊥` whole (`PlanTests`).

1. `∀`/`∃` at an object type takes its type's guard and its variable becomes fol-zfc's; at `o` and a type variable it
   is unchanged.
2. fix x, assume P(x), lem at x: the lowered proof concludes the lowered statement by ID; the discharge is `hyp(1, set(x))`.
3. assume C, fix x, assume P(x), `hyp(1, C)`: it becomes `hyp(2, C)`, and the proof concludes.
4. `(∃y. P(y)) ⟹ ∃y. Q(y)`: `∃`-elim and `∃`-intro at `i` are guarded, and an instance at the witness is discharged
   by its guard.
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
| 1 | **logic** — IFOL's ND rules and `FOL.classical` to the kernel's own steps; an inlined box instantiated at once, reduced at the proof level (`instantiate`); and, by Reify's code in the same walk, every compound term a variable with its defining atom, every function a class | every `⋀P::o` but a schema's letter; those rules' and boxes' class instantiations; `isaConst` at `i` or a function type, `isaVarApp`, `isaAbs`, `Pure.eq` at a function type, `isaAllElim` at a function type |
| 2 | **fol** — `set(x)` on every set binder, Isabelle's and reify's, a class binder bare, each written as fol-zfc's binder; every variable to `folBound`; then `legalize`. Until 2026-10-14 the guard was a pass of its own, before fol | the isa binders at `i`, `iⁿ ⇒ i`, `iⁿ ⇒ o`, and the rest of the isa dialect |

- **reify in logic's walk** (2026-10-14, "Reify called from Logic's walk"): a λ is named where it is consumed, never at
  its own node, so an IFOL rule at a λ still becomes the kernel's step and no class is built. `spec` at
  `λx. x∈A ⟶ x∈B`, then at `c`, is `isaAllElim` at `c`: `∀` and `⋀` are one node.
- **logic before fol**: Reify's variables are set binders too, and R3 guards "the ones S1 invents".
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
| … at `i^n ⇒ i` | a class variable `F`, guarded by `function(F)`, its application base's `apply` (S5) |
| … at `i^n ⇒ o` | a class variable `P`, bare (S4) |
| … at `o` | a schema letter at a statement's top, `schema_inst` at a citation; the logic's rules' are the kernel's own (S4; "Logic") |
| a constant — a function or a predicate | a class, cited globally (decision 5) |
| `c(x⃗) : i`, `f(x⃗) : i` | `∃r. fn_apply(F, t, r) ∧ φ(r)`, at the atom where it appears (decision 3) |
| `P(x⃗) : o`, a predicate constant or variable | `t ∈ P` |
| `ZF_Base.mem`; `IFOL.eq`, and Pure `≡` at `i`, which the reader reads as it | `elem`; `eq` — the target's own, not classes |
| Pure `≡` at `o` | `↔` — the reader reads it so |
| `f ≡ g` at a function type whose arguments are objects | `⋀x⃗. f x⃗ ≡ g x⃗`, β-reduced: pointwise, no class named ("Step 4", decision 1; first planned as the classes' `∀t r. fn_apply(F,t,r) ↔ fn_apply(G,t,r)`) |
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
| Pure `combination` at a function type | "Step 4" (first planned as `mfun_comb`, then β as proof at both ends) |
| Pure `abstract_rule` | its premise: `f ≡ g` and `⋀x. f x ≡ g x` are one formula ("Step 4", decision 1) |
| Pure `reflexive`, `symmetric`, `transitive` at a function type | base's `iff_*` and `eq_*` under the pointwise binders ("Step 4") |
| an inlined box instantiated at once | reduced at the proof level: the box read at its instance, no class |
| IFOL's thirteen ND rules, `FOL.classical` | the kernel's rules: `spec` is `forall_elim`, `exE` is `exists_elim`, … |

**Decisions (2026-09-29).**

1. **Arity 1 is a 1-tuple**, as R7 reads every arity. The value itself would save a tuple per unary
   application — a later size optimisation.
2. **Order: logic → reify → guard → fol**, on prerequisite 1; the guard is fol's since 2026-10-14, and reify runs in
   logic's walk since 2026-10-14 ("Reify called from Logic's walk").
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
   `@def`, so what is named is the constant's defining property, and a statement using the constant binds its
   class where it stands, `∃C. c(C) ∧ …` ("Reify — S1 at the site"). Of the relation form's four per-constant lemmas
   (FOUNDATION §2 S2, R5), two go and two merge:

   | relation form | class form |
   |---|---|
   | GRAPH | the constant is its class |
   | CONG | membership respects `=` for every class — `g1_pmem_cong`, proved once |
   | EX, UNIQ | EX and UNIQ of the term an instance meets, stated per term; a function variable's are base's `apply_EX` and, under `function(F)`, `apply_UNIQ` |
   | — | the class exists: class existence from the definition's body, the classes of the constants it uses as parameters (R5) |

   **The translator builds this definition/lemma graph** — during reify, as helpers, in definitional order
   (S3) — not as a phase before or after the passes. Not built: the per-formula class existence proof
   (FOUNDATION §3, "per-formula generation stays"). `base/` states the five primitives as relations
   (`primitives`: `Pow(A, r)`; `inf`: `Inf(r)`, the least inductive set) and their class predicates from those
   (`zf`).

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
