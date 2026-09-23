# isa2fol: Isabelle/ZF to FOL-ZFC Translation

## Problem

Isabelle/ZF is a proof assistant that mechanizes set theory (ZFC) within a
higher-order metalogic framework. The mathematical content — theorems about
sets, ordinals, cardinals, etc. — is first-order logic with ZFC axioms.
However, Isabelle wraps this content in layers of metalogic, type system
infrastructure, and proof automation machinery.

We want to **independently verify** these ZF proofs by translating them into
a standalone first-order logic proof format (fol-zfc) and checking them with
a separate proof checker. This provides a second, independent confirmation
that the proofs are correct.

### What we translate

**Claims:** ZF theorem statements — first-order formulas about sets.
Example: `forall A. forall B. forall C. (elem(A, B) -> elem(B, C) -> elem(A, union(C)))`

**Proofs:** Natural deduction derivations using FOL rules (forall_intro,
implies_elim, eq_subst, etc.) that derive each claim from ZFC axioms and
previously proved theorems.

### What we do NOT translate

Isabelle's infrastructure that implements FOL but is not itself FOL:

- **Pure metalogic** — `Pure.eq` (meta-equality `≡`), `Pure.imp`
  (meta-implication `⟹`), `Pure.all` (meta-universal `⋀`). These are
  Isabelle's proof framework, not part of the mathematics.

- **IFOL/FOL definitions** — theorems like `IFOL.not_def` that *define*
  what `¬` means in Isabelle. In fol-zfc, `¬` is a primitive.

- **Simplifier machinery** — reflection lemmas, congruence rules, and
  rewrite chains that Isabelle's `simp` tactic produces. These are
  proof automation artifacts.

- **Type/sort infrastructure** — sort constraints, type class machinery,
  type variable abstractions. In ZFC all types collapse to a single sort.

## Source: Isabelle Proof Terms

Isabelle exports proof terms as YXML binary files. Each proof term is a tree
built from six constructors:

| Constructor | Tag | Meaning |
|---|---|---|
| ZAbst | 2, 4 (with attr) | `⋀`-introduction (bind a variable) |
| ZAbsp | 3 | `⟹`-introduction (assume a hypothesis) |
| ZAppt | 4 (no attr) | `⋀`-elimination (apply a term/formula) |
| ZAppp | 5 | `⟹`-elimination (modus ponens) |
| ZThm | 10 | Reference to a proved theorem (by serial number) |
| ZAxiom | 7 | Reference to a kernel axiom |

A proof file also contains:
- **Type environment** — declares the free variables and their types
- **Proposition** — the formula being proved
- **Sort constraints** — type class constraints (trivially true in ZFC)

### Key insight: meta/object distinction

Isabelle has TWO levels of logic:

- **Meta-level:** `⟹` (meta-implication), `⋀` (meta-universal), `≡` (meta-equality)
- **Object-level:** `→` (implication), `∀` (universal), `↔` (iff), `=` (equality)

In our translation, the meta/object distinction collapses — but only for
**term-level** quantification:

- `⟹` = `→` (meta-implication = object implication)
- `⋀x:i. P(x)` = `∀x. P(x)` (meta-universal over terms = object universal)
- `≡` on propositions = `↔` (meta-equality on props = biconditional)
- `≡` on terms = `=` (meta-equality on terms = object equality)

**But** `⋀P:o. P → P` (meta-universal over *propositions*) does NOT become
`∀P. P → P`. It becomes a **schema** with `P` as a free schema variable.
The linearizer handles this: `SchemaAbst` strips the meta-quantifier and
leaves the variable free.

This collapse is valid because ZFC has only one sort (sets), so all
term-level meta/object distinctions are trivially satisfied. Proposition-level
meta-quantification becomes schema quantification in the fol-zfc framework.

## Target: fol-zfc Proof System

The fol-zfc proof checker supports these native proof rules:

### Propositional logic
- `and_intro(h1, h2)` — from A and B, derive A & B
- `and_elim_l(h)` / `and_elim_r(h)` — from A & B, derive A or B
- `or_intro_l(h, let_B)` / `or_intro_r(let_A, h)` — disjunction introduction
- `or_elim(h_or, h_left, h_right)` — disjunction elimination
- `implies_intro(h)` / `implies_elim(h_imp, h_ant)` — implication
- `not_intro(h)` / `not_elim(h_neg, h_pos)` — negation
- `bottom_elim(h_bot, let_formula)` — ex falso quodlibet
- `iff_intro(h_fwd, h_bwd)` / `iff_elim_l(h_iff, h_a)` / `iff_elim_r(h_iff, h_b)` — biconditional

### First-order logic
- `forall_intro(h)` / `forall_elim(h, term)` — universal quantification
- `exists_intro(h, witness)` / `exists_elim(h)` — existential quantification
- `eq_subst(h_eq, h_target)` — Leibniz substitution

### Classical logic
- `double_neg_elim(h)` — from ~~A, derive A
- `excluded_middle(let_formula)` — derive A | ~A
- `classical_absurd(h)` — from assumption ~A leading to bottom, derive A

### Proof management
- `fix x` — introduce a term variable (for forall_intro)
- `assume formula` — introduce a hypothesis (for implies_intro)
- `let formula` — introduce a formula term (for or_intro, bottom_elim, etc.)
- `use name` — reference a previously proved theorem
- `schema_inst name { bindings }` — instantiate a schema
- `qed handle` — conclude the proof

## Translation Pipeline

```
YXML proof file
  → parse (yxml.rs)
  → IR1: Isabelle-native proof tree (linearize.rs)
  → Flat steps: unified Step enum, Core + Isa dialect (linearize.rs)
  → Pass 0: Pure.eq elimination (Isa → Fol)
  → Pass 1: Identity elimination
  → Pass 2: Native ND lowering
  → Pass 3: Standard library renaming
  → Validation
  → text output (emit.rs)
```

### IR1 — Isabelle proof tree

A tree that faithfully represents Isabelle's proof term constructors.
This is the only Isabelle-specific IR — everything after linearization
uses the unified Step enum.

```
TermAbst(var, body)         — ZAbst on a term variable
SchemaAbst(var, type, body) — ZAbst on a schema variable (stripped)
TypeAbst(body)              — ZAbst on a type variable (stripped)
ImpliesIntro(hyp, formula, body) — ZAbsp
SortConstraintIntro(body)   — ZAbsp on a sort constraint (stripped)
ImpliesElim(left, right)    — ZAppp
Appt(proof, arg)            — ZAppt (not yet classified)
ThmRef(serial)              — ZThm
PureAxiomRef(kind)          — ZAxiom for recognized Pure axioms
AxiomRef(name)              — ZAxiom for other axioms
BoundProof(name)            — bound proof variable (de Bruijn)
```

### Linearization (IR1 → flat steps)

The tree is linearized into a flat step list using the unified Step enum.
During linearization:

- ZAbst on terms → `Fix` + body + `ForallIntro` (Core dialect)
- ZAbsp → `Assume` + body + `ImpliesIntro` (Core dialect)
- ZAppp → `ImpliesElim` (Core dialect)
- ZAppt → classified using per-theorem type info from theorem database:
  - Term arguments → `ForallElim` (Core dialect)
  - Schema arguments → collected into `SchemaInst` (Core dialect)
- Sort constraints and type abstractions are stripped
- Pure axioms (reflexive, symmetric, transitive, equal_elim, equal_intr,
  combination, abstract_rule) → `PureRefl`, `PureSym`, etc. (Isa dialect)

After linearization, the steps contain Core + Isa dialect. No Fol dialect
steps exist yet — those are introduced by the passes.

### Passes (flat steps → flat steps)

All passes operate on `Vec<Step>` using shared `PassContext` infrastructure.
Each pass progressively eliminates non-FOL constructs and introduces
native fol-zfc steps. See the Pass Framework section below for details.

## Formula Translation (IsaExpr → FolFormula)

Isabelle formulas (IsaExpr) must be translated to fol-zfc formulas
(FolFormula) for claim/schema declarations and for formula arguments
in proof steps (Assume, Let, etc.).

Key transformations:

- **Connectives**: direct mapping (And, Or, Implies, Not, Iff, True, False)
- **Quantifiers**: `∀x:i. P(x)` → `forall x. P(x)` (term vars);
  `∀P:o. ...` → schema variable P (prop vars, stripped)
- **Sort constraint implications**: `IFOL.term('a) ⟹ P` → `P` (stripped,
  trivially true in ZFC)
- **Named function application**: `succ(n)` where `succ` is a defined
  constant → `exists _v. (succ_fn1(n, _v) & P(_v))` (function-as-predicate)
- **Variable function application**: `f(x)` where `f` is a free variable
  of type `i→i` → `exists _v. (apply(f, x, _v) & P(_v))` using generic
  `apply` (function graph membership)
- **Equality**: `Pure.eq` on terms → `eq(a, b)`;
  `Pure.eq` on propositions → `(A <-> B)`
- **Type erasure**: all type information dropped (single-sorted in ZFC)
- **Name sanitization**: Isabelle names like `IFOL.conj` → `IFOL_2econj`
  (dots encoded as `_2e`, special chars as hex)

### Function encoding in ZFC

In Isabelle/ZF, many theorems take function parameters (`f: i→i`).
These are meta-level functions used for substitution. In FOL, functions
are sets (of ordered pairs), not meta-level entities.

**Design principle:** functions are sets. A function variable `f: i→i`
is a ZFC set. Applying `f(x)` is `apply(f, x)` where `apply` is
function graph membership: `apply(f, x, y) ↔ elem(Pair(x, y), f)`.

Each named function constant produces three declarations:

1. **Definition axiom**: defines what the function computes
   ```
   axiom succ_def: forall x, y. (succ_fn(x, y) <-> eq(y, union(x, singleton(x))))
   ```

2. **Function claim** (UNPROVED, codegen later): asserts it is a valid function
   ```
   claim is_function_succ: is_function(succ)
   ```

3. **Existence** (derived from is_function): if `is_function(f)`, then
   `forall x. exists y. apply(f, x, y)`.

Theorems that take function parameters (RepFun, Ball, Bex, Sigma, etc.)
include `is_function(f)` as a premise:

```
forall b A f P. is_function(f) ->
  (elem(b, RepFun(A, f)) ->
   (forall x. elem(x, A) -> (exists _v. apply(f, x, _v) & eq(b, _v)) -> P) -> P)
```

In proofs, when Isabelle passes a named function to such a theorem:
```
_h0 = use RepFunE
_h1 = forall_elim _h0, b
_h2 = forall_elim _h1, A
_h3 = forall_elim _h2, succ        // f = succ (plain variable, a ZFC set)
_h4 = use is_function_succ          // is_function(succ)
_h5 = implies_elim _h3, _h4        // discharge function constraint
```

No schema_inst needed for function parameters. No lambdas in proof steps.

When Isabelle passes `λx. g(x)` (eta-reducible): use `g` directly.
When Isabelle passes `λx. complex_body(x)` (anonymous): construct the
function set as a term and declare is_function for it (UNPROVED/conditional).

### Proposition variables vs function variables

In Isabelle, theorem parameters are classified by type:

| Type | Example | FOL encoding |
|---|---|---|
| `i` (term) | `x`, `A` | Plain variable, `forall_elim` |
| `i→i` (function) | `f`, `succ` | ZFC function set, `forall_elim` + `is_function` |
| `o` (proposition) | `P` | Schema variable, `schema_inst` |
| `i→o` (predicate) | `P(x)` | Schema variable with arity, `schema_inst` |

Only propositions and predicates use schemas. Functions are first-order
(they're sets) and use `forall_elim`.

### Theorem database

Before translating proofs, a pre-scan of all proof files builds a
theorem database mapping each serial number to:

- **name**: sanitized theorem name (from thms files)
- **var_types**: ordered type list from type_env (for ZAppt dispatch:
  term vs schema arguments)
- **schema_vars**: (name, arity) pairs for schema variables
- **closed_formula**: translated proposition with free term vars
  universally closed

This database is used during linearization (to classify ZAppt arguments)
and during bridge emission (for schema/claim declarations).

### What proofs do we translate?

We translate proofs from **ZF theories only** (directories starting with
`ZF`). Proofs from Pure, IFOL, and FOL theories are NOT translated — they
are logic infrastructure, not mathematical content.

Within ZF theories, we translate ALL proofs including unnamed intermediate
lemmas (thm_NNN). These intermediate lemmas are typically proof steps that
Isabelle's automation broke into sub-proofs. They are real mathematical
derivations.

A proof that references a feature we cannot yet handle (unknown theorem
pattern, untranslatable formula construct) is marked as `failed` and
emitted as `UNPROVED`. This does not block other proofs — the checker
treats unproved dependencies as conditional.

## Non-FOL Theorem Classification

When a ZF proof references a theorem (via ZThm), that theorem might be
a ZF theorem (real mathematics) or an IFOL/FOL/Pure theorem (logic
infrastructure). We audited all ZF proof files and found **148 distinct
non-ZF theorem serials** referenced, totaling 1.75M references.

These fall into three categories with different handling strategies:

### Category 1: Identity elimination (18 theorems, 1.19M refs)

These theorems are identity functions in our translation (because the
meta/object distinction collapses). The lowering pass eliminates them
by remapping the result handle to the argument handle.

| Theorem | What it does | Why it's identity |
|---|---|---|
| IFOL.eq_reflection | eq(a,b) → a ≡ b | meta-eq on terms = eq |
| IFOL.iff_reflection{,_T,_F} | (P↔Q) → P ≡ Q | meta-eq on props = iff |
| IFOL.impI | (P⟹Q) → P→Q | ⟹ = → |
| IFOL.mp | (P→Q) → P → Q | same as implies_elim |
| IFOL.rev_mp | P → (P→Q) → Q | implies_elim with swapped args |
| IFOL.allI | (⋀x.P(x)) → ∀x.P(x) | ⋀ = ∀ |
| IFOL.allE / IFOL.spec | (∀x.P(x)) → P(a) | same as forall_elim |
| IFOL.def_imp_iff | (A↔B) → (A↔B) | trivial identity |
| IFOL.meta_eq_to_obj_eq | a ≡ b → eq(a,b) | inverse of eq_reflection |
| IFOL.meta_eq_to_iff | P ≡ Q → (P↔Q) | inverse of iff_reflection |
| Pure.protectI / protectD | A → A | simplifier guard, identity |
| Pure.conjunctionD1/D2/I | meta-conjunction | meta-and intro/elim, identity |

### Category 2: Native ND lowering (15 theorems, ~65K refs)

These theorems correspond directly to fol-zfc proof rules. The lowering
pass recognizes the pattern `SchemaInst(theorem) + ImpliesElim chain` and
replaces it with the native rule.

**Straightforward lowerings:**

| Theorem | Pattern | fol-zfc rule |
|---|---|---|
| IFOL.conjI | SI + 2×IE | and_intro(arg1, arg2) |
| IFOL.conjunct1 | SI + IE | and_elim_l(arg) |
| IFOL.conjunct2 | SI + IE | and_elim_r(arg) |
| IFOL.disjI1 | SI + IE | or_intro_l(arg, let_Q) |
| IFOL.disjI2 | SI + IE | or_intro_r(let_P, arg) |
| IFOL.disjE | SI + 3×IE | or_elim(arg1, arg2, arg3) |
| IFOL.FalseE | SI + IE | bottom_elim(arg, let_P) |
| IFOL.notE | SI + 2×IE | not_elim(arg1, arg2) |
| IFOL.iffI | SI + 2×IE | iff_intro(arg1, arg2) |
| IFOL.iffD1 | SI + 2×IE | iff_elim_l(arg1, arg2) |
| IFOL.iffD2 | SI + 2×IE | iff_elim_r(arg1, arg2) |
| IFOL.exI | SI + FE + IE | exists_intro(arg, term) |
| IFOL.subst | SI + 2×FE + 2×IE | eq_subst(eq_arg, target_arg) |
| FOL.classical | SI + IE | excluded_middle / classical_absurd |
| FOL.ccontr | SI + IE | classical_absurd |

(SI = SchemaInst, IE = ImpliesElim, FE = ForallElim)

**Complex lowerings (deferred — see Open Questions):**

| Theorem | Difficulty | Issue |
|---|---|---|
| IFOL.notI | scope mismatch | `implies_intro` produces `P → _|_`, but `not_intro` produces `~P`. Need to verify if the checker treats these as equivalent, or if scope rewriting is needed. |
| IFOL.conjE | compound pattern | `P&Q ⟹ (P⟹Q⟹R) ⟹ R` requires expanding into `and_elim_l` + `and_elim_r` + two `implies_elim` steps. The second argument is a nested implication that must be decomposed. |
| IFOL.exE | scope-sensitive | `∃x.P(x) ⟹ (⋀x. P(x)⟹R) ⟹ R` requires opening a witness scope via `exists_elim`, running the sub-proof, and closing it. Needs scope analysis of the argument proof. |

**Moved to standard library (not native lowering):**

| Theorem | Reason |
|---|---|
| IFOL.TrueI | No native `true_intro` in fol-zfc. If True = `~_|_`, proving it requires multi-step expansion. Simpler as stdlib claim. |
| IFOL.refl | No native `eq_refl` in fol-zfc (only `eq_subst`). Must be declared as axiom or stdlib claim. |

### Category 3: Standard library (110 theorems, 251K refs)

These are **valid first-order logic theorems** — not metalogic, not
infrastructure, but actual FOL facts. They include:

**Simplifier tautologies** (IFOL_simps, ~80 theorems):
- `P & True <-> P`, `P & False <-> False`
- `P | True <-> True`, `P | False <-> P`
- `~~P <-> P` (classical), `(P -> False) <-> ~P`
- Associativity, idempotence, De Morgan's laws
- Quantifier simplifications

**Congruence lemmas** (~10 theorems):
- `(P<->P') -> (Q<->Q') -> ((P&Q) <-> (P'&Q'))` (conj_cong)
- `(P<->P') -> (P'->(Q<->Q')) -> ((P->Q) <-> (P'->Q'))` (imp_cong)
- Similar for disjunction, negation, quantifiers

**Classical reasoning rules** (~20 theorems):
- `FOL.swap`: `~P -> (~R -> P) -> R`
- `FOL.impCE`, `FOL.iffCE`: classical elimination rules
- Various `cla_simps` rules

**Strategy: declare as unproved claims.** These are true FOL theorems
that can be proved later. For now, they're included as a standard library
`.fol.def` file. Any ZF proof that depends on them gets "conditional"
verification status from the checker — correct assuming the library is
sound.

## IR Design

### Problem with separate IR2/IR3 types

The current codebase has IR2 (with Pure markers) and IR3 (fol-zfc steps)
as separate enums. This causes:

1. **Duplicated shared ops** — Fix, Assume, Use, SchemaInst, ForallIntro,
   ForallElim, ImpliesIntro, ImpliesElim, Qed are defined in both enums
   with identical fields. Any change must be made twice.

2. **Duplicated pass infrastructure** — Each pass (optimize.rs, lower.rs)
   independently builds its own `HashMap<Handle, Handle>` for remapping,
   `HandleGen` for fresh handles, and a massive `remap_step()` function
   that pattern-matches every variant to update handle fields.

3. **False boundary** — The IR2→IR3 conversion isn't a clean boundary.
   The Pure.eq elimination pass produces IR3 steps (IffElimL) while
   consuming IR2 steps (PureElim). Passes after it operate on IR3 but
   still find IFOL theorem references in the "shared" ops (Use, SchemaInst,
   ImpliesElim). The type boundary doesn't protect what matters.

### Solution: unified Step enum with dialect tags

One flat enum containing all step kinds from both Isabelle and fol-zfc.
Each variant belongs to a dialect:

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dialect { Core, Isa, Fol }

enum Step {
    // ── Core dialect (valid throughout the pipeline) ──
    Fix { var: String },
    Assume { handle: Handle, formula: String },
    Use { handle: Handle, name: String },
    Let { handle: Handle, formula: String },
    SchemaInst { handle: Handle, name: String, bindings: Vec<SchemaBinding> },
    ForallIntro { handle: Handle, src: Handle },
    ForallElim { handle: Handle, src: Handle, term: String },
    ImpliesIntro { handle: Handle, src: Handle },
    ImpliesElim { handle: Handle, src: Handle, arg: Handle },
    Qed { src: Handle },

    // ── Isabelle dialect (eliminated by passes) ──
    PureRefl { handle: Handle, formula: String },
    PureSym { handle: Handle, left: String, right: String },
    PureTrans { handle: Handle, a: String, b: String, c: String },
    PureElim { handle: Handle, left: String, right: String },
    PureIntr { handle: Handle, left: String, right: String },
    PureComb { handle: Handle, f: String, g: String, a: String, b: String },
    PureAbst { handle: Handle, f: String, g: String },

    // ── fol-zfc dialect (introduced by passes) ──
    AndIntro { handle: Handle, left: Handle, right: Handle },
    AndElimL { handle: Handle, src: Handle },
    AndElimR { handle: Handle, src: Handle },
    OrIntroL { handle: Handle, left: Handle, right: Handle },
    OrIntroR { handle: Handle, left: Handle, right: Handle },
    OrElim { handle: Handle, or_proof: Handle, left_case: Handle, right_case: Handle },
    NotIntro { handle: Handle, src: Handle },
    NotElim { handle: Handle, neg: Handle, pos: Handle },
    BottomElim { handle: Handle, bottom: Handle, formula: Handle },
    IffIntro { handle: Handle, forward: Handle, backward: Handle },
    IffElimL { handle: Handle, iff: Handle, left: Handle },
    IffElimR { handle: Handle, iff: Handle, right: Handle },
    ExistsIntro { handle: Handle, body: Handle, witness: String },
    ExistsElim { handle: Handle, src: Handle },
    EqSubst { handle: Handle, eq: Handle, target: Handle },
    DoubleNegElim { handle: Handle, src: Handle },
    ExcludedMiddle { handle: Handle, formula: Handle },
}
```

Benefits:
- **No duplication**: shared ops defined once
- **Progressive lowering**: passes freely mix dialects during transformation
- **Flat pattern matching**: no nested `Step::Shared(SharedOp::Fix{..})`
- **Dialect query**: `step.dialect()` returns Core/Isa/Fol for validation

### Validation

After all passes, validate that no Isabelle-dialect steps remain:

```rust
fn validate_no_isa(steps: &[Step]) -> Result<(), ValidationError> {
    for (i, step) in steps.iter().enumerate() {
        if step.dialect() == Dialect::Isa {
            return Err(ValidationError { index: i, step: step.clone() });
        }
    }
    Ok(())
}
```

The emitter also refuses to emit Isa-dialect steps (panic/error).

Additionally, validate that no Use/SchemaInst references known non-ZF
names (except standard library entries):

```rust
fn validate_no_ifol_refs(steps: &[Step], stdlib: &HashSet<String>) -> Result<(), ...> {
    for step in steps {
        if let Step::Use { name, .. } | Step::SchemaInst { name, .. } = step {
            if is_known_ifol(name) && !stdlib.contains(name) {
                return Err(...);
            }
        }
    }
    Ok(())
}
```

### Handle infrastructure

All passes need the same handle manipulation machinery. This is provided
by a shared `PassContext`:

```rust
struct PassContext {
    /// Handle remapping: old handle → new handle.
    /// Used when a step is eliminated and downstream references
    /// need to point to the replacement.
    remap: HashMap<Handle, Handle>,

    /// Fresh handle generator. Initialized past the max existing handle.
    gen: HandleGen,

    /// Output step buffer.
    output: Vec<Step>,
}

impl PassContext {
    /// Resolve a handle through the remap chain (follows transitive remaps).
    fn map(&self, h: Handle) -> Handle { ... }

    /// Generate a fresh handle.
    fn fresh(&mut self) -> Handle { ... }

    /// Record that `from` should be remapped to `to` (identity elimination).
    fn remap(&mut self, from: Handle, to: Handle) { ... }

    /// Emit a step to the output, applying handle remapping to all fields.
    fn emit(&mut self, step: Step) { ... }

    /// Apply handle remapping to all handle fields in a step.
    /// This is defined ONCE for the unified Step enum — not duplicated per pass.
    fn remap_step(&self, step: Step) -> Step { ... }
}
```

The critical win: `remap_step()` is written once for all ~30 variants.
Every pass reuses it instead of reimplementing the same match arms.

## Pass Framework

Each pass is a function that takes ownership of a `Vec<Step>` and returns
a new `Vec<Step>`. Passes use `PassContext` for shared infrastructure and
add domain-specific logic on top.

```rust
/// A proof being translated.
struct Proof {
    serial: i32,
    name: String,
    steps: Vec<Step>,
}

/// The full pipeline.
fn translate_proof(ir1: &ir1::Node, ...) -> Proof {
    let steps = linearize(ir1, ...);         // IR1 tree → flat steps (Core + Isa dialect)
    let steps = pass_pure_eq(steps);         // eliminate Isa Pure markers → Fol iff ops
    let steps = pass_identity_elim(steps);   // eliminate identity theorems
    let steps = pass_native_nd(steps);       // lower IFOL rules → Fol native ops
    let steps = pass_stdlib_rename(steps);   // rename remaining refs to stdlib names
    validate_no_isa(&steps).unwrap();
    validate_no_ifol_refs(&steps, &stdlib_names).unwrap();
    Proof { serial, name, steps }
}
```

### Pass 0: Pure.eq elimination

**Input:** Core + Isa dialect steps.
**Output:** Core + Fol dialect steps. All Isa-dialect Pure markers eliminated.

Uses semantic tagging to track what each handle represents (Iff, PurePartial,
ImpliesFromPure, Formula). When ImpliesElim consumes a Pure marker, the
pass recognizes the pattern and emits native IffElimL/IffElimR/IffIntro instead.

This is the existing `optimize.rs` logic, adapted to use the unified Step enum.

### Pass 1: Identity elimination

**Input:** Core + Fol steps, with Use/SchemaInst referencing identity theorems.
**Output:** Same, with identity theorems eliminated.

For each recognized identity theorem (eq_reflection, iff_reflection, impI,
allI, protectD/I, etc.):
1. When SchemaInst/Use of the theorem is encountered, tag as pending
2. When the expected ForallElim/ImpliesElim chain completes, remap the
   final handle to the argument handle
3. No step is emitted — the theorem application vanishes

### Pass 2: Native ND lowering

**Input:** Core + Fol steps, with Use/SchemaInst referencing IFOL proof rules.
**Output:** Same, with IFOL rules replaced by native fol-zfc steps.

For each recognized ND theorem (conjI, notE, FalseE, subst, etc.):
1. Tag SchemaInst/Use as pending with the expected argument count
2. Track ForallElim/ImpliesElim consumption
3. When complete, emit the native fol-zfc step (AndIntro, NotElim, etc.)

### Pass 3: Standard library renaming

**Input:** Core + Fol steps, with Use/SchemaInst referencing FOL simplifier
rules and congruence lemmas.
**Output:** Same, with references renamed to match the standard library
declaration names.

This pass handles the 110 standard library theorems. It may also need to
adjust schema variable bindings to match the library's variable naming.

### Pass ordering

Pass 0 **must** run first — later passes assume no Isa-dialect steps.

Pass 1 (identity) and Pass 2 (native ND) are **independent** — they
recognize different theorem names and don't interact. Either order works.
However, running identity elimination first is slightly better: it reduces
the step count before native ND lowering, making the forward scan faster.

Pass 3 (stdlib rename) **must** run last — it handles whatever non-ZF
references remain after passes 1 and 2.

**Lenient by default:** each pass leaves unrecognized patterns unchanged
(passes them through to output). This allows incremental development —
we can add handling for new patterns without breaking existing passes.
A pattern not handled by pass 2 simply survives to pass 3 or validation.

### Validation

After all passes:
1. No Isa-dialect steps remain (emitter rejects them at runtime)
2. No Use/SchemaInst references known IFOL/FOL/Pure names (except stdlib)
3. All handles resolve (no dangling references)

Validation errors indicate lowering gaps — patterns we haven't implemented
yet. The error message should identify the offending step and theorem name
so we can add the missing lowering rule.

## Output Format

Two files are produced:

### Definition file (.fol.def)

```
schema <name> [<vars>]: <formula>    -- schema with variables
claim <name>: <formula>              -- theorem to be proved
axiom <name>: <formula>              -- accepted without proof
```

### Proof file (.fol.proof)

```
proof <name>:
    fix x
    _h0 = assume P(x)
    _h1 = use other_theorem
    _h2 = forall_elim _h1, x
    _h3 = implies_elim _h2, _h0
    _h4 = forall_intro _h3
    qed _h4
```

### Standard library file (stdlib.fol.def)

Contains the 110 FOL tautology/congruence declarations as unproved
claims. Loaded as a dependency by the checker. Proofs for these can be
added later for full (non-conditional) verification.

## Data Layout

```
data/zf_export/
├── Pure/          -- Pure metalogic (skip proofs)
├── IFOL/          -- Intuitionistic FOL (skip proofs, use as lowering source)
├── FOL/           -- Classical FOL (skip proofs, standard library)
├── ZF/            -- ZF base theory
├── ZF.upair/      -- Unordered pairs
├── ZF.equalities/ -- Set equalities
├── ZF.Ordinal/    -- Ordinals
├── ...            -- ~40 ZF theories
└── each theory/
    ├── theory/thms    -- theorem serial→name mapping (YXML)
    ├── theory/consts  -- constant type information (YXML)
    └── proofs/NNN     -- individual proof files by serial (YXML)
```

## Verification

```bash
# Build
cd rs && cargo build --release

# Translate
rs/target/release/isa2fol --bridge data/zf_export --output /tmp/out.fol.def

# Verify (with standard library)
proof_checker stdlib.fol.def /tmp/out.fol.def /tmp/out.fol.proof
```

The checker reports:
- **Proved**: theorem verified from axioms and proved dependencies
- **Conditional**: theorem correct assuming unproved library claims
- **Failed**: translation error (indicates a bug in our pipeline)

## Resolved Design Decisions

### Function-typed parameters (lambda/forall_elim problem)

**Problem:** 29K `forall_elim` steps had complex terms (formulas, lambdas)
instead of plain variables. Isabelle passes lambdas `λx. body(x)` to
function-typed parameters (`f: i→i`), but FOL can't express lambdas as terms.

**Solution:** Functions are ZFC sets. Function parameters use `forall_elim`
with the function set as a plain variable. Function application uses generic
`apply(f, x, y)` (graph membership). Each function constant gets an
`is_function` claim. Theorems with function parameters include
`is_function(f)` as a premise.

- Named functions (succ, Pair, etc.): `forall_elim _h, succ` — plain variable
- Lambda `λx. g(x)` (eta-reducible): use `g` directly
- Anonymous lambda `λx. body(x)` (rare): construct function set, UNPROVED

See "Function encoding in ZFC" section above for details.

### Definition-unfolding theorems (schema arity conflicts)

**Problem:** 50 schemas had arity conflicts (same variable used at arity 0
and arity N). These are Isabelle's definition-unfolding machinery where
`Pure.eq` equates a predicate variable with a concrete constant.

**Solution:** These are not FOL content. They're emitted as placeholder
schemas with `_|_`. The level-3 instantiated versions (which ARE valid FOL)
are emitted as claims. Proofs that reference them are conditional.

## Open Questions and Known Limitations

### 1. notI scope mismatch

In Isabelle, `notI: (P ⟹ False) ⟹ ~P` converts a meta-implication to
negation. Our linearizer produces `implies_intro` (yielding `P → _|_`)
for the inner `⟹`. Then the notI application wraps it as `~P`.

In fol-zfc, `not_intro` and `implies_intro` produce different formulas:
`~P` vs `P → _|_`. If the checker treats these as distinct, we need
scope rewriting — changing an `implies_intro` to `not_intro` after the
fact. If the checker treats `~P` and `P → _|_` as interchangeable,
this is a non-issue.

**Status:** needs investigation of checker behavior.

### 2. Selective eq_subst

fol-zfc's `eq_subst(h_eq, h_target)` replaces ALL occurrences of term `a`
with `b` in the target formula. Isabelle's `IFOL.subst` uses a schema
predicate `P` that can selectively replace: `P = λx. elem(x, a)` replaces
only the first position, giving `elem(b, a)` not `elem(b, b)`.

If a ZF proof uses subst for selective replacement, our lowering to
eq_subst produces the wrong result.

**Status:** need to audit actual subst usage patterns in ZF proofs.
The schema binding `P` tells us WHAT is being substituted — we may
be able to detect selective cases and handle them differently.

### 3. exists_elim scope management

fol-zfc's `exists_elim` opens a witness scope (introduces a fresh
variable). Isabelle's `IFOL.exE` is encoded as a theorem application:
`∃x.P(x) ⟹ (⋀x. P(x)⟹R) ⟹ R`. The second argument contains a
sub-proof that assumes `P(c)` for fresh `c` and derives `R`.

Lowering this requires:
1. Emit `exists_elim` to open the scope
2. Process the sub-proof body (which was a ZAbsp + ZAbst)
3. Close the scope appropriately

The difficulty: by the time we see the IFOL.exE pattern in flat IR3,
the sub-proof has already been linearized into flat steps (Assume, Fix,
ImpliesIntro, ForallIntro). We need to identify which steps belong to
the sub-proof and restructure them around the exists_elim scope.

**Status:** needs detailed design. May require a scope analysis pass.

### 4. Formula correctness for _|_ cases

Some Isabelle constructs produce `_|_` (bottom) in translated formulas
when the translator doesn't recognize the term. This means some claim
formulas are incorrect. Proofs of these claims might verify against the
wrong formula.

**Status:** need to audit which IsaExpr constructs produce `_|_` and
fix the formula translator.

### 5. TrueI and refl as axioms

IFOL.TrueI (proof of True) and IFOL.refl (proof of eq(a,a)) cannot
be lowered to native fol-zfc rules — there are no `true_intro` or
`eq_refl` primitives. They must be provided as axioms or standard
library claims.

For refl, the fol-zfc axiom would be: `axiom eq_refl: forall x. eq(x, x)`
For TrueI, if True = `~_|_`: `axiom true_intro: ~_|_`

These are sound axioms (true in every model). Adding them as axioms
rather than unproved claims avoids "conditional" status for proofs
that use reflexivity or True.

### 6. conj_cong dependency on antecedent

The congruence lemma `imp_cong` has the form:
`(P<->P') -> (P' -> (Q<->Q')) -> ((P->Q) <-> (P'->Q'))`

Note the second premise: `P' -> (Q<->Q')` — the equivalence of Q and Q'
is conditional on P' being true. This is a contextual congruence used by
Isabelle's simplifier to rewrite under assumptions.

In fol-zfc, this is a valid FOL theorem. But if we ever want to prove
it (instead of using it as an unproved claim), the proof requires
careful handling of the conditional equivalence.

**Status:** not blocking (stdlib is unproved for now), but worth noting
for future proof development.

### 7. Unknown thm_NNN serials from IFOL/FOL

The audit found ~1.5K references to unnamed theorems (thm_NNN) from
IFOL/FOL theories. These are intermediate lemmas in IFOL/FOL that
aren't listed in the thms files. They need to be classified into the
three categories (identity / native ND / stdlib) by examining their
proof files.

**Status:** low priority. These are few references compared to the
named theorems. They can be handled by the lenient pass-through
behavior — unrecognized patterns survive to stdlib/validation.
