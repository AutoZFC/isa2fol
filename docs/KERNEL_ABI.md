# Kernel ABI — a PROPOSAL

**STATUS: UNDECIDED, AND DELIBERATELY NOT ACTED ON.** Nothing here is built.
This exists so the decision is concrete when the gate in §10 resolves, not so it
can be started early.

**The claim is narrow.** Driving `fol-zfc`'s own `ProofContext` from the
translator buys *error locality* and deletes one bug class. It changes no
mathematics, closes no gap in FOUNDATION §4's census, and moves no ceiling.

---

## 1. The finding — there is a runtime, and it is LCF-shaped

`fol-zfc-comb/src/runtime/runtime.h:91`. `ProofContext` wraps
`ClassicalProofStack` (`src/proof/nd/stack.h:149`) and is an *incremental*
builder, not a batch validator:

```cpp
FormulaHandle parse(std::string_view);
FormulaResult use(const std::string& name);
Term          fix_var();
FormulaHandle assume(FormulaHandle const&);
FormulaResult implies_elim(FormulaHandle const& impl, FormulaHandle const& antecedent);
FormulaResult exists_elim(FormulaHandle const&);      // opens scope, fresh witness
util::ResultStatus qed(FormulaHandle const& derived);
```

`FormulaResult = util::Result<FormulaHandle>` — **every rule answers per step.**
`ProofStack::get_scopes()`/`derived()` are annotated "for serialization", so the
design already anticipates being driven from outside.

That is what makes this proposal different from "port the translator to C++".
The *runtime* is the asset. The language is not: every value crossing the
boundary is opaque (§4), so a C ABI gives Rust the whole of it.

---

## 2. The one design decision — ORACLE, not emitter

The kernel does **not** produce the artifact. `emit.rs` keeps producing
`.fol.def`/`.fol.proof`, `unit::check` (`src/unit.rs:203`) keeps running the
standalone `proof_checker` on it, and the ABI is called *in lockstep* during
construction to answer two questions:

| question | answered by |
|---|---|
| does this step compose? | the rule's `FolStatus` |
| what formula did it derive? | `fol_render` on the returned step |

**Rejected: construct-then-serialize.** It needs a C++ emitter that does not
exist, and it collapses the audit — the builder and the judge would share one
`GlobalContext`. The invariant "exit 0 AND empty stderr from a separately built
binary" is the whole content of `unit::check`, and it survives §2 untouched.

**⚠ THE ABI'S ABSENCE MUST NOT DEGRADE ANYTHING SILENTLY (rule 1).** Mirror
`PROOF_CHECKER=`: a missing library is a hard `Rejection` from whatever gate
requires it, never a quiet skip.

---

## 3. The surface is the IMAGE of `ir::nd::Rule` — not the preimage of `ProofContext`

This is the load-bearing rule of the whole design.

`ProofContext` exposes `eq_subst`, `eq_sym`, `iota_elim`, `last_iota_term`.
FOUNDATION §4 says `Step` has no `EqSubst` and no `IotaElim` so that "the
rejected constructs are unrepresentable rather than discouraged", and
`docs/phase2_probes/README.md` bans all four from every checked-in artifact.
**Binding `ProofContext` wholesale hands them back as one call.**

`rs/src/ir/nd.rs:48` already carries the correct narrowing. So:

> **The ABI exposes exactly the variants of `ir::nd::Rule`, plus `Step::Fix`,
> plus `parse`/`qed`. Nothing else. Widening it means widening `Rule` first,
> deliberately.**

### Exposed (23 rules + Fix)

`Assume` `Let` `Use` `SchemaInst` · `AndIntro` `AndElimL` `AndElimR` ·
`OrIntroL` `OrIntroR` `OrElim` · `ImpliesIntro` `ImpliesElim` ·
`NotIntro` `NotElim` · `BottomElim` · `IffIntro` `IffElimL` `IffElimR` ·
`ForallIntro` `ForallElim` · `ExistsIntro` `ExistsElim` · `DoubleNegElim`

### Omitted, and why

| omitted | reason |
|---|---|
| `eq_subst`, `eq_sym` | the `eqsubst` retirement; banned from every artifact |
| `iota_elim`, `last_iota_term` | the `iotafree` rail; banned from every artifact |
| `Term::description` (`core/formula.h:59`) | `Term` is a variant that *can be* a description — see §4 |
| `excluded_middle`, `classical_absurd`, `peirce` | not in `Rule`; not yet needed. Adding one is a `Rule` change, then an ABI change |
| `builder()`, `scopes()`, `derived()` | only needed by construct-then-serialize, which §2 rejects |

**This is strictly stronger than today's enforcement.** The ban is currently a
grep sweep over emitted text (`no_checked_in_artifact_carries_a_banned_construct`).
Under a narrowed ABI the function does not exist at the Rust call site.

### The invariant, and how it is enforced

`ABI surface == Rule variants` is checkable, not disciplinary: the Rust
dispatcher in §6 is one exhaustive `match` with no `_` arm, so **adding a `Rule`
variant fails to compile until the ABI covers it.** Same mechanism as
`ir/meta_tests.rs`'s `frozen_*` (§14's freeze), verified the same way — add a
variant and watch it fail.

---

## 4. Handles — opaque `u32`, minted only by the shim

`FormulaHandle = util::Handle<Formula>` is `{ size_t id_; const RegistryBase* }`
(`util/registry.h:41`). **That raw pointer never crosses the boundary.** The
shim keeps `std::vector<FormulaHandle>` and hands out its index.

`rs/src/ir/nd.rs:14` is already `pub struct Handle(pub u32)` — the match is exact.

Three namespaces, kept apart at the type level:

| ABI type | minted by | note |
|---|---|---|
| `FolFormula` | `fol_parse` | **NAMED, not asserted** — this is `Rule::Let` |
| `FolStep` | any rule, `fol_assume`, `fol_use` | derived |
| `FolTermId` | `fol_fix` and `fol_exists_elim`'s out-param **only** | |

**⚠ THE TERM NAMESPACE IS WHAT CLOSES THE DESCRIPTION LEAK.** `Term` is
`variant<GeneralizedVarTag, FixedVarTag, DescriptionTag>` and `DescriptionTag`
carries a `FormulaHandle`. Expose a term *constructor* and `forall_elim` can be
handed a description, re-opening exactly what §3 omits `iota_elim` to close.
Terms must be unforgeable: only `fix_var` and the witness out-param mint them.

`ProofContext` carries both as one `FormulaHandle`; only `ProofStack::is_derived`
(`stack.h:157`) tells them apart, and `ProofContext` does not re-expose it. The ABI
must separate them statically: `or_intro_l(FolStep, FolFormula)`.

---

## 5. The header

**`docs/fol_abi.h`** — the complete surface, not a sketch. All 23 `Rule`
variants are covered; it compiles clean under `-std=c99 -Wall -Wextra` and
`-std=c++17`. Read it there rather than duplicating it here.

Two things writing it out forced, which an abbreviated version hid:

- **`fol_step_formula`.** A derived step is sometimes wanted where a formula is —
  `or_intro`'s named disjunct, `bottom_elim`'s target. One downgrade function,
  rather than collapsing §4's two namespaces.

- **⚠ THE `or_intro` PAIR IS ASYMMETRIC, AND RUST CANNOT SEE IT.** `or_intro_l`
  derives from its LEFT; `or_intro_r` derives from its RIGHT. Both are
  `Rule::OrIntro{L,R} { left, right }` with two `nd::Handle`, and `emit.rs:60-61`
  renders both positionally, so nothing on the Rust side distinguishes the
  derived operand from the named one. **Swap them and the kernel accepts a
  different disjunction.** This is the sharpest argument for §4's two namespaces:
  typed apart in C, the swap does not compile.

`fol_render` is the debugging payoff made concrete: it returns *the kernel's own*
rendering of what a step derived, so a mismatch against `Formula::to_text()` is
visible at the step instead of as a unit-level stderr line.

`fol_parse` reuses the checker's parser, which also retires the risk that the two
`.fol.def` surface parsers drift. It is given a `FolStatus` deliberately:
`ProofContext::parse` (`runtime.h:112`) returns a bare `FormulaHandle` with no
way to report a parse failure, and rule 1 does not allow inheriting that.

## 6. The Rust side

```rust
pub struct Kernel {
    raw: *mut FolCtx,
    _not_send: PhantomData<*const ()>,   // §7: GlobalContext is single-threaded
}

#[derive(Debug)]
pub struct KernelError {
    pub at: usize,          // index into the step list
    pub rule: &'static str,
    pub node: Option<meta::ThmId>,   // the Isabelle proof-term node — the point of all this
    pub msg: String,
}

impl Kernel {
    pub fn open(defs: &[PathBuf]) -> Result<Self, KernelError>;
    pub fn prove(&mut self, claim: &str) -> Result<(), KernelError>;

    pub fn step(&mut self, at: usize, r: &nd::Rule) -> Result<nd::Handle, KernelError> {
        match r {                     // NO `_` ARM. Adding a Rule variant must not compile.
            nd::Rule::ImpliesElim { imp, arg } => self.call2(at, "implies_elim", *imp, *arg),
            nd::Rule::ForallElim  { src, term } => ...,
            ...
        }
    }

    pub fn rendered(&self, h: nd::Handle) -> Result<String, KernelError>;
}
```

`nd::Handle(u32)` passes through unchanged. `FolTerm::Var(name)` maps to the
`FolTermId` minted by that name's `fol_fix`; `FolTerm::HandleRef(h)`
(`ir/fol.rs:17`) maps to the id the binding step returned — which is exactly what
`h.name()` renders as in the text today.

---

## 7. Four things that will bite

1. **⚠ A SCHEMA'S `qed` RETURNING OK MEANS NOTHING.** `proof/runner.h`: the
   schema mark "fires whenever `claim_name` names a schema, **irrespective of
   proof success** — the schema's body is taken as an axiom and any 'proof' of it
   is a structural sanity-check." Already known (§1's "the checker cannot report a
   failed schema"), and unchanged here — but an API returning `Ok` is far more
   seductive than an exit code, and R2 is the rule it would quietly undermine.
   `fol_is_schema` exists so the wrapper can refuse to call it verification.

2. **Threading.** `proof/runner.h`: "a `ProofRunner` is single-threaded with
   respect to its `GlobalContext`". One `Runtime` per thread, `Kernel` is
   `!Send`/`!Sync`. This interacts with CLAUDE.md rule 10's `JOBS` cap — a
   per-thread `Runtime` is a per-thread heap, where today it is a per-thread
   `proof_checker` *process*.

3. **`Term` can be a description** — §4. The single most likely way this design
   silently re-admits what §3 omits.

4. **`Let` is not a step.** `Rule::Let` names a formula nothing proves; conflating
   it with a derived step is how `or_intro_l` would get an unproven disjunct past
   the type system. §4's two namespaces exist for this.

---

## 8. Build

`fol-zfc-comb` is Bazel and already emits `cc_library` targets (`nd:stack`,
`nd:verifier`, `//src/runtime`). Add one `cc_library` for the shim and a static
archive; **do not couple cargo to bazel.** Follow existing practice: a
`FOL_ABI=` env var naming a prebuilt archive, read by `build.rs`, absent → the
gate that needs it fails loudly (§2).

---

## 9. What this does NOT buy

It changes the feedback loop, not the translation. §14's H/S/E passes exist
because Isabelle identifies terms up to αβη silently and the target does not, and
because S1 must materialise compound terms. In-process the kernel tells you
*sooner* that a pass is wrong; it never tells you what is right.

None of the open problems are feedback-loop problems: FOUNDATION §3's atom, the
wide atom gating 2,437 against 16,791
(`the_ceiling_is_gated_by_the_wide_atom_not_the_graphs`), the iota-free plan.

---

## 10. The gate

FOUNDATION §4: **"No whole proof has been replayed. Answer it on one small theory
before building outward."**

Replay one proof through the existing text boundary first. Then:

| the replay fails because | verdict |
|---|---|
| the translator mispredicted kernel matching — the epsilon-wall, `implies_elim` "antecedent doesn't match" | **build this.** It is the bug class §1 deletes, and it pays back immediately |
| the mathematics is not derived yet | **do not build this.** It would have changed nothing |

Build it only on the first row.
