/* fol_abi.h — the C surface of fol-zfc's ProofContext, as seen from Rust.
 *
 * STATUS: PROPOSAL. Nothing implements this. See docs/KERNEL_ABI.md; build it
 * only if the §10 gate resolves on the first row.
 *
 * ---------------------------------------------------------------------------
 * THE ONE RULE
 * ---------------------------------------------------------------------------
 * This surface is the IMAGE of `rs/src/ir/nd.rs`'s `Rule`, not the preimage of
 * `fol-zfc-comb/src/runtime/runtime.h`'s ProofContext. Every function below
 * corresponds to exactly one `Rule` variant (or to `Step::Fix`). There are 23
 * variants and they are all covered.
 *
 * Widening this header means widening `Rule` first, deliberately. The Rust
 * dispatcher (`Kernel::step`) is one exhaustive match with no `_` arm, so a new
 * `Rule` variant fails to compile until a function here covers it.
 *
 * ---------------------------------------------------------------------------
 * DELIBERATELY NOT EXPOSED  -- do not add these
 * ---------------------------------------------------------------------------
 *   ProofContext::eq_subst         the eq_subst retirement. Banned from every
 *   ProofContext::eq_sym           checked-in artifact by
 *                                  gate::tests::no_checked_in_artifact_carries_a_banned_construct.
 *
 *   ProofContext::iota_elim        the iota-free rail. Same ban.
 *   ProofContext::last_iota_term
 *
 *   Term::description              core/formula.h:59 -- Term is a variant that
 *                                  CAN BE a description. Exposing any term
 *                                  constructor lets forall_elim take one, which
 *                                  re-opens exactly what omitting iota_elim
 *                                  closes. See FolTermId below: terms are
 *                                  unforgeable by construction.
 *
 *   ProofContext::excluded_middle  not in `Rule`. Not yet needed. Adding one is
 *   ProofContext::classical_absurd a `Rule` change first, then a change here.
 *   ProofContext::peirce
 *
 *   ProofStack::builder            only construct-then-serialize needs these,
 *   ProofStack::get_scopes         and KERNEL_ABI.md §2 rejects that design:
 *   ProofStack::derived            the artifact stays emit.rs's, and the
 *                                  standalone proof_checker stays the auditor.
 *
 * FOUNDATION.md §4: the rejected constructs must be UNREPRESENTABLE, not
 * discouraged. On the Rust side of this header they do not exist.
 */

#ifndef FOL_ABI_H
#define FOL_ABI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===========================================================================
 * Types
 *
 * FormulaHandle is { size_t id_; const RegistryBase<Formula>* } -- 16 bytes
 * carrying a raw pointer (util/registry.h:41). It NEVER crosses this boundary.
 * The shim keeps a side table; these ids are indices into it, so Rust holds
 * nothing that can dangle. rs/src/ir/nd.rs:14 is already `Handle(pub u32)`.
 * ======================================================================== */

typedef struct FolCtx FolCtx;

typedef uint32_t FolFormula; /* a NAMED formula. Asserts nothing. This is Rule::Let. */
typedef uint32_t FolStep;    /* a DERIVED step. */
typedef uint32_t FolTermId;  /* UNFORGEABLE: minted only by fol_fix and by
                              * fol_exists_elim's witness out-param. There is no
                              * term constructor, which is what keeps a
                              * description out of forall_elim. */

#define FOL_NULL ((uint32_t)0)

typedef int32_t FolStatus; /* 0 == ok; anything else, call fol_error */
#define FOL_OK ((FolStatus)0)

/* ProofContext carries derived and merely-named formulas as one FormulaHandle;
 * only ProofStack::is_derived (stack.h:157) tells them apart, and ProofContext
 * does not re-expose it. This header separates them statically instead. Use
 * fol_step_formula to pass a derived step where a formula is wanted. */
FolStatus fol_step_formula(FolCtx *, FolStep, FolFormula *out);

/* ===========================================================================
 * Lifecycle
 *
 * THREADING: ProofRunner is single-threaded with respect to its GlobalContext
 * (proof/runner.h). One FolCtx per thread, never shared. The Rust wrapper is
 * !Send + !Sync. Note each context is a Runtime HEAP where today each test
 * thread gets a proof_checker PROCESS -- this interacts with CLAUDE.md rule
 * 10's JOBS cap.
 * ======================================================================== */

FolCtx *fol_open(const char *const *def_paths, size_t n);
void    fol_close(FolCtx *);

/* Resolve a claim or schema by name and open a proof against it. */
FolStatus fol_prove(FolCtx *, const char *claim_name);

/* Last diagnostic. NUL-terminated, owned by the context, valid until the next
 * call on it. */
const char *fol_error(const FolCtx *);

/* ===========================================================================
 * Formulas
 * ======================================================================== */

/* Rule::Let. Names a formula without asserting it; there is no separate rule
 * call for Let.
 *
 * ProofContext::parse (runtime.h:112) returns a bare FormulaHandle with no way
 * to report a parse failure. Rule 1 does not allow inheriting that, so this
 * carries a status. */
FolStatus fol_parse(FolCtx *, const char *text, FolFormula *out);

/* The kernel's OWN rendering of what a step derived -- the point of the whole
 * design. Compare against Formula::to_text() to localise a divergence at the
 * step instead of reading it off a unit-level stderr line.
 * Writes at most cap bytes; always sets *len to the full length. */
FolStatus fol_render(const FolCtx *, FolStep, char *buf, size_t cap, size_t *len);

/* ===========================================================================
 * Scope                                      Step::Fix, Rule::Assume
 * ======================================================================== */

FolStatus fol_fix(FolCtx *, const char *var_name, FolTermId *out);
FolStatus fol_assume(FolCtx *, FolFormula, FolStep *out);
FolStatus fol_pop(FolCtx *);

/* ===========================================================================
 * Citation                                   Rule::Use, Rule::SchemaInst
 * ======================================================================== */

/* Cites an axiom OR a theorem; lowering.cpp resolves both through find_known. */
FolStatus fol_use(FolCtx *, const char *name, FolStep *out);

/* One `P: phi` or `P: \x y. phi`, matching nd::Binding { var, params, formula }.
 *
 * The shim resolves both name fields against the SchemaDefinition:
 *   var    -> the schema var id       (C++ SchemaBind is POSITIONAL, by id)
 *   params -> var_index per parameter (C++ SchemaBind::params is indices)
 * Rust holds names, so resolving them here is the shim's job, not the caller's.
 * arity 0 means params_n == 0 and params may be NULL. */
typedef struct {
    const char        *var;
    const char *const *params;
    size_t             params_n;
    FolFormula         body;
} FolBinding;

FolStatus fol_schema_inst(FolCtx *, const char *schema_name,
                          const FolBinding *bindings, size_t n, FolStep *out);

/* ===========================================================================
 * Conjunction                                Rule::AndIntro/AndElimL/AndElimR
 * ======================================================================== */

FolStatus fol_and_intro(FolCtx *, FolStep left, FolStep right, FolStep *out);
FolStatus fol_and_elim_l(FolCtx *, FolStep src, FolStep *out);
FolStatus fol_and_elim_r(FolCtx *, FolStep src, FolStep *out);

/* ===========================================================================
 * Disjunction                                Rule::OrIntroL/OrIntroR/OrElim
 *
 * !! THE INTRO PAIR IS ASYMMETRIC AND emit.rs RENDERS BOTH POSITIONALLY.
 *    or_intro_l: from A, derive A|B -- LEFT is derived, RIGHT is only named.
 *    or_intro_r: from B, derive A|B -- RIGHT is derived, LEFT is only named.
 *    Both are `Rule::OrIntroL/R { left, right }` with two nd::Handle in Rust,
 *    so the asymmetry is invisible there and is why the two namespaces above
 *    are separate types here. Swapping them builds a DIFFERENT disjunction that
 *    the kernel will happily accept.
 * ======================================================================== */

FolStatus fol_or_intro_l(FolCtx *, FolStep left, FolFormula right, FolStep *out);
FolStatus fol_or_intro_r(FolCtx *, FolFormula left, FolStep right, FolStep *out);
FolStatus fol_or_elim(FolCtx *, FolStep or_step, FolStep left_case,
                      FolStep right_case, FolStep *out);

/* ===========================================================================
 * Implication                                Rule::ImpliesIntro/ImpliesElim
 * ======================================================================== */

/* Closes the innermost assumption scope: from assumption A deriving B, get A->B. */
FolStatus fol_implies_intro(FolCtx *, FolStep conclusion, FolStep *out);
FolStatus fol_implies_elim(FolCtx *, FolStep imp, FolStep arg, FolStep *out);

/* ===========================================================================
 * Negation and bottom            Rule::NotIntro/NotElim/BottomElim
 * ======================================================================== */

FolStatus fol_not_intro(FolCtx *, FolStep bottom, FolStep *out);
FolStatus fol_not_elim(FolCtx *, FolStep neg, FolStep pos, FolStep *out);

/* Ex falso. `formula` is the TARGET -- named, not derived. */
FolStatus fol_bottom_elim(FolCtx *, FolStep bottom, FolFormula formula, FolStep *out);

/* ===========================================================================
 * Biconditional                  Rule::IffIntro/IffElimL/IffElimR
 * ======================================================================== */

FolStatus fol_iff_intro(FolCtx *, FolStep fwd, FolStep bwd, FolStep *out);
FolStatus fol_iff_elim_l(FolCtx *, FolStep iff, FolStep arg, FolStep *out);
FolStatus fol_iff_elim_r(FolCtx *, FolStep iff, FolStep arg, FolStep *out);

/* ===========================================================================
 * Quantifiers        Rule::ForallIntro/ForallElim/ExistsIntro/ExistsElim
 * ======================================================================== */

FolStatus fol_forall_intro(FolCtx *, FolStep src, FolStep *out);
FolStatus fol_forall_elim(FolCtx *, FolStep src, FolTermId, FolStep *out);

/* witness may be FOL_NULL (Rule::ExistsIntro's `witness: Option<FolTerm>`):
 * absent means close the current Exists scope, present means generalise it. */
FolStatus fol_exists_intro(FolCtx *, FolStep body, FolTermId witness, FolStep *out);

/* Opens an Exists scope with a fresh witness. *witness receives it -- this is
 * the ONLY other place a FolTermId is minted. */
FolStatus fol_exists_elim(FolCtx *, FolStep src, FolStep *out, FolTermId *witness);

/* ===========================================================================
 * Classical                                  Rule::DoubleNegElim
 * ======================================================================== */

FolStatus fol_double_neg_elim(FolCtx *, FolStep src, FolStep *out);

/* ===========================================================================
 * Completion
 * ======================================================================== */

FolStatus fol_qed(FolCtx *, FolStep derived);

/* !! A SCHEMA'S fol_qed RETURNING FOL_OK MEANS NOTHING.
 *    proof/runner.h: the schema mark fires whenever claim_name names a schema,
 *    "irrespective of proof success -- the schema's body is taken as an axiom
 *    and any 'proof' of it is a structural sanity-check." Known already
 *    (FOUNDATION_TO_FOLZFC §1, "the checker cannot report a failed schema"),
 *    and unchanged by going in-process. But FOL_OK is far more seductive than
 *    an exit code, and R2 -- every schema proved -- is the rule it would
 *    quietly undermine. Call this before believing fol_qed. */
int fol_is_schema(const FolCtx *);

/* Axioms and theorems consulted since fol_prove (NDVerifier::last_used_names).
 * Writes at most cap pointers; always sets *n to the true count. Strings are
 * owned by the context. */
FolStatus fol_used(const FolCtx *, const char **buf, size_t cap, size_t *n);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FOL_ABI_H */
