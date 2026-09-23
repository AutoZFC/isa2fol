# STATE — isa2fol
`6b135a66` · `feature/exists-descent` · 2026-09-03.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

**⚠ FIRST ROW OR NOTHING ELSE RUNS.** `command -v cargo; ls $CK`. Absent → nothing below
runs. `cargo` is NOT on a non-login shell's PATH — it is at `~/.cargo/bin`.
**⚠ THE SUITE IS GREEN.** A failure is a REGRESSION, not the designed state.
**⚠ NEVER RAISE `MEM`** — the suite fits `capped.sh`'s default (8G, 4 jobs).

| command (from `rs/`) | expect |
|---|---|
| `scripts/capped.sh cargo test --release --no-fail-fast` | **`305` passed, `0` failed** |
| `MEM=16G JOBS=8 scripts/capped.sh cargo build --release` | `0` × `^warning` |
| comment density of `src/**/*.rs` | `4.9996%` (`586/11721`) — **cap 5%, FOUR LINES away** |
| `find src -name '*.rs' \| xargs wc -l \| tail -1` | `12781` |
| `grep -cE '^axiom' base/axioms.fol.def` | `17` (**do NOT grep all of `base/`** — that gives 19) |
| `grep '^pub const TIERS' src/base.rs` | **9** entries (`ADMITTING_TIERS` matches too — count the one line) |
| `ls base/tiers/*.fol.def \| wc -l` | `10` — `diagonal` is present but deliberately OUT of `TIERS` |
| `ls docs/phase2_probes/*.fol.def \| wc -l` | `17` |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

Worktree `/home/arthur/repos/isa2fol`, branch `feature/exists-descent`, tree CLEAN,
**70 ahead of `origin/feature/exists-descent`, NOT pushed**.
`$CK` = `~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`, passed via
`PROOF_CHECKER=`. **Its absence is not a build failure — every kernel test simply fails.**
**⚠ CLAUDE.md's checker path `/home/arthur/Documents/repo/fol-zfc/` DOES NOT EXIST.**
**⚠ TWO STALE WORKTREES** — `isa2fol-build`, `.claude/worktrees/contig`. Both rest on the
deleted layer. **`main.rs` has only `--scan`.**

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `rs/docs/FOUNDATION.md` **§3** | assignments; the construction table; **the atom's open question, stated and NOT answered** |
| `rs/docs/FOUNDATION.md` **§3a** | the SUPERSEDED construction. Its probes are green — read the ⚠ |
| `rs/docs/FOUNDATION.md` **§2 S1/S4/S5** | terms are variables; `?P`→class variable; where each half is built |
| `rs/docs/phase2_probes/README.md` | the three ledgers; "an artifact survives only if a test runs it" |
| `rs/src/statement/mod.rs` | `pred_class`, `meta_fn_graph`, `schema_at`, the `Quant` arm |
| `rs/src/base.rs:26-30` | `TIERS` is 9; the ⚠ on what was removed |

## 3. Invariants

| invariant | enforced by |
|---|---|
| Only `base/` may emit a bare `axiom` | `gate::admission` |
| A Unit is valid only once the kernel accepted it: exit 0 AND empty stderr | `unit::check` |
| Comments ≤ 5% of `src/**/*.rs` | the §0 row; **delete prose, never raise the cap** |
| Every build/test capped | `scripts/capped.sh`; CLAUDE.md rule 10 |
| Every probe has exactly one ledger role | `gate::tests::every_probe_has_a_role` |

**Standing warnings — silent if repeated:**

- **⚠ §3a's PROBES ARE GREEN, LEDGERED, AND ANSWER IN THE SUPERSEDED VOICE.**
  `tuple_lemma`, `expansion`, `compiler_b` implement T1–T4 and sit in `CHAIN_PROBES`.
  A search for "how is class existence built" lands there, kernel-verified, reading as
  current. **T1–T4 are what §3's widening law REPLACES. Do not build on them.** This
  already caused one deleted commit's worth of work.
- **⚠ `a ∈ C` IS PLAIN `elem` UNDER §3**, so `∧` is B2 and `¬` is B3 DIRECTLY. Anything
  lifting them to `pmem` (`base/tiers/steps`) is §3a's.
- **⚠ DO NOT restore `tiers/{tuples,seeds,diagonal}`.** `diagonal`'s CLAIM survives (the
  `x = y` atom); its proof cites the removed T1/T2/T4.
- **⚠ A PIN DISAGREEING WITH THE CODE CAN MEAN THE CODE IS WRONG.** The S1-boundary pin
  was "corrected" to match an over-broad refusal; restoring the rendering restored the
  original numbers exactly. Trace upstream before editing an expectation.
- **⚠ CITATIONS ARE NOT THE AXIS.** `use` translates any cited theorem whose STATEMENT is
  expressible. Counting `_def` citations answers nothing.
- **⚠ ELIGIBILITY IS A CLOSURE.** A proof replays only if every theorem it cites does.
  Gap-shaving does not move it — see §4.

## 4. State

| claim | verified by |
|---|---|
| `?P` at arity ≥1 is a class variable; `⋀P` an unguarded class quantifier | `statement::tests::a_meta_quantifier_over_a_predicate_becomes_an_unguarded_class_quantifier` |
| `elem`/`pmem`/`tmem` are the whole vocabulary; wider `mem_n` refuses | `a_meta_function_variable_wider_than_tmem_is_refused` |
| 393→**401** eligible today; **2,437** with all 197 graphs; **16,791** with the gaps closed | `the_ceiling_is_gated_by_the_wide_atom_not_the_graphs` |
| 26 `no-rule` gaps remain; **18 are CORRECT refusals** (14 arity-0, 4 `mem4`) | same test |
| S3's induction is well-founded: 197 constants, 27 levels, no cycles | `the_constant_induction_is_well_founded` |
| Access is **0.28×** placement; max context width **9** | `access_costs_less_than_placement_on_real_bodies` |
| The base stays **19**; R6's two are `setclass`/`split` | `r6s_two_refusals_are_the_meta_function_values` |
| `The` is DEFINED (serial 1928), deps `{Replace,Union,cons,zero}` | `the_is_defined_not_primitive` |
| `ZF.pair/3594` renders — the only `ZF.*` statement that does | `zf_theories_refuse_at_the_s1_boundary` |

## 5. Beliefs — NOT verified

- **`base/tiers/steps` is unnecessary under §3** (B2/B3 apply directly). Removing it is a
  base change; not attempted.
- **Isabelle's own `Pair` stays Kuratowski.** §3 says so, but it was asked and never
  answered whether the switch was meant to reach the object language too. If it was,
  `fst`'s whole description-elimination route is obsolete rather than owed.

## 6. Open decisions

1. **§3's atom: does the `∃u v` arise?** `a(x) ∈ a(y)` unfolds to
   `∃u v. (⟨x,u⟩∈a ∧ ⟨y,v⟩∈a ∧ u∈v)`, and B4 — the only elimination — consumes a class of
   PAIRS. Either it does not arise (build at `I = {x,y}`, where the assignment IS
   `{⟨x,u⟩,⟨y,v⟩}` and determines both), or a width-3 intermediate is forced by the
   axioms' vocabulary. **The difference is exactly whether T1/T3 come back.** §3 poses
   this and does not answer it.
2. **`base/tiers/steps`** — remove as §3a, or keep?
3. **The two stale worktrees** — drop, or keep `contig` as a record?
4. **`the_p4_blocker_census`** — §2's "TWO, not eight" is unevidenced until the S5
   analysis is rebuilt. A structural proxy gives 75/58, a strict superset; do not cite it.
5. **Source language: Isabelle/ZF or Lean?** Isabelle/ZF is ALREADY ZFC — a change of
   ENCODING, which S6's conservativity carries. Lean would interpret CIC in set theory,
   and its strength is ZFC + countably many inaccessibles, **which R1 forbids**: a
   foundation change, not a front end. It would remove the meta-logic layer, which §4
   measures as NOT the bottleneck. ⚠ UNMEASURED — no handle here backs the Lean half.

## 7. Next action

**Settle §6.1 with the user, in FOUNDATION, before writing any code.**

**Done when** §3 states which way the atom's `∃` goes and why, and a reader can tell from
§3 alone whether a nested-pair intermediate is admissible. Nothing should be built on §3
until then — the last attempt was deleted for exactly this.
