# STATE — isa2fol
The commit that last updates this file (parent `760b96d2`) · `feature/exists-descent` · 2026-09-29.  **RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is at `~/.local/bin` — not on a non-login shell's PATH. Run from the repo root, after `swift build -c release`.

| command | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | `205` |
| `find Sources Tests -name '*.swift' \| wc -l` · total lines | `44` · `5790` |
| comment density of `Sources` (CLAUDE.md rule 9's script) | `9/2629 = 0.3%` |
| `grep -rnE '^\s*default:' Sources \| wc -l` | `0` |
| `.build/release/isa2fol read data/zf_export \| grep -A1 -E '^named'` | `proved: 9420` · `…outside the ZF sessions: 200` / `proved: 200` |
| `.build/release/isa2fol lower data/zf_export \| grep -E '^(lowered\|refused\|  guard)'` | `lowered through guard: 2685 — …` · `refused: 6735` · `  guard: compoundInstantiation: 6735` |
| `.build/release/isa2fol surface data/zf_export \| grep '^\| \*\*all'` | `\| **all** \| **9420** \|` |
| `find data/zf_export -path '*/proofs/*' -type f \| wc -l` | `38923` — else `bash scripts/03-export-zf.sh` |
| `scripts/capped.sh scripts/check-base.sh` | every tier `exit 0  stderr 0`; Proved: axioms 7, pairs 20, witness 6, logic 3, cong 4, s2s3 0, primitives 11, regroup 0, skolem 3, tuples 15, classes 38, metafun 11; script exits 0 |
| `readlink ~/repos/fol-zfc-comb/bazel-bin \| sed 's\|.*bazel-out/\|\|'` | `k8-opt/bin`, `proof_checker` executable there |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h qualified-names` | `487c68c` (unmerged) |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

`/home/arthur/repos/isa2fol`, branch `feature/exists-descent`, clean, 152 commits not pushed
(`git rev-list --count origin/feature/exists-descent..HEAD`). fol-zfc-comb sits on its own `comb-verifier`
with an uncommitted `MODULE.bazel.lock` that is the user's; leave both alone. `git worktree list` also
shows `../isa2fol-build` and `.claude/worktrees/agent-*`: not this work.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `docs/FOUNDATION.md` **§1a**, **§3** | tuples are functions; the base is standard NBG and what we use is PROVED; §3's rows, the scope rule, the atom question answered |
| `DESIGN.md` §4a **"The meta level, lowered — the pass plan"** | DECIDED: logic → reify → guard → fol, what each construct becomes, the two framework prerequisites, the five decisions (4 deferred) |
| `base/tiers/tuples.fol.def`, `classes.fol.def`, `metafun.fol.def` | the claims; each header says what the tier is. Proofs are machine-long; read the statements |
| `Sources/IR/Traversal.swift`, `Pass.swift`, `Sources/Lowering/Guard.swift` | the built framework and pass 1 (guard) |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 AND stderr is empty | `scripts/check-base.sh`; the real-checker tests in `Tests/FolDialectTests` |
| Nothing is admitted outside `base/axioms` (and `skolem`'s Inf introduction); every tier lemma is a proved claim | `scripts/check-base.sh`; review of every added claim |
| Equal content is one node; an ill-formed node cannot exist | `Table.intern` (`TableTests`, `ProofTests`) |
| Every proof read, and every lowered one, concludes its statement BY ID | `Reader.prove`; `Pipeline.run` → `PipelineError.unproved` |
| The reader emits only the isa dialect | `theReaderEmitsOnlyTheIsaDialect`; `legalize`; `render` throws `sourceKind` |

**Standing warnings — silent or misleading if repeated:**

- **⚠ A CONSTANT IS A CLASS, APPLIED BY MEMBERSHIP** — `⟨t, r⟩ ∈ F`, never a relation `c(x⃗, r)`
  (FOUNDATION's top banner). FOUNDATION §2 still writes the relation form; read it as that atom.
- **⚠ A COMPOUND TERM'S VARIABLE IS BOUND WHERE THE TERM APPEARS, NEVER WIDER**; a λ or compound
  term is never lifted into a global claim (DESIGN §4a decision 3).
- **⚠ A TUPLE IS A FUNCTION WITH DOMAIN `n`, NEVER A NESTED PAIR** (FOUNDATION §1a). Triples appear only in
  B6/B7 and in `classes`' `cls_*` toolkit; no row or claim above states one. `tmem` is B6/B7's notation alone.
- **⚠ `index(n)` IS TRANSITIVE AND `n ∉ n` — NOT FINITE.** It replaces Foundation (no Regularity in `base/`).
- **⚠ A BASE TIER IS CHAINED**: run bare it reports `Failed`, which reads as staleness. Use `scripts/check-base.sh`.
- **⚠ THE CHECKER WILL NOT `use` A CLAIM WITH NO PROOF BLOCK**, and a missing proof goes to stderr. Agents
  proving in parallel stub others' claims `proof X: UNPROVED` at the top; strip the stubs when merging, and
  order blocks so a claim's proof precedes every use.
- **⚠ `exists_intro` TAKES 1 OR 2 ARGUMENTS**; with a witness it abstracts EVERY occurrence. No `let` form.
- **⚠ `Conditional` IS NOT `Proved`; NEVER SUM THEM.**
- **⚠ THE READER CHOOSES NOTHING** — which types, what `OFCLASS` becomes: translation's (`DESIGN.md` §4.3a).
- **⚠ BINDER KNOWLEDGE LIVES ONLY IN `mapChildren`**; **A RULE MUST BE A FUNCTION OF (node, context, table)**;
  **THE CACHE IS KEYED ON THE NARROWED CONTEXT** (full context: one proof exceeds 150 M rewrites).
- **⚠ THE GUARD IS ONE WALK, NEVER A `RulePass`**; **`folPred` TAKES ONLY A VARIABLE** — `folBound`, or `isaBound` not at `o` (S1 as a check); **A VARIABLE KEEPS `isaBound(k, T)` UNTIL FOL** — its type is how the guard tells a set from a class.
- **⚠ A SECOND REFERENCE TO `unit.table` COPIES THE WHOLE TABLE** at the pipeline's first write.
- **⚠ `false`, LOWERCASE, IS ⊥**; **NO NAME MANGLING** (rule 5); **NEVER ITERATE A `Dictionary`/`Set` TOWARD OUTPUT**.
- **⚠ `t[try t.intern(…)]` READS THE TABLE BEFORE THE INTERN** — intern into a `let` first.
- **⚠ REORDERING `Node` CASES LEAVES DEPENDENT MODULES STALE** — `rm -rf .build/out/Products .build/out/Intermediates.noindex`.
- **⚠ BUILDING fol-zfc-comb IN DEFAULT CONFIG REPOINTS `bazel-bin` TO `k8-fastbuild`**; restore it to `k8-opt/bin`.
- **⚠ A SERIAL NAMES A THEOREM ONLY WITHIN ONE BUILD AND ONE THEORY**; **`data/zf_export` IS ONE BUILD OR NOTHING**.
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED**; `docs/phase2_probes/README.md` describes
  Rust-era gates that no longer exist — nothing runs the probes but a hand.

## 4. State

| claim | verified by |
|---|---|
| The reader proves all 9,420 named theorems of the 8 sessions, plus the 200 Pure/IFOL/FOL theorems they cite; 0 refused | §0's `read` row |
| Pass 1, the guard: 2,685 lowered BY ID, 6,735 refused `compoundInstantiation`; variables keep `isaBound`, so the output is still isa | §0's `lower` row; `LoweringTests` (7) |
| A fol node takes an isa variable of matching type: `folPred` any variable not at `o`, `exists_intro`/`exists_elim` the typed `ifolEx` (DESIGN §4a prerequisite 1) | `aPredicateTakesAVariableOfEveryTermType`, `aVariableAtOIsNotAPredicateArgument`, `existentialStepsTakeTheTypedExistsBeforeFol` |
| `render` emits formulas and proofs the REAL checker proves; a typed `use` is not rendered | `theRealCheckerProvesWhatEmissionWrites`, `aCitationOfAnInstanceIsNotRendered` |
| Proofs rest on Pure/IFOL/FOL axioms and defs, ZF_Base's 6 axioms, `AC.AC`, 984 ZF definitions, 5 example axioms; 0 oracles | `isa2fol closure data/zf_export` (`docs/CLOSURE.md`) |
| `base/axioms` states 17 of the 19 — not Regularity, not Choice | `base/axioms.fol.def:19` |
| FOUNDATION §1a's layers are theorems of B1–B7: `tuples` (snoc, `fun_extend`), `classes` (rows `row_mem` `row_eq` `row_class` `row_class2` `row_ex` `tuples_class`; ∧ = B2, ¬ = B3), `metafun` (`mfun`, `lam_class`, `lam_pred`, `lam_eta`, `mfun_ext`, `mfun_comb`) | §0's `check-base` row |
| D2's five laws hold over 300 seeded formulas each | `IndexTests` |

## 5. Beliefs — NOT verified

- Decision 4's population (`DESIGN.md` §4a: which theorems are cited at a type other than `i`) is a
  scratch probe's, not kept.
- That pass 1 (logic) removes every IFOL-rule and inlined-box class instantiation — reasoning.
- `Pure.dummy_pattern` occurs as a term inside proofs (`AC15_WO6.AC12_AC15`); that its value is irrelevant is a guess.
- 197 term constants in 27 levels (`~/isabelle-object-constants.md`) — no handle.

## 6. Open decisions

1. **Decision 4, deferred** (`DESIGN.md` §4a): an unrestricted type variable — `split`'s case, and
   `MetaExists` — until it blocks.
2. **The branch** `feature/exists-descent` names deleted work and is unpushed: rename, branch fresh, or merge.
3. **The checker branch `qualified-names`**: review, merge, rebuild `-c opt`; then tests can emit Isabelle names.
4. **Regularity and Choice** are unstated in `base/`; `ZF_Base.foundation` and `AC.AC` need them.
5. **`UNPROVED` as `extern`**; **shared subproofs at emission**; **`isaFree`/`abstract`** with no producer;
   **`ifolAll`/`ifolEx` → `isaAll`/`isaEx`**; **`RulePass`**'s two small fixes; **`lower --show refused`**.

## 7. Next action

Logic, pass 1 of `DESIGN.md` §4a: IFOL's thirteen ND rules and `FOL.classical` to the kernel's steps,
inlined boxes reduced at the proof level, and the guard's two `∃` rules it needs. Design its rules with the
user first — the plan names what it removes, not how. Done when `isa2fol lower` runs logic then the guard,
every lowered proof still concludes its statement by ID, and `swift test` passes.
