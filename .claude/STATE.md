# STATE — isa2fol
The commit that adds this file (parent `19dafdc2`) · `feature/exists-descent` · 2026-09-28.  **RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is at `~/.local/bin` — not on a non-login shell's PATH. Run from the repo root, after `swift build -c release`.

| command | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | `202` |
| `find Sources Tests -name '*.swift' \| wc -l` · total lines | `44` · `5744` |
| comment density of `Sources` (CLAUDE.md rule 9's script) | `9/2621 = 0.3%` |
| `grep -rnE '^\s*default:' Sources \| wc -l` | `0` |
| `.build/release/isa2fol read data/zf_export \| grep -A1 -E '^named'` | `proved: 9420` · `…outside the ZF sessions: 200` / `proved: 200` |
| `.build/release/isa2fol lower data/zf_export \| grep -E '^(lowered\|refused\|  guard)'` | `lowered through guard: 2685 — …` · `refused: 6735` · `  guard: compoundInstantiation: 6735` |
| `.build/release/isa2fol surface data/zf_export \| grep '^\| \*\*all'` | `\| **all** \| **9420** \|` |
| `find data/zf_export -path '*/proofs/*' -type f \| wc -l` | `38923` — else `bash scripts/03-export-zf.sh` |
| `readlink ~/repos/fol-zfc-comb/bazel-bin \| sed 's\|.*bazel-out/\|\|'` | `k8-opt/bin`, `proof_checker` executable there |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h qualified-names` | `487c68c` (unmerged) |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

`/home/arthur/repos/isa2fol`, branch `feature/exists-descent`, clean, 144 commits not pushed
(`git rev-list --count origin/feature/exists-descent..HEAD`). fol-zfc-comb sits on its own
`comb-verifier` with an uncommitted `MODULE.bazel.lock` that is the user's; leave both alone.
`git worktree list` also shows `../isa2fol-build` and `.claude/worktrees/agent-*`: not this work.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `Sources/IR/Traversal.swift` | `Rule`: `Context`, `start`, `enter`, `narrow`, `before`, `after`; `transform(roots)` → `[Rewrite]`; the cache key `(node, narrow(context))`; a `Refusal` caught per root |
| `Sources/IR/Pass.swift` | `Pass`, `RulePass` (fixpoint over live roots), `Statement`/`Unit`/`Refused`, `Pipeline` — pass by pass, the conclusion check BY ID |
| `Sources/Lowering/Guard.swift` | pass 1: `isaBound(k, i)` → `folBound(k)`; `set` is `folPred`; the `fix(guarded:)`/`assume` stack; discharge and renumbering; `compoundInstantiation` |
| `DESIGN.md` **§4.5, §4a** | the framework as built; pass 1, and the compound route it forces |
| `docs/FOUNDATION.md` **§2** | S1–S5: constants as graph predicates, arguments as class parameters — the next pass |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 AND stderr is empty | the two real-checker tests in `Tests/FolDialectTests` |
| Equal content is one node; an ill-formed node cannot exist | `Table.intern` (`TableTests`, `ProofTests`) |
| Every proof read concludes its statement, BY ID; every lowered one too | `Reader.prove`; `Pipeline.run` → `PipelineError.unproved` |
| The reader emits only the isa dialect; no isa-only kind reaches the text | `theReaderEmitsOnlyTheIsaDialect`; `legalize`; `render` throws `sourceKind` |
| A pass `Refusal` ends only its own root; any other error stops the run | `aRefusalStopsOnlyItsOwnRootAndKeepsTheCache`, `anErrorThatIsNotARefusalStopsTheWalk` |

**Standing warnings — silent or misleading if repeated:**

- **⚠ `Conditional` IS NOT `Proved`; NEVER SUM THEM.** A claim with no proof block is not citable.
- **⚠ THE READER CHOOSES NOTHING** — which types, what `OFCLASS` becomes: translation's (`DESIGN.md` §4.3a 3, 5).
- **⚠ A CITATION IS `head % terms %% discharges`** — the ∀-closure is outermost.
- **⚠ BINDER KNOWLEDGE LIVES ONLY IN `mapChildren`** — a second list is D2's silent de Bruijn error.
- **⚠ A RULE MUST BE A FUNCTION OF (node, context, table)** — the cache hands a stateful rule each key once.
- **⚠ `transform` SURVIVES PROOFS ONLY THROUGH ITS CACHE, KEYED ON THE NARROWED CONTEXT** — keyed on the full
  context one proof exceeds 150 M rewrites; a tree walk is exponential (the 3.1 GB file).
- **⚠ THE GUARD IS ONE WALK, NEVER A `RulePass`** — rerun, it guards its own output forever.
- **⚠ `folPred` TAKES ONLY A `folBound`** — `set(t)` cannot be written for a compound `t`; that is S1 as a type.
- **⚠ A SECOND REFERENCE TO `unit.table` COPIES THE WHOLE TABLE** at the pipeline's first write (copy on
  write): `Lower.swift` lowers the one `unit` in place. `Unit` there is `IR.Unit` — Foundation has one.
- **⚠ A MUTATION THAT DOES NOT COMPILE PRINTS NO FAILING TEST** — read the build output before calling one caught.
- **⚠ `false`, LOWERCASE, IS ⊥** — `False` lexes as a nullary predicate (`probe_bottom`).
- **⚠ NO NAME MANGLING** (CLAUDE.md rule 5); real-checker tests use plain names until `qualified-names` is merged.
- **⚠ NEVER ITERATE A `Dictionary`/`Set` TOWARD OUTPUT** — `Hasher` is seeded per process (§4.6).
- **⚠ `t.type(of: try t.intern(…))` AND `t[try t.intern(…)]` READ THE TABLE BEFORE THE INTERN** — intern into a `let` first.
- **⚠ REORDERING OR ADDING `Node` CASES LEAVES DEPENDENT MODULES ON THE OLD LAYOUT** in an incremental
  build — `rm -rf .build/out/Products .build/out/Intermediates.noindex`.
- **⚠ `pgrep -f` IN A WAIT LOOP MATCHES ITS OWN COMMAND LINE**; run jobs in sequence.
- **⚠ BUILDING fol-zfc-comb IN DEFAULT CONFIG REPOINTS `bazel-bin` TO `k8-fastbuild`**; restore
  `ln -sfn <execroot>/bazel-out/k8-opt/bin bazel-bin`. Its `//src/library` needs `--cxxopt=-Wno-error=stringop-overflow`.
- **⚠ A SERIAL NAMES A THEOREM ONLY WITHIN ONE BUILD, AND ONLY WITHIN ITS THEORY** — never in a test, fixture or doc.
- **⚠ `data/zf_export` IS ONE BUILD OR NOTHING** — rebuilt whole, never patched.
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED.**

## 4. State

| claim | verified by |
|---|---|
| The reader proves ALL 9,420 named theorems of the 8 exported sessions as Isabelle states them, plus the 200 named Pure/IFOL/FOL theorems their proofs reach; 0 refused | §0's `read` row |
| A citation is `use(name, types, root)`; `render` refuses a typed `use`, so no real proof renders yet | `aCitationCarriesItsTypes`, `aCitationOfAnInstanceIsNotRendered` |
| `render` emits formulas and proofs the REAL checker proves, every rule family | `theRealCheckerProvesWhatEmissionWrites`, `theRealCheckerAcceptsWhatRenderEmits` |
| The framework: `Statement` is `(name, root, proof)`; `enter` runs once per BOUND child; the cache shares a node across contexts that narrow alike and across roots of one walk; `Unit.refused` records `(name, pass, refusal)` | `TraversalTests`: `aRuleSeesTheContextItsBindersMade`, `aNodeSeesOnlyTheContextItsRuleNarrowedTo`, `aSharedNodeIsRewrittenOncePerContext`, `oneWalkOverSeveralRootsRewritesASharedNodeOnce`, `aPipelineRecordsARefusedStatementAndLaterPassesNeverSeeIt` |
| Pass 1, the guard: 2,685 of the 9,420 lowered, each proof concluding its guarded statement BY ID; 6,735 refused, all `compoundInstantiation`. The check is the TABLE's: the output is still isa, `legalize` refuses it, no kernel has seen it | §0's `lower` row; `LoweringTests` (7) |
| `claimName` is public (`name(4)` → `name.4`); the unit's names are the ones citations use | `aTheoremsClaimNameIsTheNameItsCitationsUse` |
| Proofs rest on Pure/IFOL/FOL axioms and defs, ZF_Base's 6 axioms, `AC.AC`, 984 ZF definitions, and 5 example-session axioms with no proof anywhere; 0 oracles | `.build/release/isa2fol closure data/zf_export` (`docs/CLOSURE.md`) |
| `base/` states 17 of FOUNDATION §1's 19 axioms — not Regularity, not Choice — and the 5 primitives' graphs with EX/UNIQ/CONG | `base/axioms.fol.def:19`; `base/tiers/primitives`, `base/tiers/skolem` |
| D2's five laws hold over 300 seeded formulas each | `IndexTests` |
| The tests have teeth: mutations of `Traversal.swift`, `Pass.swift`, `Guard.swift` are each caught | re-run by hand after touching them |

## 5. Beliefs — NOT verified

- Distinct `⋀x::i` elimination steps: 121,120 at a bound variable, 179,745 at a constant applied, 3,850 at a
  function variable applied — a throwaway probe, not kept. Likewise the cache figures in DESIGN §4.5.
- `Pure.dummy_pattern` occurs as a term inside proofs: `AC15_WO6.AC12_AC15` instantiates `refl` at
  `cons(0, Sigma(dummy_pattern(…), λ_. nat))` (a throwaway probe). That its value is irrelevant is a guess.
- Once compound terms become variables through their constants' EX (S1), every current refusal lowers — reasoning.
- Every export citation resolves; 197 term constants in 27 levels (`~/isabelle-object-constants.md`) — no handle.

## 6. Open decisions

1. **The branch** `feature/exists-descent` names deleted work and is unpushed: rename, branch fresh, or merge.
2. **The checker branch `qualified-names`**: review, merge, rebuild `-c opt`; then tests can emit Isabelle names.
3. **`UNPROVED` as `extern`**: ban at the final link, or per unit?
4. **Shared subproofs at emission**: emission unfolds a shared subproof per use; name them by content.
5. **`isaFree` and `abstract`** have no producer: delete, or keep?
6. **Generic theorems** and **what `OFCLASS` becomes** (translation's).
7. **Rename `ifolAll`/`ifolEx` → `isaAll`/`isaEx`**: yes or no.
8. **Regularity and Choice** are unstated in `base/`; `ZF_Base.foundation` and `AC.AC` need them. And where the
   proofs of ZF_Base's axioms from `base/` live — a `base/` tier or a pipeline unit. `DESIGN.md:339` still says
   "the target's axioms"; they are to be PROVED from `base/`, not admitted.
9. **`RulePass`**: a refusal counts as a change (one wasted round), and `if case .rewritten(id)` reads as a
   binding while it compares. Two small fixes offered, not decided.
10. **`isa2fol lower --show refused`** with a printer for isa terms: offered, not decided.
11. **`Pure.dummy_pattern` inside proof terms**: how S1 treats a term with no definition.

## 7. Next action

Draft the next pass in `DESIGN.md` §4a for the user's review — Isabelle's meta-level functions grounded in
NBG, from `FOUNDATION.md` §2: CONSTANTS as graph predicates `F(x⃗, r)` with EX/UNIQ/CONG (S1–S3), in
definitional order from `base/tiers/primitives`, each compound instantiation becoming one at a variable
whose EX delivers `set(r)`; `λ` ARGUMENTS as class parameters (S5) after. No code before approval. Done
when the user approves the section.
