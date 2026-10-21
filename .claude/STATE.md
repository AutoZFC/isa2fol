# STATE — isa2fol
HEAD "`AC.AC`: Choice pinned as Gödel's axiom E; Isabelle's AC by `lam_type` at base's choice function" (parent "Memory
under the CI's 32 GB: …") · primitives · 2026-10-21. RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
`$ZF` is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,ZF-Resid,ZF-ex`: every run is the ZF session alone
until it is fully translated (user). Lint before every run: `pre-commit run --all-files`.

| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -2 --format=%s` | `` `AC.AC`: … ``, `Memory under the CI's 32 GB: …` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --abbrev-ref primitives@{upstream}` | `origin/primitives` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `17606` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `7405a6f` (branch `remove-eq-subst`: no `eq_subst`); `bazel-bin/src/tools/proof_checker` built 2026-10-19 15:47 PDT from `37ae807`, the binary that checked §0's unit; `7405a6f` renames a section header |
| `grep -c '^axiom ' base/axioms.fol.def` | `19` — FOUNDATION §1's all: NBG with Regularity and Choice (Gödel's E), and `elem_first_subst`; the tiers admit none |
| `pre-commit run --all-files` | `SwiftFormat ... Passed`, `SwiftLint ... Passed` |
| `MEM=48G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | 14, 142, 172, 135, 51 passed — none failing |
| `MEM=16G scripts/capped.sh scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`; `axioms` 9 of 9 (`choice_singleton`), `metafun` 19 of 19 (`choice_function`), `zf` 22 of 22 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR --threads 16` (25:33, peak 17.5 GB), then `MEM=32G scripts/capped.sh scripts/check-unit.sh DIR` | `lowered … 3609`; `refused, named: 7`, all `no owner` (a type no class restricts); `lemmas … unbuilt: 0`; 97 parts, every one `exit 0  stderr 0`; claims 50306 of 50306, schemas 6273 of 6273; 4,518,493,956 bytes; `table: 152096494 nodes`; stages `expand 4.7 s, logic 279.5 s, registry 483.9 s, fol 530.8 s` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, upstream `origin/primitives` (`git@github.com:AutoZFC/isa2fol.git`).
The checker is fol-zfc-comb, the user's, built only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE.

## 2. Read these first-hand
- `DESIGN.md` "Memory under the CI's 32 GB": the three costs measured, the two root causes, Built, Measured.
- `DESIGN.md` "`AC.AC`": Gödel's E, base's `choice_function`, the lemma's isa proof; its decisions in the build.
- `Sources/Lowering/Axioms.swift` — `chosen`: the isa proof of `AC` that Logic's walk lowers.
- `Sources/Lowering/Fol.swift` — `FolRule.Context`: a reference into the walk's chain of binders, never a copy.
- `base/axioms.fol.def` (`choice`, its note) and `base/tiers/metafun.fol.def` (`choice_function`).

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits FOUNDATION §1's 19 axioms and nothing else | §0's `grep`; `check-base.sh` |
| a node is 16 bytes, a type one word: a wide kind behind a reference | `aNodeIsSixteenBytesAndATypeOneWord` |
| Fol's context is a reference into the walk's chain of binders; a formula's is the empty one | `FolContextTests` (four) |
| `AC.AC` is derived from axiom 19: base's choice function and the unit's `func.lam_type` | `AxiomTests.choiceIsProvedByLamTypeAtBasesChoiceFunction`, `choiceWithoutLamTypeIsRefusedCitingIt` |
| a prover reads a named statement as the proving pass took it and as it left it | `theRegistryHandsItsProversEachNamedStatementAsTheProvingPassTookItAndLeftIt` |
| an `∃` at every object type is eliminated, a guarded one by two cuts | `anExistentialAtAFunctionTypeIsOpenedByItsGuard` |
| every build, test, checker and lowering run is capped; lint before every run | `scripts/capped.sh`; `pre-commit run --all-files` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A NAMED SET IS READ FROM THE PARTS BY EXCLUDING THE GENERATED SUFFIXES BY NAME** (`_UNFOLD`, `_AXIOM`, `_CLASS`,
  `_LIFT`, `_EX`, `_UNIQ`, `_FUNC`, `_TOTAL`, `_AGREE`), never by any uppercase suffix: `equalities.Union_eq_UN`,
  `Ordinal.Ord_INT` are theorems. The parts are `ZF.fol.def` and `ZF.*.fol.def`: `ZF.*` alone misses theory `ZF`'s.
- ⚠ **A NODE IS 16 BYTES**: a kind wider than three children and a type goes behind `indirect`, or every node pays
  for it (80 bytes, 20.3 GB at 151M nodes). ⚠ **A WALK'S CONTEXT IS NEVER COPIED INTO A KEY**: Fol's keys held 9 GB
  in one walk, and the heap kept it.
- ⚠ **`t[try f(…, &t)]` READS A COPY TAKEN BEFORE THE MUTATION** (rule 13): bind the interned node first.
- ⚠ **A PROVER WRITES AN ISA PROOF AND LETS LOGIC'S WALK LOWER IT** where the proof instantiates at λs or holds
  terms: written in Logic's form, its instances and values would be a second copy of Logic's rules.
- ⚠ **AN INSTANCE AT A SET TERM IN STATEMENT FORM IS A PROOF'S INSTANCE MET BACK**: there is no statement-form instance
  at a term.
- ⚠ **THE SURVEY IS A CLASS**; ⚠ **`Sharing.premises` IS `render`'s CITATIONS**; ⚠ **A CLOSURE IS COUNTED IN TEXT**.
- ⚠ **THE INDEX NEVER HOLDS A NODE AGAIN**; ⚠ **THE IMPORT HOLDS NO REFERENCE TO THE LAYER'S BOX**; ⚠ **A PASS'S WALK
  IS BUILT ONCE A RUN**.
- ⚠ **A PROVER'S ERROR OTHER THAN `MeetingError.unmet` IS FATAL TO THE RUN**.
- ⚠ **BASE'S `_NBG` STATEMENTS AND `choice_function` ARE THE TRANSLATOR'S WORDS, CHECKED ONLY BY THE KERNEL.**
- ⚠ **A LOST THEOREM IS FOUND BY DIFFING NAMED SETS ACROSS RUNS, NEVER BY THE COUNT ALONE.**
- ⚠ **THE CHECKER KEYS A DERIVED FACT BY ITS FORMULA**: never cite a step outside the block that wrote it.
- ⚠ **`pkill -f`/`pgrep -f` MATCH THE SHELL RUNNING THEM**: find a run by `ps`, kill by PID; ⚠ **A VARIABLE SET IN A
  BACKGROUNDED `&&` CHAIN IS NOT SET AFTER IT** — write the chain as a script.
- ⚠ **`pre-commit run --all-files` LINTS TRACKED FILES ONLY** (`git add -N` a new file); ⚠ **THE RELEASE BINARY IS NOT
  REBUILT BY `swift test`**; ⚠ **STATE GOES IN ITS STEP'S COMMIT**.

## 4. State
| claim | verified by |
|---|---|
| ZF (3,616 named): 3,609 lowered — the 3,565 of the step before, name for name, and the 44 of `AC.AC`'s chain, `Zorn.Zorn` and `Zorn.Hausdorff` among them | §0's complete run; its parts' names diffed against the run before |
| every proof and statement of the run before is the same text; 867 proofs added | §0's unit diffed, proof by proof, against the run before |
| refused, named: 7 — `pair.split`, `pair.expand_split`, `ZF_Base.split_def`, `QPair.qsplit`, `QPair.expand_qsplit`, `QPair.qsplit_def`, `Inductive.def_trans`: a type no class restricts, the ceiling | §0's complete run; `DESIGN.md` "A named theorem at a type no class restricts"; FOUNDATION §3b |
| the complete run fits the CI's `MEM=32G`: 25:33, peak 17.5 GB at emission; lowering under 8.0 GB | §0's run under `/usr/bin/time -v`, RSS sampled every 15 s |
| comments 296/17606 = 1.7% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- Against Isabelle's size: exponent 1.10 against its DAG over the statements measured before "`AC.AC`"; Logic's
  growth per Isabelle step, 3–17 distinct steps after Fol where measured, is what is left above linear.
- Emission adds about 10 GB over lowering: every proof's text held until the last is rendered (4.3 GB) and sixteen
  threads' working memory — measured at the step before, not split by cause since.

## 6. Open decisions
- **The ZF session is translated to its ceiling**: what comes next is the user's — the other seven sessions of the
  export (`ZF-AC` … `ZF-ex`, each `--skip`ped now), proof size (Logic's growth per Isabelle step), or emission's memory.

## 7. Next action
Get the user's choice among §6. Done when the user has chosen.
