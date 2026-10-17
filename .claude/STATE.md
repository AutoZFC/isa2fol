# STATE — isa2fol
HEAD (see §0) · primitives · 2026-10-16.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `An instance at a class type: forall_elim at the λ's class at its arguments, then β at each occurrence of the class variable` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `8828` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 14, 136, 97, 110, 41 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`, Proved n of n; `metafun` 18 of 18 |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export` | `proved: 9420` of 9420; cited: 195 named, 956 boxes binding a proposition, all proved |
| `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR` (24 min, peak 25.5 GB), then `scripts/check-unit.sh DIR` | 73 named lowered; 45 parts; claims 4579 of 4579, schemas 111 of 111; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, tree clean. The checker is fol-zfc-comb `224d60e`, branch
`libraries-and-streaming`, unmerged; build it only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE: consulted, never merged.

## 2. Read these first-hand
- `DESIGN.md` "Step 3 — an instance at a class type" — the six agreed decisions, the nine made in the build, Measured:
  where the unit's bytes go.
- `Sources/Lowering/Lambda.swift` — the instance (`R`, `forall_elim` at the opened class), `Beta` per unit, the function
  application's cut, `LambdaProofs` (`atTuple` shared by the predicate and function λ).
- `Sources/Lowering/Instance.swift` — `units`, `converted`, `Sides`, `slotConverted`, `reclosed`: shared by Reify's
  instance at a compound term and Lambda's.
- `Sources/Lowering/Facts.swift` — `closed`: a proposition closes as a letter at a lemma's top.
- `Sources/Lowering/Logic.swift` — `claimed`: an axiom base claims, under the class premises the axiom states.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms, NBG and `elem_first_subst` | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| an instance at a λ concludes the walk's own rewrite of Isabelle's formula, kernel-checked: at variables, compound and nested arguments, a slot, a function λ of one to three arguments, the identity | `LambdaTests` |
| a λ holding a proposition is a schema in it; the class prover refuses it, and its citers fall | `aLambdaHoldingALetterIsASchemaInIt`, `aLambdaHoldingATruthSetVariableIsASchemaCitedAtItsTruth` |
| the congruence walks a class binder by `forall_elim` at the bound class | `aClassBinderBelowTheInstantiatedVariableIsWalkedAtACompoundTerm` |
| `subst` with its class premise stated is base's `class_subst` under it | `substWithItsClassPremiseStatedIsBasesClassSubstUnderIt` |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A FRAME'S VARIABLE READ BEFORE AN `open` OR A `fix` NAMES THE WRONG BINDER AFTER IT.** Three times in step 3 (`τ`,
  `vs` before `K`, `zf.variable(zf.fix(.i))`): the table caught each as `premiseMismatch` or an index out of range. Read
  `frame.variable(level)` where it is used.
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13) — tests too: `lowered(l, try
  helper(&l))` lowered a stale table. Bind first.
- ⚠ **THE TABLE TRUSTS A CITATION'S ROOT.** A base claim standing for an axiom whose statement differs (`subst` and its
  class premise) passes every pass and only the kernel refuses it: kernel-check every new reach.
- ⚠ **`exists_intro` ABSTRACTS EVERY OCCURRENCE OF ITS WITNESS**: close a naming around a fresh `z = value`, then
  instantiate `z` (EX of a variable concluded `∃y. y = y`).
- ⚠ **FOL TRANSFORMS EACH STATEMENT BY ITSELF**: one transform over every root kept one cache for all and passed 32 GB.
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Instances conclude `walked`, the walk's own rule.
- ⚠ **A BOX'S NAME MOVES WITH THE IR'S PRINTED PAYLOAD**: count boxes, never diff their names.
- ⚠ **A LETTER IS THE READER'S, NEVER A POSITION AFTER EXPAND.**
- ⚠ **A SERIAL NEVER REACHES OUTPUT.** A box is named by its proof's content (§4.6 R2).
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **BASE'S STATEMENTS ARE FOL-ZFC; THE WALK'S ARE ISA UNTIL FOL.** They agree by ID only after Fol.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**: run `swift build -c release` before §0's `read` and `lower`.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 73 of 9,420 named lowered; refused: no owner 3,702, logic 3,071, letter off spine 204, cites refused 2,370 | `MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| logic's refusals led by `isaCombination((i => o), o, o)` 2,274 and `isaAbstract((i => o), o)` 1,991 (step 4); no owner by `use(theorem, [i], o)` 1,627, `isaFree(i)` 1,413, `isaDefinition(zf, object, [], args: [])` 1,034 | the same report |
| kernel: 45 parts, claims 4,579 of 4,579, schemas 111 of 111 | `scripts/check-unit.sh DIR` |
| 4,242 of the 4,579 claims (303 of 326 MB) are in the `_uncited` parts: 638 `LAMBDA_` (7 cited), 724 `CLASS_`, 771 EX, 823 UNIQ, 196 `FUNC_` | `grep -c '^claim LAMBDA_' DIR/_uncited*.fol.def`, … |
| the 16 lemmas unbuilt are all `CLASS_`: a λ holding a proposition, which the class prover does not read | a throwaway listing of `unit.refused`, not kept |
| `SOURCE_SURFACE.md` and `CLOSURE.md` unchanged by this step | `isa2fol surface data/zf_export`, `closure`; `diff` empty |
| comments 46/8828 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- All 204 letters off their spine are an instance walking under a `⋀` at `o` the cited theorem binds after the
  instantiated variable — from their three patterns and one test, no per-theorem trace.
- Most uncited lemmas come from statements that fall at a refused citation; the split between that and a letter off the
  spine is not measured.
- 382 instances at a λ holding a letter and 24 holding a truth-set variable (a throwaway count over the read unit).

## 6. Open decisions
- **The uncited lemmas**: 93% of the unit's bytes prove lemmas for statements that then fall. Prune at link what nothing
  cites, or request lemmas only once a statement is known to stay — the user's to choose; neither is designed.
- **The next step**, the user's to choose: step 4, Pure's equality at a function type (Logic's largest refusal now);
  letters instantiated before an instance at a class type (204 off the spine); the class prover reading a letter (S4's
  truth set, 16 `CLASS_`); `use(theorem, [i], o)` 1,627; step 5's ZF definition cited, 1,034; step 7's hidden variable,
  1,413.
- For the user's review: "Step 3 — …"'s nine decisions in the build; "OFCLASS — …"'s seven; and the earlier steps'
  listed in their sections; merging the checker branch.

## 7. Next action
Put the step's outcome and the uncited-lemma question to the user. Done when the user has chosen what comes next.
