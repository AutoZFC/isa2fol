# STATE — isa2fol
HEAD (see §0) · primitives · 2026-10-16.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `git branch --show-current` | `primitives` |
| `git log -1 --format=%s` | `OFCLASS by its class's definition: a definition defines what its left side is, and a generic theorem cited at a type is its proof there` |
| `git status --short \| wc -l` | `0` |
| `git rev-parse --short kinds-proposal` | `21ca100f` |
| `find Sources -name '*.swift' -exec cat {} + \| grep -cv '^\s*$'` | `8381` |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h` | `224d60e` (branch `libraries-and-streaming`) |
| `grep -c '^axiom ' base/axioms.fol.def` | `17` — NBG and `elem_first_subst`; the tiers admit none |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep "Test run with"` | five lines, all passed: 136, 109, 82, 41, 14 tests |
| `MEM=16G scripts/capped.sh bash scripts/check-base.sh` | 14 tiers, each `exit 0  stderr 0`, Proved n of n; `truth` Schemas proved (2 of 2) |
| `swift build -c release`, then `MEM=32G scripts/capped.sh .build/release/isa2fol read data/zf_export` | `proved: 9420` of 9420; cited: 195 named, 956 boxes binding a proposition, all proved |
| `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export --emit DIR`, then `scripts/check-unit.sh DIR` | 65 named lowered; 40 parts; claims 2222 of 2222, schemas 110 of 110; exit 0 |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
`/home/arthur/repos/isa2fol`, branch `primitives`, no upstream, tree clean. The checker is fol-zfc-comb `224d60e`, branch
`libraries-and-streaming`, unmerged; build it only with `bazel build -c opt`. `kinds-proposal` (`21ca100f`) is the
REFERENCE: consulted, never merged.

## 2. Read these first-hand
- `DESIGN.md` "OFCLASS — a class's membership by its definition, and a generic theorem in place" — the three decisions,
  the seven made in the build (6: Reify's instance and `walked`), Measured: where the 5,601 went.
- `DESIGN.md` "The steps after class existence, in order" — where the order of work stands.
- `Sources/Reader/Reader.swift` — `definiendum`, `axiom(defining:)`, `definition(of:at:)` for a class, and `head`'s
  generic theorem in place.
- `Sources/Lowering/Expand.swift` — the membership piece; definitions keyed by `(Definiendum, axiomTypes)`.
- `Sources/Lowering/Instance.swift` and `Congruence.swift` — `walked(_:base:in:)` as the instance's conclusion; the
  truth set's binder in the congruence.

## 3. Invariants
| invariant | enforced by |
|---|---|
| a unit is valid only when every part exits 0, stderr empty, every claim and schema Proved | `scripts/check-unit.sh`, `check-base.sh` |
| nothing Isabelle states is admitted: base admits 17 axioms, NBG and `elem_first_subst` | §0's `grep`; `check-base.sh` |
| each pattern has the owner the division gives it, one at most | `eachPatternHasTheOwnerTheDivisionGivesIt` |
| a definition defines what its left side is; a class membership unfolds by its class's definition | `aCitationOfAClassDefinitionDefinesTheClass`, `aClassMembershipUnfoldsByItsClassDefinitionAndACitationOfItIsReflexive`, `aClassMembershipIsLoweredByItsDefinitionAndProved` |
| a theorem no class restricts, cited at a type and binding no proposition on its spine there, is its proof in place | `aGenericTheoremCitedAtATypeIsItsProofThereInPlace`, `aTheoremWithATypeVariableNotRestrictedToTermIsReadAsStated` |
| an instance at a compound term concludes the walk's own rewrite, truth sets rendered | `aClassPremiseCitedAtACompoundTermIsLoweredAndProved`, `aTruthSetHoldingTheInstantiatedVariableIsLoweredAndProvedAtACompoundTerm` |
| an application of a definition is one node at its terms, `reflexive` there | `anAppliedDefinitionIsReadAtItsTerms`, `aDefinitionAtItsTermsIsLoweredAndProved` |
| a box binding a proposition is cited by `<theory>.BOX_<fingerprint>`, the same at any serial | `aBoxBindingAPropositionIsCitedByItsContentsName` |
| every build, test, checker and lowering run is capped | `scripts/capped.sh` |

**Standing warnings — each repeated silently otherwise:**
- ⚠ **A SECOND COPY OF A PASS'S REWRITE DIVERGES SILENTLY.** Reify's instance at a compound term computed its conclusion
  by naming alone; once Logic rendered truth sets inside formulas, only a corpus run found it (`noCongruence`). It calls
  `walked`, the walk's own rule.
- ⚠ **A BOX'S NAME MOVES WITH THE IR'S PRINTED PAYLOAD** (its fingerprint hashes each node's description): a box "gone"
  between runs after an IR change is renamed, not lost. Count boxes, never diff their names.
- ⚠ **A LETTER IS THE READER'S, NEVER A POSITION AFTER EXPAND.** Expand unfolds a definition's `⋀` (`&&&`, `TERM`) onto a
  statement's top; read by position there, one formula took two readings and the table refused the step.
- ⚠ **A REGEX ADDING NEW KINDS TO CATCH-ALL LISTS ALSO EXTENDS DEDICATED CASES**: match the list's text, count per file.
- ⚠ **A SERIAL NEVER REACHES OUTPUT.** A box is named by its proof's content (§4.6 R2).
- ⚠ **NO RULE READS A NODE BESIDE ITS OWN PIECE.** A rule reads its premises' conclusions, never their proofs' shapes.
- ⚠ **`x.f(try x.g(…))` READS A COPY OF `x` TAKEN BEFORE `g` MUTATES IT** (rule 13). Bind first.
- ⚠ **BASE'S STATEMENTS ARE FOL-ZFC; THE WALK'S ARE ISA UNTIL FOL.** A truth set's binder is fol-zfc's own `∀`.
- ⚠ **THE RELEASE BINARY IS NOT REBUILT BY `swift test`**: run `swift build -c release` before §0's `read` and `lower`.
- ⚠ **STATE GOES IN ITS STEP'S COMMIT**, never a commit of its own.

## 4. State
| claim | verified by |
|---|---|
| `lower`: 65 of 9,420 named lowered; refused: no owner 3,702, logic 3,955, letter off spine 13, cites refused 1,685 | `MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export` |
| no owner led by `use(theorem, [i], o)` 1,627; logic by `isaAllElim(o, (i => o))` 2,820; refused citations by `Formula.satisfies_DEF` 63 | the same report |
| kernel: 40 parts, claims 2,222 of 2,222, schemas 110 of 110; `ZF_Base.arity_term_i` is `forall b0. (truth(b0) -> (holds(b0) -> holds(b0)))` | `scripts/check-unit.sh DIR`; `grep arity_term_i DIR/ZF.ZF_Base.fol.def` |
| `SOURCE_SURFACE.md`: 1,573 patterns; `CLOSURE.md` unchanged by this step | `isa2fol surface data/zf_export`, `closure` |
| comments 40/8381 = 0.5% of `Sources` | `CLAUDE.md` rule 9's script |

## 5. Beliefs — NOT verified
- The 13 named theorems off their spine (listed in DESIGN "A definition read at its terms", Measured) are unchanged in
  count and patterns; their source is not traced.
- `notI`, `notE`, `iffI`, `iffD1` wait on `IFOL.not_def` / `iff_def`, whose boxes bind a variable of type `o ⇒ o`.
- Most of the 2,820 at `isaAllElim(o, (i => o))` are `spec` and `subst` at a λ, now past their class premise (from the
  report's pattern alone; no per-theorem trace).

## 6. Open decisions
- **The next step**, the user's to choose: step 3, an instance at a class type (`isaAllElim(o, (i => o))` 2,820, Logic's
  largest); a theorem binding a proposition cited at a type (`use(theorem, [i], o)` 1,627, `FOL.meta_simps.1`): its
  instance as a named schema; a ZF definition cited (step 5, `isaDefinition(zf, object, [], args: [])` 1,034); the hidden variable
  (step 7, `isaFree(i)` 1,413); `not_def`/`iff_def`; `exI`; tracing the 13 off their spine.
- For the user's review: "OFCLASS — …"'s seven decisions in the build; "A definition read at its terms"'s two; "Functions
  of propositions and the bound `⋀P`"'s seven; "Boxes binding a proposition"'s three and four; "The logic's rules read as
  steps"'s four; step 2's `Equalities.atI`; emission's seven; merging the checker branch.

## 7. Next action
Put the next step to the user, in the docs' own terms: which of §6's first item comes next. Done when the user has chosen.
