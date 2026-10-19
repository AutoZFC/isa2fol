# isa2fol: Isabelle/ZF to FOL-ZFC Translator

## Active development: Swift, at the repo root

The Rust tree (`rs/`, 12,781 lines) was **deleted 2026-09-22**. It is in git
history and nothing depends on it. `docs/`, `base/` and `scripts/capped.sh`
were hoisted out of it first and are live.

**The reader is built.** `isa2fol read data/zf_export` reads every named theorem of
the ZF sessions, statement AND proof, into the IR: ALL 9,420 are proved — the proof's
conclusion is the statement's node, by ID — and 0 are refused (`DESIGN.md` §2). Nothing is
absorbed: a type variable is `IRType.variable`, a class membership `isaOfClass` — and a theorem whose every type variable
is restricted to `term` is read at `i`, the only type in `term` ("Step 1"); one no class restricts, cited at a type, is
its proof read there, in place, when it binds no proposition on its spine there ("OFCLASS — …", 3), and its instance
there a statement of the unit, named by its proof's content, when it binds one ("A theorem cited at a type"). **The input layer is
`DESIGN.md` §4.3b**: Pure, IFOL, FOL and ZF contribute axioms and constants, read as typed values — Pure's equality
rules, and the logic's natural-deduction rules fol-zfc has, read as their steps ("The logic's rules read as steps") —
`Constant` (primitive · defined · declared), `Cited` (theorem · definition · axiom · theory axiom,
and lowering's lemma and base's schema); a
leaf FOL has reads as its node, a defined constant as defined, at its declared level (object · meta); a gap in the
dialect stops the read.
**Lowering is the plan of three passes, declared whole** (`DESIGN.md` §4a, "Lowering's components"): expand ·
logic · fol. **Reify is no pass**: the logic pass's walk calls its code ("Reify called from Logic's walk"). Each pass
owns patterns by ONE exhaustive switch over `Pattern`; the pipeline refuses a statement holding a pattern no pass owns
before the first pass, and one a pass owns unbuilt at that pass. **The registry is no pass**: after logic it hands
each lemma a pass cites to the component that states it, which proves it or answers unbuilt. The unit holds the
named theorems, the 194 they cite outside the ZF sessions, the 951 boxes binding a proposition and the 1,005 definitions
they reach; a statement citing a refused one falls ("The unit and its citations"). Expand (the logic's defined constants and ZF's meta-level ones
unfolded, a definition read at its terms as the `reflexive` step there, a class's membership by its class's definition), Logic (a `⋀P::o` at a statement's top a schema
letter, `schema_inst` at a citation, and Pure's `⋀` over a proposition below it a truth set, `∀E. truth(E) → φ*`, its variable
`holds(E)`; Pure's equality at a function of propositions pointwise over truth sets; `subst` base's `class_subst`; `classical` and `iff_reflection`, which the reader
reads as isa steps, the kernel's after Expand; Pure's equality, which the reader reads as steps, as base's `iff_*` at `o`
and `eq_*` at `i`, base's schemas parsed from base's own text), Reify in Logic's walk (S1: a term and a λ in a class slot named where they stand; a constant's
class by its `@def`, which its prover states from the definition; an instance at a compound term by EX and UNIQ of the
term) and Fol (the guard Reify gives each object type — `set`, `function`, none — fol-zfc's variables, `∃` at `i`) have
rules, and an instance at a class type is Lambda's (`DESIGN.md` "Step 3 — an instance at a class type": `forall_elim`
at the λ's class at its arguments, `LAMBDA_<fp>`, then β at each occurrence of the class variable — its slot's class
kept, an application at its value), and Pure's equality between functions is Logic's (`DESIGN.md` "Step 4 — Pure's
equality between functions": pointwise, `f ≡ g` read `⋀x⃗. f x⃗ ≡ g x⃗`, the λs wrappers; `combination` the premise at
the argument, then the argument's equation substituted into the function by the replacement walk). **A statement's
letters come first** (`DESIGN.md` "Letters first"): the reader closes a theorem over its propositions before its other
frees and permutes each citation's leading term arguments to match, so a letter is instantiated by `schema_inst` on the
citation and no instance walks a binder over a proposition; an axiom keeps the export's order. **A proposition as an
argument is its truth set** (`DESIGN.md` "Step 6"): `If`, `bool_of_o` take a proposition, an entry of the argument tuple
named where it stands. **In a proof, a term is its value** (`DESIGN.md` "Proof size", "Linear proof size"): a term whose
variables the proof has fixed is fixed once, by `exists_elim` over its EX, and every formula the proof passes holds the
value; a statement keeps S1's naming, universal (`∀v. ⟦v = t⟧ → φ(v)`); where a formula meets the proof's values, a lemma
proved once per formula crosses them — `MEET_<fp>`, `BETA_<fp>` at a λ (its class variable's application read at its
arguments' names), `SUBST_<fp>` Leibniz, `ARGS_<fp>` — below a statement's letters, which stay on its spine. Of the ZF
session's 3,616 named theorems (`--skip` the other seven), `lower` lowers 369 to fol-zfc: 7 stop at no owner, 1 at logic
(`AC.AC`, Choice), and 3,239 cite a refused statement, led by a box of `ZF_Base` (595) and `FOL.int_ex_simps.2` (296),
each at a variable only the proof uses beyond objects — a `@def` holding a piece not built, or a theorem refused for one
of the others. **ZF's axioms are theorems of base read back into Isabelle's form**
(`DESIGN.md` "Step 8 — ZF's axioms, derived from NBG"): base states each in NBG's words — a primitive by its relation,
a predicate Isabelle defines by its definition — and proves it, Regularity pinned for `foundation`; a lemma per axiom,
`ZF_Base.a_AXIOM`, reads the words back, a named predicate by its `c_UNFOLD`, a primitive's application by its class at
its tuple, `infinity`'s `succ` by `upair.succ_iff`; the registry hands provers the unit's named statements, and emission
places a statement no earlier than what it cites. `infinity` waits on `succ_iff`, which falls with `upair.UpairI2`
through `Replace_iff`. **The definition command's local constant at a function of classes or of propositions is
substituted where its box is cited** (`DESIGN.md` "Step 9 — the definition command's local constant", "Step 9,
widened"): a box binding a variable whose type takes a function or a proposition is read at its citation, its proof at
the cited terms, and never a schema though it binds a proposition; Expand reads Pure's `combination`, `symmetric` and
`transitive` at a type with an argument taking a function or a proposition as `reflexive` where they conclude `t ≡ t`,
the only reading they have. **A ZF
definition cited is its constant's pointwise definition** (`DESIGN.md` "Step 5 — a ZF definition cited"): `c_UNFOLD`,
cited and instantiated at the terms, proved by Reify's prover from the `@def` through Lambda's conversion of a class at
its tuple, the slot classes of class parameters read back by Lambda's β. **The rules that consumed a proposition where it stood are removed**
(`DESIGN.md` "Removed — the rules that consumed a proposition where it stood"): FOUNDATION S4 makes a proposition an
object as its truth set. **A proposition bound below a statement's top and a function of propositions have its rules**
(`DESIGN.md` "Functions of propositions and the bound `⋀P`"): the reader reads Pure's `⋀` over a proposition apart from a
statement's own variables, `isaPropAll`, `isaPropIntro`, `isaPropBound`, and Logic reads them by kind, from base's `truth`
tier (`holds`, `truth`, `truth_EX`, `weaken`). **An ∃-intro states its body** (`DESIGN.md` "An ∃-intro carrying its
body"): `isaExIntro(p, x, body: P)`, the reader's `exI` and every closing lowering builds, written through base's
`ex_intro` — fol-zfc's `exists_intro` binds every occurrence of its witness. **A variable only the proof uses is bound at
its proof's top** (`DESIGN.md` "Step 7"): `isaHidden(T, body)`, `exists_elim` over its type's inhabitation, base's
`set_inhabited`, `function_inhabited`, `truth_inhabited`. **A box binding a proposition is a schema of the unit**
(`DESIGN.md` "Boxes binding a proposition, read as schemas"): an unnamed theorem a proof cites, named
`<theory>.BOX_<fingerprint of its proof>` — never its serial — and cited by `schema_inst`, unless it binds a variable
step 9 substitutes; any other box is inlined.
**A definition is read at its terms** (`DESIGN.md` "A definition read at its terms"): an application of a definition
axiom is one node, `isaDefinition`, which Expand proves `reflexive` there — no schema, no binder. **`OFCLASS` is its
class's definition** (`DESIGN.md` "OFCLASS — a class's membership by its definition"): a definition defines what its left
side is, a constant or a class's membership (`Definiendum`), and Expand states `OFCLASS(i, term)` as `⋀P. P ⟹ P`, true;
`arity_term_i` proves it by `term_class.intro` in place at `i`. Reify's instance at a compound term concludes the walk's
own rewrite of the instance (`walked`), truth sets rendered. The logic's facts reach
the kernel through theirs (`IFOL.conjunct1`, `TrueI`, `refl`, `spec`, `subst`, `FOL.ccontr`, `Pure.protectD`,
`conjunctionI`, `not_def`, `iff_def`, `notI`, `iffD1`, `iffD2`, …), and with them 51 `mutual_induct`s;
`FOL.IFOL_simps.32` and `int_all_simps.3` stop at a variable only the proof uses, at `o ⇒ i` and `(i ⇒ o) ⇒ o ⇒ i`. **EX and UNIQ have their prover** (`DESIGN.md` "EX and UNIQ — their
prover"): a term's naming walked binder by binder, one fact per piece, per constant, per closed λ and per arity, a
constant's from its `@def` and a primitive's from base. **Class existence has its prover** (`DESIGN.md` "Class existence
— its prover", FOUNDATION §3, R5, R4): a formula's class of records built from base's rows and read back exact, named by
`member_class` or `graph_class`; a class binder a hypothesis of what lies under it; one lift per class-taking constant,
uniform in the record's length, re-keyed by `REKEY`; S1's tuple formula one atom, `TUPLE_ROW_n`, proved once per arity
at symbolic positions, and a level one fact, base's `snoc_facts` (`DESIGN.md` "Class existence at a few steps a node");
the class prover does not read yet the classes of λs holding a proposition. **A lemma is proved once a statement that stands cites it** (`DESIGN.md` "Lazy proving"): the link closes
before the registry proves, and the unit keeps only what a kept statement cites — 8,207 lemmas of the
ZF session left out, never proved; a request set aside comes back when a proof the registry makes cites it. **Emission
is built** (`DESIGN.md` "Emission"): `isa2fol lower data/zf_export --emit DIR` writes the unit as parts — a theory's
theorems, a lemma in its first citer's part — and `scripts/check-unit.sh DIR` kernel-checks each against the libraries
of base and of the parts it cites: all 7,969 claims and 568 schemas of the ZF session's unit Proved, 206.3 MB; a step
is cited only inside the block that wrote it, the checker keying a fact by its formula; a cut, `folCut`, is its proof's
step, the body citing it by name — `Frame.have`, Fol's `∃`-elim at `i` and Logic's cuts build it (`DESIGN.md` "A fact
derived once, cited by name"); a line already written in an open block is cited, never written again, a line opening or
closing a block never shared (`DESIGN.md` "A record's facts at fewer steps"). `DESIGN.md` is the plan; its "The steps after class
existence, in order" is the order of work, agreed again from step 2 on around FOUNDATION S4.

## Build

```bash
swift build
swift test
scripts/capped.sh swift test        # see rule 10
pre-commit run --all-files          # format and lint the tree
```

**Format and lint are the tools', never by hand**: SwiftFormat (`.swiftformat`) and SwiftLint (`.swiftlint.yml`),
the Airbnb Swift Style Guide's configurations, each override marked `isa2fol:`, pinned in `.pre-commit-config.yaml`.
Once per clone: `uv tool install pre-commit && pre-commit install`; every commit then formats and lints what it
stages. A rule that does not fit is changed in the configuration, never disabled inline.

Swift 6.4, language mode 5. `scripts/02-install-swift.sh` installs it into
`$HOME` with no sudo and is idempotent.

## Verification

**Iterate on the stage being built; run the whole unit only as CI** (`DESIGN.md` "Iteration"). A feature fails at the
earliest stage that sees it, so a run stops there (`--through expand|logic|registry`) and on the theorems it concerns
(`--theorem NAME,…`, `--skip SESSION,…`; the export's load, ~30 s, stays). The complete run, emitted and
kernel-checked, is the check of a feature believed complete. **Until the ZF session is fully translated, every run is
the ZF session alone** (user, 2026-10-17): `$ZF` below is `--skip ZF-AC,ZF-Coind,ZF-Constructible,ZF-IMP,ZF-Induct,
ZF-Resid,ZF-ex`. **Lint before every run** (user, 2026-10-17): `pre-commit run --all-files` first.

```bash
MEM=48G scripts/capped.sh .build/release/isa2fol lower data/zf_export --through logic $ZF [--theorem NAME,…]
MEM=32G scripts/capped.sh .build/release/isa2fol lower data/zf_export $ZF --emit DIR [--threads N]   # CI; N: every core
MEM=32G scripts/capped.sh scripts/check-unit.sh DIR        # each part, against base's and its parts' libraries
MEM=16G scripts/capped.sh scripts/check-base.sh [LIBDIR]   # base alone, each tier once
```

⚠ **THE COMPLETE RUN PEAKS AT 45.8 GB** (2026-10-19, `--threads 16`, 13:11): `MEM=32G` kills it. Run it with
`MEM=80G` until its memory is brought back under the CI's 32 GB.

The checker is at **`~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`**
and its source at `~/repos/fol-zfc-comb` (C++, Bazel). Tests find it via
`PROOF_CHECKER`, falling back to that path. It must have `--lib` (fol-zfc-comb 340e700,
branch `libraries-and-streaming`) and quoted name segments. ⚠ **BUILD IT ONLY WITH
`bazel build -c opt`**: a plain build repoints `bazel-bin` to the fastbuild outputs,
where no `proof_checker` is.

**A unit is valid only when the checker exits 0 AND stderr is empty.** The
checker reports three states and they are not interchangeable:

| | |
|---|---|
| `Proved` | the closure bottoms out in the admitted axioms |
| `Conditional (depends on: X)` | a valid derivation FROM `X`, which is not itself proved |
| `Unproved` | declared, marked `UNPROVED`, not proved |

⚠ **`Conditional` is never summed with `Proved`.** A corpus conditional on one
missing lemma would otherwise read as a triumph.

Schemas are reported in their own section (`Schemas proved (N):`), never in the
claims' `Proved (N):`.

## Mathematical foundation

**`docs/FOUNDATION.md` is the single authoritative document.** The 19-axiom NBG
base, rules R1-R6, the six specification obligations S1-S6, the class-existence
construction, and where the code disagrees.

It is the ONLY design document. `FOUNDATION_TO_FOLZFC.md`, `DECLARE.md`,
`REPLAY.md`, `KERNEL_ABI.md`, `fol_abi.h` and `DESIGN_rs.md` were **deleted
2026-09-23**: all six planned the Rust implementation — `IR1`-`IR4`, the
`H → S → E → LOWER` pipeline, `PassContext`, `src/replay/` — and none of it
survives the language change. They are in git history. Do not restore one to
answer a design question; `DESIGN.md` and the code are the structure.

Read it before proposing any schema, encoding, shortcut, or kernel-trust
optimisation. If a proposal contradicts it, the proposal is wrong — or the
document needs changing first, deliberately, not in passing.

**Method:** reason from what FOUNDATION.md requires. Corpus counts are tests,
never premises.

`docs/SOURCE_SURFACE.md` is the **measured** companion, and the distinction is
load-bearing: FOUNDATION.md says what the translation must satisfy, SOURCE_SURFACE
says what the corpus actually contains. A count never justifies a specification.
It is GENERATED by `isa2fol surface data/zf_export` — the reader's patterns, counted (`DESIGN.md` §4.3b 5); `docs/CLOSURE.md`, what every
proof rests on down to axioms, by `isa2fol closure data/zf_export` — so unlike every figure in
FOUNDATION.md its numbers have a live handle.

⚠ **FOUNDATION.md IS MATHEMATICS ONLY AND CARRIES NO CODE REFERENCE.** No module
path, no function name, no test name — they were stripped 2026-09-23 because each
one named something deleted while reading as live evidence. Do not add one back:
cite a `base/` tier or a probe, which the kernel checks, or state the claim
without a handle. Its source- and target-language vocabulary (`AppT`, `ZAppt`,
`UNPROVED`, theory names) is not a code reference.

⚠ **CONSEQUENTLY EVERY CORPUS FIGURE IN IT IS UNEVIDENCED** — the measuring code
is gone. §5 says so. Treat every number there as a belief, never a premise.

## Coding rules

### Design rules — MUST, before any change

D1. **Translate from the primitives.** `docs/SOURCE_SURFACE.md` lists every piece the corpus is built from; the
    translation owes ONE rule per piece, in the pass that owns that piece, and every composition then translates by
    itself. A rule is LOCAL to its piece: it never detects a surrounding shape, never keys on a constant's name (the
    primitives themselves excepted), never exists for one refusal. A piece that can only be handled by finding a
    shape around it has no translation yet — that is design work, raised, not coded around.

D2. **Components meet through contracts, and the contract comes first.** Each component and pass states what it
    PROVIDES and what it ASSUMES, written in `DESIGN.md` and agreed before its code; steps are built in the plan's
    order, so a feature never lands before the interfaces it consumes. A consumer assumes the contract and cites what
    it promises, even where the provider is incomplete today: the feature then fails on those cases AT THE PROVIDER,
    and fixing the provider fixes every consumer at once. NEVER patch a consumer to finish a feature: no consumer-side
    refusal of another component's gap, no special case working around it.

D3. **A meaning has one home**: the lowest component it belongs to, never the file that first needed it; a component
    exports exactly what others use; dependencies point only toward `IR`.

I1. **A concept that crosses a component is a typed value, built by its owner, never parsed back.**

I2. **A lemma is the contract: consumers cite it, the registry provides it.** A lemma's statement is built from the
    request alone, so citing never waits on the provider; a lemma the provider cannot prove is refused THERE, and
    every statement citing it falls with it.

I3. **Each pass states its input and output as `Pattern` sets, and dispatches by ONE exhaustive switch over
    `Pattern`**: a new pattern breaks the build until it has a rule, and every lemma generated is checked to contain
    only patterns the passes handle.

`DESIGN.md` holds the rest of the structure's rules: what the reader may reject (§2), a node's identity (§4.3),
determinism R1–R3 (§4.6).

### NO FALLBACKS. NO LEGACY. NO TRASH.

1. **No fallback code paths.** If a case can't be handled it MUST fail
   explicitly — `throw`, never a default that loses information. No
   "try A, fall back to B".

2. **No placeholder output.** A formula is either correctly translated or the
   translation fails. Emitting something that means "I couldn't do this" is not
   acceptable.

3. **No lossy encoding.** Every translation preserves the full mathematical
   content. Dropping information is never acceptable, even temporarily.

4. **Unified code paths.** One canonical way to handle each construct. No
   duplicate logic, no parallel paths doing similar things differently.

5. **No name sanitization — Isabelle's names reach the text unchanged.** The
   checker accepts qualified names (`ZF_Base.mem`, `QPair.QPair_iff`) in claim-name
   and predicate positions, never in a variable's (`DESIGN.md` §3). Do NOT
   introduce a mangling function: `ZF_Base.mem` → `ZF_Base_2emem` collides with a
   name that is literally `ZF_Base_2emem`, and silently. A fact index `name(4)` is
   spelled `name.4`.

6. **Test before implement.** Write the failing test that documents the
   expected behaviour, then implement to it.

7. **Understand before code.** Know WHY a bug happens and WHAT the correct
   output is. Discuss before writing.

8. **No code that "works for now."** If the design is wrong, fix the design.

9. **Comments are capped at 5% of `Sources/**/*.swift`.** A comment is a claim
   about the code that nothing checks, so it rots silently and then misleads.

   - **The default is NO comment.** A public item with a clear name and
     signature gets nothing.
   - **The only comment worth writing records a correction** — a mistake that is
     silent when repeated. Write it as a standing warning, naming what breaks.
   - No essays, no restated mathematics, no rationale narration, never an
     explanation of *what* the code does.
   - Rationale belongs in the **commit message**; mathematics in `docs/`.
   - If a change breaches the cap, **delete prose** — never raise the cap.

   ```bash
   python3 -c "
   import os
   t=c=0
   for r,_,fs in os.walk('Sources'):
     for f in fs:
       if f.endswith('.swift'):
         for l in open(os.path.join(r,f)):
           s=l.strip()
           if s: t+=1; c+= s.startswith('//')
   print(f'{c}/{t} = {100*c/t:.1f}%')"
   ```

   ✓ **CURRENTLY 263/16763 = 1.6%, under the cap.** Keep it there: a breach is
   fixed by deleting prose, never by raising the cap.

   Does not apply to `base/**/*.fol.def` headers: those record provenance of
   hand-copied proof text, which is not derivable from the artifact.

10. **NEVER run a build, test or checker uncapped** once the suite is large
    enough to matter. `scripts/capped.sh` runs a command in a memory-capped
    systemd user scope so the OOM killer acts inside that cgroup instead of
    taking down the session.

    ```bash
    MEM=16G scripts/capped.sh swift test
    ```

    - `MEM` is the backstop and is what actually protects the session.
    - The script REFUSES rather than running uncapped if `systemd-run` is
      missing. Do not add a fallback — rule 1 applies to tooling too.
    - `systemctl --user is-system-running` exits non-zero for `degraded`, which
      is a perfectly healthy instance. Test the state string, never the exit
      code.
    - The one OOM ever traced was exponential dependency nesting, **not**
      parallelism. Do not repeat the parallelism story as established.

### Swift rules

11. **No `default:` in a switch over an IR enum.** Exhaustiveness is the entire
    mechanism: adding a variant must break the build. One `default` and it
    silently stops doing that.

12. **IR enums stay `internal`, or `@frozen`.** Across a library-evolution
    boundary Swift permits `@unknown default`, which reopens what rule 11
    closes.

13. **Intern before you read: `t.type(of: try s.variable(k, &t))` reads a copy of `t` taken BEFORE the argument
    interns its node** — an index out of range the first time that node is new, and silent while it already exists.
    Bind the interned node first, then read.

## Architecture

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → a hash-consed Forest (equal subtrees, one Ref).  Knows no dialect.
  IR/            Node · Table · transform · index engine · passes · legalize
  FolDialect/    Declaration · render (formulas and proofs) · parse (base's schemas) — the text boundary over IR
  Reader/        the export → isa nodes: Export (loading) · IsaType · Constants · Terms (η-long, closed) · Statements · Proofs (decoder) · Reader (proofs) · Census
  Lowering/      the plan, never seen by the framework: the passes Expand · Logic · Fol, Reify a component in Logic's walk, and the registry — Expand's rules, Logic's for a proposition's letter, Pure's `⋀` over a proposition and functions of propositions (Truth, S4's truth set), `subst` and Pure's equality at `o` and at `i`, Reify's naming, `@def`s and instance at a compound term, a ZF definition cited (Unfolding, `c_UNFOLD`), Fol's at every object type, class existence (Comprehension, the class prover), a proof's values (Values) and the meeting lemmas (Meeting) built
  isa2fol/       CLI
Tests/           YXMLTests · FolDialectTests · IRTests · ReaderTests · LoweringTests
base/            the NBG foundation: axioms.fol.def + 13 tiers, kernel-checked
docs/            FOUNDATION.md · SOURCE_SURFACE.md · CLOSURE.md (both generated) · phase2_probes
data/zf_export/  the Isabelle export — a LOCAL CACHE, never committed: scripts/03-export-zf.sh
```

```
  YXML        IR        FolDialect
```

The reader (YXML → IR) reads statements and proofs (`Sources/Reader`); `Sources/Lowering` holds
the plan, Expand, Logic and Fol its passes with rules, Reify's code, which the logic pass calls, and the registry's provers,
Reify's (EX and UNIQ of a term, a constant's and a λ's facts), Tuple's and the class prover's (`CLASS ⟨λ⟩`, `c_CLASS`,
`c_LIFT`, `REKEY`, from Comprehension's classes of records); the emitter (`Sources/FolDialect/Emit.swift`) writes a unit
as parts; S4's truth set is Truth's (`Sources/Lowering/Truth.swift`); an instance at a class type is Lambda's
(`Sources/Lowering/Lambda.swift`), its lemma `LAMBDA_<fp>` and its prover; the rest of Logic's are unbuilt.

**There is ONE formula table per unit, holding isa and fol nodes together** —
interned, immutable, de Bruijn; proof steps live in scope regions and point into
it. That is `DESIGN.md` §4; the framework — formulas AND proof steps — is built in
`Sources/IR`, rendering and proof emission in `Sources/FolDialect`. No pass, no reader.
`Pattern.dialects` — one exhaustive switch — is the only place naming both vocabularies:
each kind is isa only, fol-zfc only, or both (a leaf FOL covers; a citation only of a theorem or a lemma at no
type arguments; a binder, its intro and its variable only at `o`, the schema's letter) — and `Node` declares its kinds in those groups, commented: the first two are exactly the reader's output. `Pattern` (`Sources/IR/Pattern.swift`)
is a node with each child replaced by its type and each constant or citation by its kind: what a pass
switches over (I3). `legalize` reads its `dialects`, and each pass states what it owns by an exhaustive switch
over it: what rule 11 rests on.

⚠ **THE TREE IR IS GONE.** `IsaDialect`'s `Sort`/`Term`/`Prop`/`Proof`/
`Statement<Stage>` were deleted 2026-09-23: the graph represents the same
constructs as ops, and keeping both was rule 4's duplication. A type variable is
`IRType.variable`, and a citation `use(cited, types, root)` carries its type arguments
(`DESIGN.md` §4.3a 3): the table holds each theorem as Isabelle states it. What becomes
of a generic theorem is `DESIGN.md` §4a decision 4: restricted to class `term`, it is read
at `i`; unrestricted, deferred.

### The dialects

**FolDialect** renders formulas and proofs from the table. A predicate's
arguments are *variables, and there is no other term*: the table refuses anything
else (`predicateArgumentNotVariable`), and a variable at `o` (`propositionAsTerm`). That is S1 as a check, and it is what makes
a description former unrepresentable. Whether a binder is a set or a class is its
IR TYPE, which Fol reads: every set binder guarded, **every class binder
unguarded** — guarding a class makes the claim false, not redundant.

### Translation

`docs/FOUNDATION.md` §2 is the specification (S1-S6). In short: the target
signature has **no function symbols**, so an Isabelle constant becomes a CLASS —
its graph on argument tuples — applied by membership, `⟨t, r⟩ ∈ F` (§1a). That its
class exists and is a function (`mfun`) is derived from its definition, never
admitted; congruence is membership's, proved once. `DESIGN.md` §4a is the pass plan.

`~/isabelle-pure-metalogic.md` and `~/isabelle-object-constants.md` are reading
notes on the source side: the 7 Pure rules, and the 197 term constants in
definitional order with their `.thy` files.

## Debugging

### Trace upstream before fixing downstream

If a value is wrong at point X, the bug is almost never at X. Trace backward to
where the bad state was introduced. The fix belongs at the source.

**Bad:** "key missing → add a default"
**Good:** "key missing → WHY? → the upstream phase skipped it because of Y → fix Y"

### Never add guards for "impossible" states without understanding why

A state that "shouldn't happen" IS the bug. Do not guard and move on.

### Question the design, not just the code

If a fix does not fit the architecture, state what the design assumes, identify
the violated assumption, and propose fixing the design.

### Reproduce first, then trace

Which file triggers it (theory + serial)? Expected output? Actual? At which
stage does the divergence start?

⚠ **Serials are not globally unique** — they are unique only within a theory.
Any index over the export must key on `(theory, serial)`.

⚠ **A SERIAL NAMES A THEOREM ONLY WITHIN ONE BUILD OF THE EXPORT.** It is a
per-process counter, and parallel proof checking hands it out in a different order
each run: two builds of the same sources differ in 1,021 of 3,955 named serials. A
test, fixture or document never names a serial — name the theorem, and resolve it
through `theory/thms` of the build at hand.

## Data

`data/zf_export/` — one directory per theory. **A local cache, git-ignored:**
`bash scripts/03-export-zf.sh` builds it from ONE Isabelle2025-2 run (64-bit Poly/ML,
the 32-bit default runs out of store on ZF.List). Never merge files from two builds:
a serial means something only within its own build, and a merged export once had a
named statement pointing at another theorem's proof and 402 dangling citations.

**Eight of the nine sessions of `src/ZF/ROOT`** — ZF, ZF-AC, ZF-Coind, ZF-Constructible,
ZF-IMP, ZF-Induct, ZF-Resid, ZF-ex. ⚠ **ZF-UNITY is missing:** Isabelle's exporter
rewrites one of its proofs (`Comp.Increasing_preserves_Stable`) past 64 GB, walking
proofs as trees; ZF-UNITY builds in 17 s with export off.

| | |
|---|---|
| `theory/thms` | theorem names and serials (YXML) |
| `theory/consts` | constant type information (YXML) |
| `theory/axioms` | axiom and definition statements, in every theory that has one — an XML TRIPLE, variables TYPED (`typed_vars = true`) |
| `theory/classes` | type classes — only `IFOL.term`, with no parameters and no axioms |
| `proofs/NNN` | one proof term per serial (YXML) |

`find data/zf_export -path '*/proofs/*' -type f | wc -l` → 38,923 proof terms, 4.2 GB,
of which ONE file, a box inside `List.nth_upt`'s proof, is 3.1 GB.
Entities carry a `file=` attribute naming their Isabelle source.
