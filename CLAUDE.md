# isa2fol: Isabelle/ZF to FOL-ZFC Translator

## Active development: Swift, at the repo root

The Rust tree (`rs/`, 12,781 lines) was **deleted 2026-09-22**. It is in git
history and nothing depends on it. `docs/`, `base/` and `scripts/capped.sh`
were hoisted out of it first and are live.

**Nothing is built yet.** `DESIGN.md` is the plan; `Sources/` is a skeleton of
dialect types plus the YXML reader.

## Build

```bash
swift build
swift test
scripts/capped.sh swift test        # see rule 10
```

Swift 6.4, language mode 5. `scripts/02-install-swift.sh` installs it into
`$HOME` with no sudo and is idempotent.

## Verification

```bash
PROOF_CHECKER_MAX_WARNINGS=100000 proof_checker unit.fol.def unit.fol.proof
```

The checker is at **`~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker`**
and its source at `~/repos/fol-zfc-comb` (C++, Bazel). Tests find it via
`PROOF_CHECKER`, falling back to that path.

**A unit is valid only when the checker exits 0 AND stderr is empty.** The
checker reports three states and they are not interchangeable:

| | |
|---|---|
| `Proved` | the closure bottoms out in the admitted axioms |
| `Conditional (depends on: X)` | a valid derivation FROM `X`, which is not itself proved |
| `Unproved` | declared, marked `UNPROVED`, not proved |

⚠ **`Conditional` is never summed with `Proved`.** A corpus conditional on one
missing lemma would otherwise read as a triumph.

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
It regenerates with `scripts/source-surface.py`, so unlike every figure in
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

   ✓ **CURRENTLY 4/1333 = 0.30%, under the cap.** Keep it there: a breach is
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

## Architecture

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → a hash-consed Forest (equal subtrees, one Ref).  Knows no dialect.
  IR/            Node · Table · transform · index engine · passes · legalize
  FolDialect/    Declaration · render (formulas and proofs) — the text boundary over IR
  Reader/        the export → isa nodes: IsaType · Constants · Terms (η-long) · (statements: unbuilt)
  isa2fol/       CLI
Tests/           YXMLTests · FolDialectTests · IRTests · ReaderTests
base/            the NBG foundation: axioms.fol.def + 9 tiers, kernel-checked
docs/            FOUNDATION.md · SOURCE_SURFACE.md · phase2_probes
data/zf_export/  the Isabelle export — a LOCAL CACHE, never committed: scripts/03-export-zf.sh
```

```
  YXML        IR        FolDialect
```

The reader (YXML → IR) is being built in `Sources/Reader` — types and constants
so far; the emitter (IR → FolDialect) is unbuilt.

**There is ONE formula table per unit, holding isa and fol nodes together** —
interned, immutable, de Bruijn; proof steps live in scope regions and point into
it. That is `DESIGN.md` §4; the framework — formulas AND proof steps — is built in
`Sources/IR`, rendering and proof emission in `Sources/FolDialect`. No pass, no reader.
`legalize` — one exhaustive switch over node kinds — stays the only place naming
both vocabularies; a rewrite is partial, so that switch is what rule 11 rests on.

⚠ **THE TREE IR IS GONE.** `IsaDialect`'s `Sort`/`Term`/`Prop`/`Proof`/
`Statement<Stage>` were deleted 2026-09-23: the graph represents the same
constructs as ops, and keeping both was rule 4's duplication. With them went
`Statement<Poly>`/`<Ground>`, so **nothing now closes polymorphism at the type
level** — `IRType` has no case for `'a` and the reader must refuse it by name.
Measured, that is cheap: **12 of 3,616 named ZF theorems** carry a type
variable (0.3%), half of them `split`/`qsplit`. The polymorphic layer is
IFOL/FOL/Pure at 37-48%, and that layer is cited, never translated.

### The dialects

**FolDialect** — `Term` is a struct with one field: *a variable, and there is no
other term.* That is S1 expressed as a type, and it is what makes a description
former unrepresentable. A `Binder` carries `.setVar` / `.classVar` so the guard
rule is two-sided: every set binder guarded, **every class binder unguarded** —
guarding a class makes the claim false, not redundant.

### Translation

`docs/FOUNDATION.md` §2 is the specification (S1-S6). In short: the target
signature has **no function symbols**, so a k-ary Isabelle term constant becomes
a relation on k+1 slots — its graph — with `C_EX`, `C_UNIQ`, `C_CONG` derived
from the `@def` body, never admitted.

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
`bash scripts/03-export-zf.sh` builds it from ONE Isabelle2025-2 run (~8 min;
64-bit Poly/ML, the 32-bit default runs out of store on ZF.List). Never merge
files from two builds: a serial means something only within its own build, and
a merged export once had a named statement pointing at another theorem's proof
and 402 dangling citations.

| | |
|---|---|
| `theory/thms` | theorem names and serials (YXML) |
| `theory/consts` | constant type information (YXML) |
| `theory/axioms` | axiom statements — only `Pure/` has one |
| `proofs/NNN` | one proof term per serial (YXML) |

`find data/zf_export -path '*/proofs/*' -type f | wc -l` → 15,946 proof terms
across the `ZF.*` theories plus `Pure`, `IFOL`, `FOL` — 3.2 GB, of which ONE file,
a box inside `List.nth_upt`'s proof, is 3.1 GB.
Entities carry a `file=` attribute naming their Isabelle source.
