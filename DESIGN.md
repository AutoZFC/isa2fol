# isa2fol — package layout and dialect types

**A SKETCH TO REACT TO.** Nothing built. Decisions I made rather than asked about
are marked **[choice]** — push back on any of them.

---

## 1. Package layout

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → node tree.   Knows no dialect.
  IR/            IRType · Op · Graph · Builder · Pass · legalize.   BUILT
  FolDialect/    types · verify · print
  Framework/     corpus · ledger · driver
  isa2fol/       CLI
Tests/
  YXMLTests/  IRTests/  FolDialectTests/
```

```
          YXML
            ▲
       IsaDialect          FolDialect
            ▲                  ▲
            └──── Framework ───┘        owns the CONVERT edge, and only that
                     ▲
                  isa2fol
```

**A dialect depends on neither the other dialect nor the Framework.** The only
place that knows both vocabularies is `Framework/Convert.swift`.

### Two rules that make the guarantee real

1. **No `default:` in a switch over an IR enum.** One `default` and adding a
   variant stops breaking the build — which is the entire mechanism.
2. **IR enums stay `internal` to their module** (or `@frozen`). Across a
   library-evolution boundary Swift permits `@unknown default`, reopening what
   rule 1 closes.

Worth writing down the way the comment cap is: they are cheap, and forgetting
either is silent.

---

## 2. Reading the export  **[NOT BUILT]**

The tree IR — `Sort`, `Term`, `Prop`, `Proof`, `Statement<Stage>` — was deleted
2026-09-23. §4's graph represents the same constructs as ops, and keeping both
was rule 4's duplication. What the reader must do survives; what it must produce
is now an `IR.Graph`, not a `Statement`.

**The surface it must cover is measured** — `docs/SOURCE_SURFACE.md`, which
regenerates: 3 Pure statement constants, 13 IFOL, **0 FOL**, 4 sorts, 249 ZF
constants; and on the proof side a frontier of 7 Pure axioms + 6 Pure derived +
132 IFOL/FOL + 7 ZF axioms + 207 object definitions.

### What the reader owes a NAMED refusal, never an absorbed case

These were `IsaDialect.Refusal`'s cases and they do not stop being obligations
because the enum is gone:

| refusal | why |
|---|---|
| a type variable | `IRType` has no case for `'a`. **Measured: 12 of 3,616 named ZF theorems (0.3%)**, half of them `split`/`qsplit`. IFOL/FOL/Pure are 37-48% polymorphic, and that layer is cited, never translated |
| a schematic `Var` (tag 2) | zero occurrences in 16,798 statements — a bet about the export's *preprocessing*, not about Isabelle. If one arrives, fail loudly |
| `Pure.conjunction` | **0 occurrences** in ZF statements, so refusing costs nothing |
| `Pure.term`, `Pure.sort_constraint` | Pure-internal, 0 in ZF statements |
| `Pure.prop` | 0 in ZF statements — erased, not refused |
| a de Bruijn index out of range | a bound variable is a block argument now, so this becomes "no producer" |
| a prop that is not a prop | structural |

⚠ **`groundnessIsStructural` WENT WITH THE MODULE, AND IT WAS THE ONLY TEST
PINNING THE POLYMORPHISM REFUSAL.** Re-pin it against the reader — a type
variable anywhere in a sort must refuse the whole statement, not just that slot.

## 3. FolDialect

### Terms — the defining constraint

```swift
public struct Term {           // A VARIABLE. There is no other term.
    public let name: String
}
```

Not an enum, and not an oversight: **S1 says the signature has no function
symbols**, so a description former, an application, a literal — none of them have
anywhere to live. This is the type that killed `iota`.

### Formulas

```swift
public enum Binder { case setVar, classVar }

public indirect enum Formula {
    case predicate(String, args: [Term], isSchema: Bool)
    case bottom
    case not(Formula)
    case binary(BinOp, Formula, Formula)              // & | -> <->
    case quantified(Quantifier, Binder, String, body: Formula)
}
```

**[choice] the binder carries its kind.** Measured: with no kind, `gate::guards`
reports a *correct* class quantifier as an R3 violation, and nothing can check the
other direction — a class that IS guarded, which makes the claim false rather than
redundant. One field makes the rule two-sided.

### Declarations

```swift
public enum Declaration {
    case axiom(String, Formula)                        // only base/ may emit one
    case claim(String, Formula)
    case schema(String, params: [(String, Int)], Formula)
}
```

### What the dialect owns

```swift
func verify(_ d: Declaration) throws
//  G4  no term former beyond a variable   — free from the Term type
//  G5  every setVar binder guarded AND every classVar binder unguarded
//  G1  an axiom's origin is base/

func render(_ d: Declaration) -> String      // .fol.def text
```

⚠ **`render` must round-trip.** The checker's bison grammar is the only authority
on the surface syntax, so the test is `parse(render(d)) == d` against text the
checker accepts — not against our own reading of the grammar.

---

## 4. IR — the pass engine  **[BUILT]**

**One graph, ops from both dialects, values typed by logical result.** Progressive
lowering in the MLIR sense: a partially-lowered graph is well-formed, so a pass may
lower one construct and stop.

### Nodes are values, edges are ops, the dialect labels the edge

Lowering **relabels edges; the nodes persist**. That is what makes it cheap, and it
works only because Isabelle's `i`/`o` and fol-zfc's object/proposition are the same
type — they differ by an *obligation* (the R3 guard), not by a sort. NBG is
one-sorted here and `set(·)` is a predicate, so one `.obj` is faithful; splitting it
would manufacture a sort the mathematics does not have.

```swift
enum IRType { case obj, prop, meta; indirect case fn(IRType, IRType) }
```

**Four cases, one per measured source sort** — `i`, `o`, Pure's `prop`, `fun`.
`.obj` and `.prop` are the fixpoint; `.meta` and `.fn` lower away. There is no
fifth: Isabelle has no sort for proofs, so a derivation's type is the
proposition it proves and its evidence-ness lives on the op. Measured surface, so
the lowering touches a minority of the graph: `i` 98.3%, `o` 12.4% arrive already
target-shaped; only `fn` 21.4% and the Pure constants move (`docs/SOURCE_SURFACE.md`).

⚠ **`fn` IS TWO DIFFERENT JOBS.** As a binder scope it becomes a **Region** and costs
nothing — that is most of the 21.4%. As a constant's *operand* it becomes a class
(S5), which is the expensive path.

### Binders are Regions, not de Bruijn

A bound variable is a block argument, so substitution is operand replacement and
there is no index shifting. Under free-form rewriting that is not a preference:
renumbering under a moved binder is the classic silent bug.

### Passes

```swift
protocol Pass { var name: String { get }; var ensures: [Invariant] { get }
                func run(_ b: inout Builder) throws }
protocol RewritePattern { func matches(_ op: Op) -> Bool
                          func rewrite(_ id: OpID, _ b: inout Builder) throws }
```

`PassManager` verifies `ensures` after **every** pass. Most passes are a bag of
patterns; adding a lowering is adding a pattern.

⚠ **THIS WEAKENS RULE 11 AND `legalize` IS THE REPLACEMENT.** A rewrite pattern is
partial, so a new `Op` case breaks no pattern and would survive lowering silently.
`legalize` is one exhaustive switch over `Op` and is the only place naming both
vocabularies — adding a case breaks the build **there**. That is the seal, relocated
from the module graph into a single function.

### The one thing the engine enforces, not the reviewer

**A value produced by an evidence op may be built, never rewritten.**
`Op.producesEvidence` is an exhaustive switch; `replaceAllUses` and `erase` look
up the producer and throw. A rewritten derivation carries no witness that it is still a
derivation, and re-establishing that in-process is a second checker, which the
kernel-as-sole-arbiter rule refuses. Object and proposition values stay freely
rewritable: a wrong one is a wrong *claim*, which is faithfulness, not soundness.

Pinned by `aDerivationCannotBeRewritten`, `aDerivationCannotBeErased`.

### Status

`legalize`'s `folZfcOnly` is the target. `Op` currently carries 12 ops — enough to
lower `⟹`/`Trueprop`/atoms/frees end to end (`loweringMakesItFolZfcOnly`) and no
more. Growing it is the work.

**Unmeasured:** `PatternPass` re-sweeps the whole graph after every single rewrite —
O(rounds × ops). Correct, and certainly too slow at ~798k proof-term nodes. Measure
before optimising; a use-list is the obvious fix.

## 5. Framework

```swift
public struct Corpus { … }                    // the export, indexed by (theory, serial)

public protocol Vocabulary {                  // what an Isabelle constant becomes
    func entry(_ isabelle: String) -> Entry?
}
public struct Entry { let predicate: String; let arity: Int; let source: Source }
public enum Source { case base, translated }  // FOUNDATION §3: Isabelle's Pair
                                              // is NOT the compiler's tuple

public enum Verdict {
    case declared
    case waiting(on: String)                  // a constant the Vocabulary lacks
    case refused(Refusal)
}
public struct Ledger { … }                    // verdicts, and blockers ranked by count

func convert(_ s: Isa.Statement<Ground>, _ v: Vocabulary) throws -> Fol.Declaration
```

`convert` is the **only** function that names both dialects.

---

## 6. What I did not decide

| | |
|---|---|
| what monomorphise instantiates at | use-site type argument, or always `'a := i`? The second is §11.0's proposal and resolves `eq`/`All`/`Ex`/`split` in one move, but makes a generic IFOL theorem mean only its `i`-instance |
| whether the ZF primitive surface is a third dialect or a stage inside IsaDialect | parked where you left it |
| what `base/` becomes | it is `.fol.def` text today; does FolDialect *read* it, or is it opaque input to the checker? |
