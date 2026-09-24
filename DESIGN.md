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
  Lowering/      the statement passes.                              BUILT
  FolDialect/    types · print
  isa2fol/       CLI
Tests/
  YXMLTests/  IRTests/  LoweringTests/  FolDialectTests/
```

```
  YXML        IR ◀── Lowering        FolDialect
```

**Nothing connects them yet.** The reader (YXML → IR) and the emitter
(IR → FolDialect) are unbuilt, and where each lives is undecided.

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
one-sorted here and `set(·)` is a predicate, so one `.i` is faithful; splitting it
into set/class would manufacture a sort the mathematics does not have.

```swift
enum IRType { case i, o, prop; indirect case fn(IRType, IRType) }
```

**Four cases carrying the surface's own names** — `i`, `o`, Pure's `prop`, `fun`.
`.i` and `.o` are the fixpoint and live fully in fol-zfc; `.prop` and `.fn` are
the meta layer and are eliminated by passes. **How a proof is typed is
undecided** — there are no proof ops, and a proof typed `.prop` would be
indistinguishable from the proposition it proves.

⚠ **`.prop` IS PURE'S `prop`, NOT "a proposition".** A formula is `.o`. So
`legalize` refusing `.prop` reads as "no meta level survives", which is
right and looks wrong. An earlier naming had `.prop` mean `o` and `.meta` mean
Pure's `prop`; that collision is what this naming removes. Measured surface, so
the lowering touches a minority of the graph: `i` 98.3%, `o` 12.4% arrive already
target-shaped; only `fn` 21.4% and the Pure constants move (`docs/SOURCE_SURFACE.md`).

⚠ **`fn` IS TWO DIFFERENT JOBS.** As a binder scope it becomes a **Region** and costs
nothing — that is most of the 21.4%. As a constant's *operand* it becomes a class
(S5), which is the expensive path.

### Binders are Regions, not de Bruijn

A **region** is a scope: `{ args: [OpID], ops: [OpID] }`. A binding op carries
one, and the bound variable is an ordinary op inside it. `∀x. (set(x) → mem(x,y))`:

```
^0():
  %0:i = folVar("y")
  %5:o = folForall(setVar, ^1)
    ^1(%1:i):                        ← the region's argument IS the bound x
      %2:o = folPred("set", [%1])
      %3:o = folPred("mem", [%1, %0])   ← %0 closes over the enclosing scope
      %4:o = folImplies(%2, %3)
```

Isabelle uses `Bound n` instead — nameless, node-less. The cost of that under
free-form rewriting is renumbering: move a subterm under or out of a binder and
every index inside shifts, silently producing a well-formed term that means
something else. With a region the bound variable is just `%1` and substitution is
operand replacement.

⚠ **SCOPE IS REPRESENTED, NOT ENFORCED.** Nothing stops an op in `^0` from
referencing `%1`. The structure to verify dominance is present; no verifier is.
Pinned only as far as `aRegionHoldsABinderBody` goes.

### Passes

```swift
protocol Pass { var name: String { get }; func run(_ b: inout Builder) throws }
protocol RewritePattern { func matches(_ op: Op) -> Bool
                          func rewrite(_ id: OpID, _ b: inout Builder) throws }
```

Most passes are a bag of patterns; adding a lowering is adding a pattern.

**A fixpoint is a walk that changes nothing.** `PatternPass` walks every live op,
applies every match, and repeats until a walk fires no pattern. There is no round
cap: a pass whose walks do not approach the fixpoint is a bug in its patterns, and
a counter would only relabel that bug as a refusal. Pinned by
`aConvergentPassNeedsNoCap`.

⚠ **THIS WEAKENS RULE 11 AND `legalize` IS THE REPLACEMENT.** A rewrite pattern is
partial, so a new `Op` case breaks no pattern and would survive lowering silently.
`legalize` is one exhaustive switch over `Op` and is the only place naming both
vocabularies — adding a case breaks the build **there**. That is the seal, relocated
from the module graph into a single function.

### A rule for the proof layer, recorded rather than coded

**A fol derivation may be built, never rewritten.** A rewritten one carries no
witness that it is still a derivation, and re-establishing that in-process is a
second checker, which the kernel-as-sole-arbiter rule refuses.

⚠ **THIS IS NOT IN THE CODE AND SHOULD NOT BE UNTIL THERE IS A PROOF LAYER.** It
was, as `Op.producesEvidence`, and guarding a thing that did not exist yet got
the rule *wrong*: it froze `isaAxiom` too, which is source — input — so neither
`replaceAllUses` nor `erase` could remove it and `legalize` became unreachable
for any graph containing a proof. Write the guard when `folImpliesElim` and
friends exist and a pass actually threatens them.

Note also what the guard could never have covered: it protects an evidence op's
*result*, not its operands, so rewriting a formula a proof step cites still
changes what is proved. What covers that is ORDER — lower every formula, then
build the proof layer.

### Status

`legalize` is the target. `Op` carries 10 ops — enough to lower
`⟹`/`Trueprop`/atoms/frees end to end and no more.

⚠ **BENCHMARK WITH `-c release`.** `swift test` is debug, where ARC and the
`b.graph` getter copy dominate; any figure from it is meaningless.

⚠ **`replaceAllUses` WALKS EVERY OP — THERE IS NO USE-LIST** (`Builder.swift`).
So a pass costs O(rewrites × ops) however few walks it takes.

### The pattern, and why not classes

**An index-handle arena, and the op enum carries its own operands.**

```swift
case isaImp(OpID, OpID)             // arity is the CASE, not a runtime check
case isaAtom(String, [OpID])        // only genuinely variadic ops hold an array
case isaAll(IRType, RegionID)
```

There is no `OpNode`. An op *is* the enum; `Graph` keeps three parallel arrays —
`storage: [Op]`, `parents`, `dead` — plus the regions.

**One value per op, so `ValueID` and `OpID` are the same thing.** `Op.type`
computes what an op yields, so there is no value table and no `results` list
either. A block argument is an op (`.blockArg`), which keeps binders uniform.

**Adding an op costs five exhaustive switches** — `type`, `region`,
`forEachOperand`, `mapOperands` in `Op`, and `legalize`. That number is the extension cost and is worth
watching: it is what rule 11 charges for its guarantee.

Two things this shape buys that the previous one could not:

- **An arity error is unrepresentable.** `IRRefusal.arityMismatch` is deleted and
  the test that covered it could not be rewritten — `folImplies(OpID, OpID)`
  cannot be given one operand.
- **Pattern matching destructures the wiring.** `case let .isaImp(a, b)` replaces
  `node.operands[0]`, `node.operands[1]`, so a rewrite reads as the rule it is.

Class-based nodes would pay ARC on every traversal step, need `weak` to break
op→region→op cycles, and could be neither `Sendable` nor snapshotted. MLIR makes
the same choice with bump-arena pointers — morally identical, and for the same
reason: no per-node refcounting. The cost we accept is that a stale `OpID` indexes
garbage rather than failing, and that an ID means nothing without its `Graph`.

Consequences worth knowing:

- **A snapshot is three retains.** `let before = b.graph` is O(1); COW makes the
  divergence lazy. This is what makes a pass cheap to run speculatively.
- **`Builder` travels `inout`**, so the pass pipeline never copies it.
- **Deletion is a tombstone** (`erased`), so IDs stay stable and nothing is
  invalidated by an erase.
- **`Op` carries `String`s.** Interning names to an `Int` would shrink `Op` and make comparison O(1). Unmeasured.

## 4a. Statement lowering  **[BUILT]**

**The statement is TRANSLATED, not passed through.** A declaration is not an
interface the proof reads unchanged — lowering changes the proposition's shape,
and the proof must be built against the changed one.

```
⋀x. (mem(x,y) ⟹ mem(x,y))     →     ∀x. (set(x) → (mem(x,y) → mem(x,y)))
```

Three passes, and the order is forced:

| pass | does |
|---|---|
| `lower-pure` | erase Pure's `o ⇒ prop` coercion; `⟹` → `→` |
| `lower-ifol` | `isaFree` → `folVar`, `isaAtom` → `folPred` — a pure relabel, node types unchanged |
| `guard-binders` | **R3**: `⋀x:i. φ` → `∀x. (set(x) → φ)`; a non-`i` sort refuses |

`guard-binders` builds a `folImplies` over the region's result, so that result
must already be a formula — Pure's coercion has to go first.

### The guard is half of a contract

Inserting `set(x)` puts an obligation on the proof: every `forall_elim` at a term
`t` now owes a `set(t)` the Isabelle proof never supplied. So the symbol a proof
links against is a **signature**, not a name and not a formula — two theorems with
identical text but different guard placement are different symbols.

⚠ **LOWERING MUST THEREFORE BE A DETERMINISTIC FUNCTION OF THE STATEMENT ALONE.**
The emitted `.fol.def` records the guards but *not* where a materialised variable
came from, so PHASE 2 recovers that by **re-running this lowering** over the
`prop` its own proof file carries. Same input, same output, same `OpID`s — no
global counters, no dependence on dictionary order. Pinned by
`loweringIsDeterministic`, which compares whole graphs.

## 5. What I did not decide

| | |
|---|---|
| what monomorphise instantiates at | use-site type argument, or always `'a := i`? The second is §11.0's proposal and resolves `eq`/`All`/`Ex`/`split` in one move, but makes a generic IFOL theorem mean only its `i`-instance |
| whether the ZF primitive surface is a third dialect or a stage inside IsaDialect | parked where you left it |
| what `base/` becomes | it is `.fol.def` text today; does FolDialect *read* it, or is it opaque input to the checker? |
