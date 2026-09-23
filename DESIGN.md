# isa2fol — package layout and dialect types

**A SKETCH TO REACT TO.** Nothing built. Decisions I made rather than asked about
are marked **[choice]** — push back on any of them.

⚠ The earlier "keep yxml.rs and export/db.rs" answer is **void** under the
language change: both have to be rewritten in Swift. Only the *format knowledge*
carries over, not the code.

---

## 1. Package layout

```
Package.swift
Sources/
  YXML/          Isabelle's transfer format → node tree.   Knows no dialect.
  IsaDialect/    types · verify · read-from-YXML
  FolDialect/    types · verify · print
  Framework/     corpus · conversion · ledger · driver
  isa2fol/       CLI
Tests/
  YXMLTests/  IsaDialectTests/  FolDialectTests/  FrameworkTests/
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

## 2. IsaDialect

### Sorts

```swift
public indirect enum Sort: Hashable {
    case i                       // ZF_Base.i  — terms
    case o                       // IFOL.o     — formulas
    case prop                    // Pure.prop
    case arrow(Sort, Sort)
    case variable(String)        // 'a — must not survive monomorphise
}
```

**[choice] Ground-ness is a phantom type, not a runtime check.**

```swift
public enum Poly {}            // may contain .variable
public enum Ground {}          // may not

public struct Statement<Stage> { let prop: Prop; let env: [String: Sort] }

public func monomorphise(_ s: Statement<Poly>) throws -> Statement<Ground>
```

The underlying enums are shared; only the wrapper is typed. So `convert` takes a
`Statement<Ground>` and **cannot be handed a polymorphic one** — the 463-refusal
problem is closed at the type level rather than by a verifier that runs.

### Terms

```swift
public indirect enum Term {
    case constant(String, types: [Sort])     // tag 0 — `types` is its instantiation
    case free(String, sort: Sort)            // tag 1
    case bound(Int)                          // tag 3 — de Bruijn
    case abs(String, sort: Sort, body: Term) // tag 4 — λ
    case app(Term, Term)                     // tag 5
}
```

**[choice] Five cases, not six — no schematic `Var` (tag 2).** Measured: **zero
occurrences** in 16,798 statements; the export writes schematics as `free`.
⚠ The risk is that this is a fact about the export's *preprocessing*, not about
Isabelle. If it ever appears, reading fails loudly at the dialect boundary, which
is the right place for it to fail.

`constant`'s `types` is what makes monomorphise possible: every use site already
carries its own instantiation.

### Propositions

```swift
public indirect enum Prop {
    case term(Term)                             // Trueprop t — the o⇒prop coercion
    case imp(Prop, Prop)                        // ⟹
    case all(String, sort: Sort, body: Prop)    // ⋀
    case eq(Term, Term, sort: Sort)             // ≡
    case ofClass(Sort, String)                  // OFCLASS
}
```

Read-time decisions, so they never reach a pass:
`Pure.prop` is the identity and is **erased**; `Pure.conjunction`,
`Pure.sort_constraint`, `Pure.term` **refuse by name**.

### Proofs — defined, not used in the first cut

```swift
public indirect enum Proof {
    case hypothesis(Int)                        // PBound
    case theorem(ThmID)                         // PThm
    case axiom(String)                          // PAxm
    case impIntro(Prop, Proof)                  // AbsP
    case impElim(Proof, Proof)                  // AppP
    case allIntro(String, sort: Sort, Proof)    // Abst
    case allElim(Proof, Term)                   // AppT
}
```

Named for what they *do*, not for the export's tags. Seven cases, and the export
contains no others.

### What the dialect owns

```swift
func read(_ node: YXML.Node) throws -> Statement<Poly>
func verify(_ s: Statement<Ground>) throws        // well-sorted; every Bound in range
```

---

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

## 4. Framework

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

## 5. What I did not decide

| | |
|---|---|
| what monomorphise instantiates at | use-site type argument, or always `'a := i`? The second is §11.0's proposal and resolves `eq`/`All`/`Ex`/`split` in one move, but makes a generic IFOL theorem mean only its `i`-instance |
| whether the ZF primitive surface is a third dialect or a stage inside IsaDialect | parked where you left it |
| what `base/` becomes | it is `.fol.def` text today; does FolDialect *read* it, or is it opaque input to the checker? |
| the fate of `rs/` | 12,781 lines, still on disk, suite green. Delete, or keep as reference while the Swift side grows? |
