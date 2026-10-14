# SOURCE SURFACE — the patterns the translation owes a rule each

**Generated — do not edit.** `isa2fol surface data/zf_export`. A census, not mathematics: `docs/FOUNDATION.md` says what the
translation must satisfy; this lists what the corpus is built from, as the reader emits it — each pattern a
primitive at its type (`DESIGN.md` §4.3b). With one rule per pattern, every theorem built from them translates.

- **The population** is the closure of the named ZF theorems: every theorem they cite, each read from its own
  proof, and the definition of every constant that occurs, transitively. An unnamed box is part of its citer's
  proof.
- **A count** is the named ZF theorems whose closure holds the pattern: the theorems that do not translate until
  it has a rule. A count orders the work; it never justifies a rule.

## Population

| session | named theorems |
|---|---:|
| ZF | 3616 |
| ZF-AC | 477 |
| ZF-Coind | 288 |
| ZF-Constructible | 2121 |
| ZF-IMP | 284 |
| ZF-Induct | 1496 |
| ZF-Resid | 340 |
| ZF-UNITY | **not in the export** |
| ZF-ex | 798 |
| **all** | **9420** |

The reader refuses none of them, nor any theorem they cite.

## Patterns (2592)

| pattern | theorems | % |
|---|---:|---:|
| `folAnd(o, o)` | 9330 | 99.0% |
| `folBottom` | 8576 | 91.0% |
| `folIff(o, o)` | 8904 | 94.5% |
| `folImplies(o, o)` | 9416 | 100.0% |
| `folImpliesElim(o, o)` | 8833 | 93.8% |
| `folImpliesIntro(o, body: o)` | 8839 | 93.8% |
| `folOr(o, o)` | 9211 | 97.8% |
| `hyp(o)` | 8824 | 93.7% |
| `ifolAll('a, body: o)` | 9179 | 97.4% |
| `ifolAll('b, body: o)` | 4636 | 49.2% |
| `ifolAll(('a => 'b), body: o)` | 4626 | 49.1% |
| `ifolAll(('a => ('a => o)), body: o)` | 7578 | 80.4% |
| `ifolAll(('a => ('b => o)), body: o)` | 1195 | 12.7% |
| `ifolAll(('a => o), body: o)` | 7950 | 84.4% |
| `ifolAll(('b => 'a), body: o)` | 439 | 4.7% |
| `ifolAll(('b => ('b => o)), body: o)` | 4626 | 49.1% |
| `ifolAll(('b => (('b => 'a) => 'a)), body: o)` | 439 | 4.7% |
| `ifolAll(('b => o), body: o)` | 4634 | 49.2% |
| `ifolAll((('a => o) => o), body: o)` | 7324 | 77.7% |
| `ifolAll((('b => 'a) => 'a), body: o)` | 439 | 4.7% |
| `ifolAll((('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)), body: o)` | 439 | 4.7% |
| `ifolAll((('b => (('b => 'a) => 'a)) => o), body: o)` | 439 | 4.7% |
| `ifolAll(((('a => o) => o) => ((('a => o) => o) => o)), body: o)` | 7323 | 77.7% |
| `ifolAll(((('a => o) => o) => o), body: o)` | 7323 | 77.7% |
| `ifolAll((((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)), body: o)` | 2773 | 29.4% |
| `ifolAll((((i => (i => 'a)) => (i => 'a)) => o), body: o)` | 2773 | 29.4% |
| `ifolAll((((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)), body: o)` | 4 | 0.0% |
| `ifolAll((((i => (i => (i => i))) => (i => i)) => o), body: o)` | 4 | 0.0% |
| `ifolAll((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)), body: o)` | 38 | 0.4% |
| `ifolAll((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o), body: o)` | 38 | 0.4% |
| `ifolAll((((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)), body: o)` | 2760 | 29.3% |
| `ifolAll((((i => (i => i)) => (i => i)) => o), body: o)` | 2760 | 29.3% |
| `ifolAll((((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)), body: o)` | 2421 | 25.7% |
| `ifolAll((((i => i) => ((i => i) => (i => i))) => o), body: o)` | 2421 | 25.7% |
| `ifolAll((((i => i) => (i => i)) => (((i => i) => (i => i)) => o)), body: o)` | 514 | 5.5% |
| `ifolAll((((i => i) => (i => i)) => o), body: o)` | 514 | 5.5% |
| `ifolAll((((i => i) => o) => (((i => i) => o) => o)), body: o)` | 531 | 5.6% |
| `ifolAll((((i => i) => o) => o), body: o)` | 531 | 5.6% |
| `ifolAll((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)), body: o)` | 70 | 0.7% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o), body: o)` | 70 | 0.7% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)), body: o)` | 183 | 1.9% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o), body: o)` | 183 | 1.9% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)), body: o)` | 318 | 3.4% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o), body: o)` | 318 | 3.4% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)), body: o)` | 53 | 0.6% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o), body: o)` | 53 | 0.6% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)), body: o)` | 155 | 1.6% |
| `ifolAll((((i => o) => ((i => (i => (i => o))) => (i => o))) => o), body: o)` | 155 | 1.6% |
| `ifolAll((((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)), body: o)` | 128 | 1.4% |
| `ifolAll((((i => o) => ((i => (i => o)) => ((i => i) => o))) => o), body: o)` | 128 | 1.4% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)), body: o)` | 243 | 2.6% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o), body: o)` | 243 | 2.6% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)), body: o)` | 225 | 2.4% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o), body: o)` | 225 | 2.4% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)), body: o)` | 141 | 1.5% |
| `ifolAll((((i => o) => ((i => (i => o)) => (i => o))) => o), body: o)` | 141 | 1.5% |
| `ifolAll((((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)), body: o)` | 585 | 6.2% |
| `ifolAll((((i => o) => ((i => (i => o)) => o)) => o), body: o)` | 585 | 6.2% |
| `ifolAll((((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)), body: o)` | 1163 | 12.3% |
| `ifolAll((((i => o) => ((i => o) => o)) => o), body: o)` | 1163 | 12.3% |
| `ifolAll((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)), body: o)` | 3 | 0.0% |
| `ifolAll((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o), body: o)` | 3 | 0.0% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)), body: o)` | 44 | 0.5% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o), body: o)` | 44 | 0.5% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)), body: o)` | 249 | 2.6% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o), body: o)` | 249 | 2.6% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)), body: o)` | 96 | 1.0% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => (i => o)))) => o), body: o)` | 96 | 1.0% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)), body: o)` | 374 | 4.0% |
| `ifolAll((((i => o) => (i => ((i => (i => o)) => o))) => o), body: o)` | 374 | 4.0% |
| `ifolAll((((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)), body: o)` | 46 | 0.5% |
| `ifolAll((((i => o) => (i => ((i => o) => (i => o)))) => o), body: o)` | 46 | 0.5% |
| `ifolAll((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)), body: o)` | 41 | 0.4% |
| `ifolAll((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o), body: o)` | 41 | 0.4% |
| `ifolAll((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o), body: o)` | 1 | 0.0% |
| `ifolAll((((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)), body: o)` | 89 | 0.9% |
| `ifolAll((((i => o) => (i => (i => (i => (i => (i => o)))))) => o), body: o)` | 89 | 0.9% |
| `ifolAll((((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)), body: o)` | 117 | 1.2% |
| `ifolAll((((i => o) => (i => (i => (i => (i => o))))) => o), body: o)` | 117 | 1.2% |
| `ifolAll((((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)), body: o)` | 1025 | 10.9% |
| `ifolAll((((i => o) => (i => (i => (i => o)))) => o), body: o)` | 1025 | 10.9% |
| `ifolAll((((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)), body: o)` | 44 | 0.5% |
| `ifolAll((((i => o) => (i => (i => i))) => o), body: o)` | 44 | 0.5% |
| `ifolAll((((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)), body: o)` | 945 | 10.0% |
| `ifolAll((((i => o) => (i => (i => o))) => o), body: o)` | 945 | 10.0% |
| `ifolAll((((i => o) => (i => i)) => (((i => o) => (i => i)) => o)), body: o)` | 2 | 0.0% |
| `ifolAll((((i => o) => (i => i)) => o), body: o)` | 2 | 0.0% |
| `ifolAll((((i => o) => (i => o)) => (((i => o) => (i => o)) => o)), body: o)` | 670 | 7.1% |
| `ifolAll((((i => o) => (i => o)) => o), body: o)` | 670 | 7.1% |
| `ifolAll((((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)), body: o)` | 92 | 1.0% |
| `ifolAll((((i => o) => (o => (i => o))) => o), body: o)` | 92 | 1.0% |
| `ifolAll((((i => o) => i) => (((i => o) => i) => o)), body: o)` | 5274 | 56.0% |
| `ifolAll((((i => o) => i) => o), body: o)` | 5274 | 56.0% |
| `ifolAll((((i => o) => o) => (((i => o) => o) => o)), body: o)` | 4100 | 43.5% |
| `ifolAll((((i => o) => o) => o), body: o)` | 4102 | 43.5% |
| `ifolAll(((i => 'a) => ((i => 'a) => o)), body: o)` | 2739 | 29.1% |
| `ifolAll(((i => 'a) => o), body: o)` | 2739 | 29.1% |
| `ifolAll(((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)), body: o)` | 25 | 0.3% |
| `ifolAll(((i => ((i => (i => (i => i))) => i)) => o), body: o)` | 25 | 0.3% |
| `ifolAll(((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)), body: o)` | 53 | 0.6% |
| `ifolAll(((i => ((i => (i => i)) => (i => (i => i)))) => o), body: o)` | 53 | 0.6% |
| `ifolAll(((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)), body: o)` | 2044 | 21.7% |
| `ifolAll(((i => ((i => (i => i)) => (i => i))) => o), body: o)` | 2044 | 21.7% |
| `ifolAll(((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)), body: o)` | 3706 | 39.3% |
| `ifolAll(((i => ((i => (i => i)) => i)) => o), body: o)` | 3706 | 39.3% |
| `ifolAll(((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)), body: o)` | 7313 | 77.6% |
| `ifolAll(((i => ((i => (i => o)) => i)) => o), body: o)` | 7313 | 77.6% |
| `ifolAll(((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)), body: o)` | 3854 | 40.9% |
| `ifolAll(((i => ((i => i) => (i => i))) => o), body: o)` | 3854 | 40.9% |
| `ifolAll(((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)), body: o)` | 6215 | 66.0% |
| `ifolAll(((i => ((i => i) => i)) => o), body: o)` | 6215 | 66.0% |
| `ifolAll(((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)), body: o)` | 4841 | 51.4% |
| `ifolAll(((i => ((i => i) => o)) => o), body: o)` | 4841 | 51.4% |
| `ifolAll(((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)), body: o)` | 7247 | 76.9% |
| `ifolAll(((i => ((i => o) => i)) => o), body: o)` | 7247 | 76.9% |
| `ifolAll(((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)), body: o)` | 7493 | 79.5% |
| `ifolAll(((i => ((i => o) => o)) => o), body: o)` | 7493 | 79.5% |
| `ifolAll(((i => (i => 'a)) => (i => 'a)), body: o)` | 2773 | 29.4% |
| `ifolAll(((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)), body: o)` | 8 | 0.1% |
| `ifolAll(((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o), body: o)` | 8 | 0.1% |
| `ifolAll(((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)), body: o)` | 4068 | 43.2% |
| `ifolAll(((i => (i => ((i => (i => i)) => (i => o)))) => o), body: o)` | 4068 | 43.2% |
| `ifolAll(((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)), body: o)` | 4061 | 43.1% |
| `ifolAll(((i => (i => ((i => (i => i)) => i))) => o), body: o)` | 4061 | 43.1% |
| `ifolAll(((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)), body: o)` | 439 | 4.7% |
| `ifolAll(((i => (i => ((i => (i => i)) => o))) => o), body: o)` | 439 | 4.7% |
| `ifolAll(((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)), body: o)` | 7 | 0.1% |
| `ifolAll(((i => (i => ((i => i) => ((i => i) => (i => o))))) => o), body: o)` | 7 | 0.1% |
| `ifolAll(((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)), body: o)` | 896 | 9.5% |
| `ifolAll(((i => (i => (i => ((i => (i => i)) => i)))) => o), body: o)` | 896 | 9.5% |
| `ifolAll(((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)), body: o)` | 21 | 0.2% |
| `ifolAll(((i => (i => (i => ((i => i) => o)))) => o), body: o)` | 21 | 0.2% |
| `ifolAll(((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)), body: o)` | 35 | 0.4% |
| `ifolAll(((i => (i => (i => (i => (i => (i => i)))))) => o), body: o)` | 35 | 0.4% |
| `ifolAll(((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)), body: o)` | 187 | 2.0% |
| `ifolAll(((i => (i => (i => (i => (i => i))))) => o), body: o)` | 187 | 2.0% |
| `ifolAll(((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)), body: o)` | 9 | 0.1% |
| `ifolAll(((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)), body: o)` | 1 | 0.0% |
| `ifolAll(((i => (i => (i => (i => (i => o))))) => o), body: o)` | 9 | 0.1% |
| `ifolAll(((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)), body: o)` | 1108 | 11.8% |
| `ifolAll(((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))), body: o)` | 38 | 0.4% |
| `ifolAll(((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))), body: o)` | 24 | 0.3% |
| `ifolAll(((i => (i => (i => (i => i)))) => o), body: o)` | 1109 | 11.8% |
| `ifolAll(((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)), body: o)` | 114 | 1.2% |
| `ifolAll(((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)), body: o)` | 2 | 0.0% |
| `ifolAll(((i => (i => (i => (i => o)))) => o), body: o)` | 114 | 1.2% |
| `ifolAll(((i => (i => (i => i))) => ((i => (i => (i => i))) => o)), body: o)` | 3075 | 32.6% |
| `ifolAll(((i => (i => (i => i))) => ((i => (i => i)) => (i => i))), body: o)` | 10 | 0.1% |
| `ifolAll(((i => (i => (i => i))) => (i => (i => i))), body: o)` | 103 | 1.1% |
| `ifolAll(((i => (i => (i => i))) => (i => i)), body: o)` | 1096 | 11.6% |
| `ifolAll(((i => (i => (i => i))) => i), body: o)` | 25 | 0.3% |
| `ifolAll(((i => (i => (i => i))) => o), body: o)` | 3077 | 32.7% |
| `ifolAll(((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))), body: o)` | 70 | 0.7% |
| `ifolAll(((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))), body: o)` | 70 | 0.7% |
| `ifolAll(((i => (i => (i => o))) => ((i => (i => (i => o))) => o)), body: o)` | 284 | 3.0% |
| `ifolAll(((i => (i => (i => o))) => ((i => (i => i)) => o)), body: o)` | 185 | 2.0% |
| `ifolAll(((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))), body: o)` | 70 | 0.7% |
| `ifolAll(((i => (i => (i => o))) => (i => (i => (i => o)))), body: o)` | 318 | 3.4% |
| `ifolAll(((i => (i => (i => o))) => (i => (i => o))), body: o)` | 149 | 1.6% |
| `ifolAll(((i => (i => (i => o))) => (i => o)), body: o)` | 156 | 1.7% |
| `ifolAll(((i => (i => (i => o))) => o), body: o)` | 284 | 3.0% |
| `ifolAll(((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))), body: o)` | 38 | 0.4% |
| `ifolAll(((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))), body: o)` | 24 | 0.3% |
| `ifolAll(((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))), body: o)` | 10 | 0.1% |
| `ifolAll(((i => (i => i)) => ((i => (i => (i => i))) => (i => i))), body: o)` | 37 | 0.4% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), body: o)` | 38 | 0.4% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))), body: o)` | 24 | 0.3% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))), body: o)` | 21 | 0.2% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => (i => i))), body: o)` | 23 | 0.2% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => i)), body: o)` | 8 | 0.1% |
| `ifolAll(((i => (i => i)) => ((i => (i => i)) => o)), body: o)` | 6923 | 73.5% |
| `ifolAll(((i => (i => i)) => ((i => i) => (i => i))), body: o)` | 965 | 10.2% |
| `ifolAll(((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))), body: o)` | 35 | 0.4% |
| `ifolAll(((i => (i => i)) => (i => (i => i))), body: o)` | 91 | 1.0% |
| `ifolAll(((i => (i => i)) => (i => i)), body: o)` | 2884 | 30.6% |
| `ifolAll(((i => (i => i)) => (i => o)), body: o)` | 4068 | 43.2% |
| `ifolAll(((i => (i => i)) => i), body: o)` | 4065 | 43.2% |
| `ifolAll(((i => (i => i)) => o), body: o)` | 6927 | 73.5% |
| `ifolAll(((i => (i => o)) => ((i => (i => o)) => o)), body: o)` | 7387 | 78.4% |
| `ifolAll(((i => (i => o)) => ((i => i) => o)), body: o)` | 132 | 1.4% |
| `ifolAll(((i => (i => o)) => (i => (i => (i => (i => o))))), body: o)` | 243 | 2.6% |
| `ifolAll(((i => (i => o)) => (i => (i => (i => o)))), body: o)` | 225 | 2.4% |
| `ifolAll(((i => (i => o)) => (i => (i => o))), body: o)` | 250 | 2.7% |
| `ifolAll(((i => (i => o)) => (i => o)), body: o)` | 344 | 3.7% |
| `ifolAll(((i => (i => o)) => i), body: o)` | 7313 | 77.6% |
| `ifolAll(((i => (i => o)) => o), body: o)` | 7404 | 78.6% |
| `ifolAll(((i => i) => ((i => (i => (i => i))) => (i => i))), body: o)` | 92 | 1.0% |
| `ifolAll(((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))), body: o)` | 23 | 0.2% |
| `ifolAll(((i => i) => ((i => i) => (i => i))), body: o)` | 2421 | 25.7% |
| `ifolAll(((i => i) => ((i => i) => (i => o))), body: o)` | 7 | 0.1% |
| `ifolAll(((i => i) => ((i => i) => o)), body: o)` | 6847 | 72.7% |
| `ifolAll(((i => i) => (i => (i => i))), body: o)` | 442 | 4.7% |
| `ifolAll(((i => i) => (i => i)), body: o)` | 4223 | 44.8% |
| `ifolAll(((i => i) => (i => o)), body: o)` | 7 | 0.1% |
| `ifolAll(((i => i) => i), body: o)` | 6229 | 66.1% |
| `ifolAll(((i => i) => o), body: o)` | 6955 | 73.8% |
| `ifolAll(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), body: o)` | 1 | 0.0% |
| `ifolAll(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), body: o)` | 1 | 0.0% |
| `ifolAll(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), body: o)` | 70 | 0.7% |
| `ifolAll(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), body: o)` | 183 | 1.9% |
| `ifolAll(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), body: o)` | 318 | 3.4% |
| `ifolAll(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), body: o)` | 53 | 0.6% |
| `ifolAll(((i => o) => ((i => (i => (i => o))) => (i => o))), body: o)` | 155 | 1.6% |
| `ifolAll(((i => o) => ((i => (i => o)) => ((i => i) => o))), body: o)` | 128 | 1.4% |
| `ifolAll(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), body: o)` | 243 | 2.6% |
| `ifolAll(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), body: o)` | 225 | 2.4% |
| `ifolAll(((i => o) => ((i => (i => o)) => (i => o))), body: o)` | 141 | 1.5% |
| `ifolAll(((i => o) => ((i => (i => o)) => o)), body: o)` | 597 | 6.3% |
| `ifolAll(((i => o) => ((i => o) => ((i => (i => o)) => o))), body: o)` | 429 | 4.6% |
| `ifolAll(((i => o) => ((i => o) => o)), body: o)` | 5453 | 57.9% |
| `ifolAll(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), body: o)` | 3 | 0.0% |
| `ifolAll(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), body: o)` | 44 | 0.5% |
| `ifolAll(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), body: o)` | 249 | 2.6% |
| `ifolAll(((i => o) => (i => ((i => (i => o)) => (i => o)))), body: o)` | 96 | 1.0% |
| `ifolAll(((i => o) => (i => ((i => (i => o)) => o))), body: o)` | 374 | 4.0% |
| `ifolAll(((i => o) => (i => ((i => o) => (i => o)))), body: o)` | 46 | 0.5% |
| `ifolAll(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), body: o)` | 41 | 0.4% |
| `ifolAll(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), body: o)` | 1 | 0.0% |
| `ifolAll(((i => o) => (i => (i => (i => (i => (i => o)))))), body: o)` | 89 | 0.9% |
| `ifolAll(((i => o) => (i => (i => (i => (i => o))))), body: o)` | 225 | 2.4% |
| `ifolAll(((i => o) => (i => (i => (i => o)))), body: o)` | 1026 | 10.9% |
| `ifolAll(((i => o) => (i => (i => i))), body: o)` | 44 | 0.5% |
| `ifolAll(((i => o) => (i => (i => o))), body: o)` | 946 | 10.0% |
| `ifolAll(((i => o) => (i => i)), body: o)` | 445 | 4.7% |
| `ifolAll(((i => o) => (i => o)), body: o)` | 838 | 8.9% |
| `ifolAll(((i => o) => (o => (i => o))), body: o)` | 92 | 1.0% |
| `ifolAll(((i => o) => i), body: o)` | 7257 | 77.0% |
| `ifolAll(((i => o) => o), body: o)` | 7746 | 82.2% |
| `ifolAll(((o => (i => (i => i))) => ((o => (i => (i => i))) => o)), body: o)` | 5018 | 53.3% |
| `ifolAll(((o => (i => (i => i))) => o), body: o)` | 5018 | 53.3% |
| `ifolAll(((o => (o => o)) => ((o => (o => o)) => o)), body: o)` | 7841 | 83.2% |
| `ifolAll(((o => (o => o)) => o), body: o)` | 7841 | 83.2% |
| `ifolAll(((o => i) => ((o => i) => o)), body: o)` | 882 | 9.4% |
| `ifolAll(((o => i) => o), body: o)` | 882 | 9.4% |
| `ifolAll(((o => o) => ((o => o) => o)), body: o)` | 7819 | 83.0% |
| `ifolAll(((o => o) => o), body: o)` | 7819 | 83.0% |
| `ifolAll((i => 'a), body: o)` | 2773 | 29.4% |
| `ifolAll((i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), body: o)` | 1 | 0.0% |
| `ifolAll((i => ((i => (i => (i => i))) => i)), body: o)` | 25 | 0.3% |
| `ifolAll((i => ((i => (i => (i => o))) => ((i => (i => i)) => o))), body: o)` | 41 | 0.4% |
| `ifolAll((i => ((i => (i => (i => o))) => (i => (i => o)))), body: o)` | 3 | 0.0% |
| `ifolAll((i => ((i => (i => i)) => ((i => (i => i)) => i))), body: o)` | 8 | 0.1% |
| `ifolAll((i => ((i => (i => i)) => (i => (i => i)))), body: o)` | 53 | 0.6% |
| `ifolAll((i => ((i => (i => i)) => (i => i))), body: o)` | 2100 | 22.3% |
| `ifolAll((i => ((i => (i => i)) => (i => o))), body: o)` | 4068 | 43.2% |
| `ifolAll((i => ((i => (i => i)) => i)), body: o)` | 4064 | 43.1% |
| `ifolAll((i => ((i => (i => i)) => o)), body: o)` | 439 | 4.7% |
| `ifolAll((i => ((i => (i => o)) => ((i => i) => o))), body: o)` | 44 | 0.5% |
| `ifolAll((i => ((i => (i => o)) => (i => (i => o)))), body: o)` | 249 | 2.6% |
| `ifolAll((i => ((i => (i => o)) => (i => o))), body: o)` | 96 | 1.0% |
| `ifolAll((i => ((i => (i => o)) => i)), body: o)` | 7313 | 77.6% |
| `ifolAll((i => ((i => (i => o)) => o)), body: o)` | 374 | 4.0% |
| `ifolAll((i => ((i => i) => ((i => i) => (i => o)))), body: o)` | 7 | 0.1% |
| `ifolAll((i => ((i => i) => (i => i))), body: o)` | 3854 | 40.9% |
| `ifolAll((i => ((i => i) => i)), body: o)` | 6226 | 66.1% |
| `ifolAll((i => ((i => i) => o)), body: o)` | 4845 | 51.4% |
| `ifolAll((i => ((i => o) => (i => o))), body: o)` | 46 | 0.5% |
| `ifolAll((i => ((i => o) => i)), body: o)` | 7247 | 76.9% |
| `ifolAll((i => ((i => o) => o)), body: o)` | 7494 | 79.6% |
| `ifolAll((i => (i => 'a)), body: o)` | 2773 | 29.4% |
| `ifolAll((i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))), body: o)` | 1 | 0.0% |
| `ifolAll((i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))), body: o)` | 41 | 0.4% |
| `ifolAll((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), body: o)` | 8 | 0.1% |
| `ifolAll((i => (i => ((i => (i => i)) => (i => i)))), body: o)` | 13 | 0.1% |
| `ifolAll((i => (i => ((i => (i => i)) => (i => o)))), body: o)` | 4068 | 43.2% |
| `ifolAll((i => (i => ((i => (i => i)) => i))), body: o)` | 4062 | 43.1% |
| `ifolAll((i => (i => ((i => (i => i)) => o))), body: o)` | 439 | 4.7% |
| `ifolAll((i => (i => ((i => i) => ((i => i) => (i => o))))), body: o)` | 7 | 0.1% |
| `ifolAll((i => (i => ((i => i) => o))), body: o)` | 21 | 0.2% |
| `ifolAll((i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))), body: o)` | 1 | 0.0% |
| `ifolAll((i => (i => (i => ((i => (i => i)) => i)))), body: o)` | 896 | 9.5% |
| `ifolAll((i => (i => (i => ((i => i) => o)))), body: o)` | 21 | 0.2% |
| `ifolAll((i => (i => (i => (i => (i => (i => i)))))), body: o)` | 35 | 0.4% |
| `ifolAll((i => (i => (i => (i => (i => i))))), body: o)` | 471 | 5.0% |
| `ifolAll((i => (i => (i => (i => (i => o))))), body: o)` | 99 | 1.1% |
| `ifolAll((i => (i => (i => (i => i)))), body: o)` | 1859 | 19.7% |
| `ifolAll((i => (i => (i => (i => o)))), body: o)` | 435 | 4.6% |
| `ifolAll((i => (i => (i => i))), body: o)` | 3581 | 38.0% |
| `ifolAll((i => (i => (i => o))), body: o)` | 1482 | 15.7% |
| `ifolAll((i => (i => i)), body: o)` | 7298 | 77.5% |
| `ifolAll((i => (i => o)), body: o)` | 8027 | 85.2% |
| `ifolAll((i => i), body: o)` | 7771 | 82.5% |
| `ifolAll((i => o), body: o)` | 8423 | 89.4% |
| `ifolAll((o => (i => (i => i))), body: o)` | 5020 | 53.3% |
| `ifolAll((o => (i => o)), body: o)` | 92 | 1.0% |
| `ifolAll((o => (o => o)), body: o)` | 8323 | 88.4% |
| `ifolAll((o => i), body: o)` | 883 | 9.4% |
| `ifolAll((o => o), body: o)` | 8432 | 89.5% |
| `ifolAll(dummy, body: o)` | 28 | 0.3% |
| `ifolAll(i, body: o)` | 9169 | 97.3% |
| `ifolAll(o, body: o)` | 8838 | 93.8% |
| `ifolEx('a, body: o)` | 9098 | 96.6% |
| `ifolEx('b, body: o)` | 580 | 6.2% |
| `ifolEx(i, body: o)` | 8567 | 90.9% |
| `isaAbs('a, body: 'b)` | 4655 | 49.4% |
| `isaAbs('a, body: ('a => o))` | 7578 | 80.4% |
| `isaAbs('a, body: ('b => o))` | 1195 | 12.7% |
| `isaAbs('a, body: (('a => 'b) => 'b))` | 508 | 5.4% |
| `isaAbs('a, body: o)` | 9167 | 97.3% |
| `isaAbs('b, body: 'a)` | 439 | 4.7% |
| `isaAbs('b, body: ('b => o))` | 4626 | 49.1% |
| `isaAbs('b, body: (('b => 'a) => 'a))` | 439 | 4.7% |
| `isaAbs('b, body: o)` | 4634 | 49.2% |
| `isaAbs(('a => 'b), body: 'b)` | 508 | 5.4% |
| `isaAbs(('a => o), body: o)` | 8963 | 95.1% |
| `isaAbs(('b => 'a), body: 'a)` | 439 | 4.7% |
| `isaAbs(('b => (('b => 'a) => 'a)), body: (('b => (('b => 'a) => 'a)) => o))` | 439 | 4.7% |
| `isaAbs(('b => (('b => 'a) => 'a)), body: o)` | 439 | 4.7% |
| `isaAbs((('a => o) => o), body: ((('a => o) => o) => o))` | 7323 | 77.7% |
| `isaAbs((('a => o) => o), body: o)` | 7323 | 77.7% |
| `isaAbs(((i => (i => 'a)) => (i => 'a)), body: (((i => (i => 'a)) => (i => 'a)) => o))` | 2773 | 29.4% |
| `isaAbs(((i => (i => 'a)) => (i => 'a)), body: o)` | 2773 | 29.4% |
| `isaAbs(((i => (i => (i => i))) => (i => i)), body: (((i => (i => (i => i))) => (i => i)) => o))` | 4 | 0.0% |
| `isaAbs(((i => (i => (i => i))) => (i => i)), body: o)` | 4 | 0.0% |
| `isaAbs(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), body: (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o))` | 38 | 0.4% |
| `isaAbs(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), body: o)` | 38 | 0.4% |
| `isaAbs(((i => (i => i)) => (i => i)), body: (((i => (i => i)) => (i => i)) => o))` | 2760 | 29.3% |
| `isaAbs(((i => (i => i)) => (i => i)), body: o)` | 2760 | 29.3% |
| `isaAbs(((i => i) => ((i => i) => (i => i))), body: (((i => i) => ((i => i) => (i => i))) => o))` | 2421 | 25.7% |
| `isaAbs(((i => i) => ((i => i) => (i => i))), body: o)` | 2421 | 25.7% |
| `isaAbs(((i => i) => (i => i)), body: (((i => i) => (i => i)) => o))` | 514 | 5.5% |
| `isaAbs(((i => i) => (i => i)), body: o)` | 514 | 5.5% |
| `isaAbs(((i => i) => o), body: (((i => i) => o) => o))` | 531 | 5.6% |
| `isaAbs(((i => i) => o), body: o)` | 531 | 5.6% |
| `isaAbs(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), body: (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o))` | 1 | 0.0% |
| `isaAbs(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), body: o)` | 1 | 0.0% |
| `isaAbs(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), body: (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o))` | 1 | 0.0% |
| `isaAbs(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), body: o)` | 1 | 0.0% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), body: (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o))` | 70 | 0.7% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), body: o)` | 70 | 0.7% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), body: (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o))` | 183 | 1.9% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), body: o)` | 183 | 1.9% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), body: (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o))` | 318 | 3.4% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), body: o)` | 318 | 3.4% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), body: (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o))` | 53 | 0.6% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), body: o)` | 53 | 0.6% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => o))), body: (((i => o) => ((i => (i => (i => o))) => (i => o))) => o))` | 155 | 1.6% |
| `isaAbs(((i => o) => ((i => (i => (i => o))) => (i => o))), body: o)` | 155 | 1.6% |
| `isaAbs(((i => o) => ((i => (i => o)) => ((i => i) => o))), body: (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o))` | 128 | 1.4% |
| `isaAbs(((i => o) => ((i => (i => o)) => ((i => i) => o))), body: o)` | 128 | 1.4% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), body: (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o))` | 243 | 2.6% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), body: o)` | 243 | 2.6% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), body: (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o))` | 225 | 2.4% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), body: o)` | 225 | 2.4% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => o))), body: (((i => o) => ((i => (i => o)) => (i => o))) => o))` | 141 | 1.5% |
| `isaAbs(((i => o) => ((i => (i => o)) => (i => o))), body: o)` | 141 | 1.5% |
| `isaAbs(((i => o) => ((i => (i => o)) => o)), body: (((i => o) => ((i => (i => o)) => o)) => o))` | 585 | 6.2% |
| `isaAbs(((i => o) => ((i => (i => o)) => o)), body: o)` | 585 | 6.2% |
| `isaAbs(((i => o) => ((i => o) => o)), body: (((i => o) => ((i => o) => o)) => o))` | 1163 | 12.3% |
| `isaAbs(((i => o) => ((i => o) => o)), body: o)` | 1163 | 12.3% |
| `isaAbs(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), body: (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o))` | 3 | 0.0% |
| `isaAbs(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), body: o)` | 3 | 0.0% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), body: (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o))` | 44 | 0.5% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), body: o)` | 44 | 0.5% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), body: (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o))` | 249 | 2.6% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), body: o)` | 249 | 2.6% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => (i => o)))), body: (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o))` | 96 | 1.0% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => (i => o)))), body: o)` | 96 | 1.0% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => o))), body: (((i => o) => (i => ((i => (i => o)) => o))) => o))` | 374 | 4.0% |
| `isaAbs(((i => o) => (i => ((i => (i => o)) => o))), body: o)` | 374 | 4.0% |
| `isaAbs(((i => o) => (i => ((i => o) => (i => o)))), body: (((i => o) => (i => ((i => o) => (i => o)))) => o))` | 46 | 0.5% |
| `isaAbs(((i => o) => (i => ((i => o) => (i => o)))), body: o)` | 46 | 0.5% |
| `isaAbs(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), body: (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o))` | 41 | 0.4% |
| `isaAbs(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), body: o)` | 41 | 0.4% |
| `isaAbs(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), body: (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o))` | 1 | 0.0% |
| `isaAbs(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), body: o)` | 1 | 0.0% |
| `isaAbs(((i => o) => (i => (i => (i => (i => (i => o)))))), body: (((i => o) => (i => (i => (i => (i => (i => o)))))) => o))` | 89 | 0.9% |
| `isaAbs(((i => o) => (i => (i => (i => (i => (i => o)))))), body: o)` | 89 | 0.9% |
| `isaAbs(((i => o) => (i => (i => (i => (i => o))))), body: (((i => o) => (i => (i => (i => (i => o))))) => o))` | 117 | 1.2% |
| `isaAbs(((i => o) => (i => (i => (i => (i => o))))), body: o)` | 117 | 1.2% |
| `isaAbs(((i => o) => (i => (i => (i => o)))), body: (((i => o) => (i => (i => (i => o)))) => o))` | 1025 | 10.9% |
| `isaAbs(((i => o) => (i => (i => (i => o)))), body: o)` | 1025 | 10.9% |
| `isaAbs(((i => o) => (i => (i => i))), body: (((i => o) => (i => (i => i))) => o))` | 44 | 0.5% |
| `isaAbs(((i => o) => (i => (i => i))), body: o)` | 44 | 0.5% |
| `isaAbs(((i => o) => (i => (i => o))), body: (((i => o) => (i => (i => o))) => o))` | 945 | 10.0% |
| `isaAbs(((i => o) => (i => (i => o))), body: o)` | 945 | 10.0% |
| `isaAbs(((i => o) => (i => i)), body: (((i => o) => (i => i)) => o))` | 2 | 0.0% |
| `isaAbs(((i => o) => (i => i)), body: o)` | 2 | 0.0% |
| `isaAbs(((i => o) => (i => o)), body: (((i => o) => (i => o)) => o))` | 670 | 7.1% |
| `isaAbs(((i => o) => (i => o)), body: o)` | 670 | 7.1% |
| `isaAbs(((i => o) => (o => (i => o))), body: (((i => o) => (o => (i => o))) => o))` | 92 | 1.0% |
| `isaAbs(((i => o) => (o => (i => o))), body: o)` | 92 | 1.0% |
| `isaAbs(((i => o) => i), body: (((i => o) => i) => o))` | 5274 | 56.0% |
| `isaAbs(((i => o) => i), body: o)` | 5274 | 56.0% |
| `isaAbs(((i => o) => o), body: (((i => o) => o) => o))` | 4100 | 43.5% |
| `isaAbs(((i => o) => o), body: o)` | 4102 | 43.5% |
| `isaAbs((i => 'a), body: ((i => 'a) => o))` | 2739 | 29.1% |
| `isaAbs((i => 'a), body: o)` | 2739 | 29.1% |
| `isaAbs((i => ((i => (i => (i => i))) => i)), body: ((i => ((i => (i => (i => i))) => i)) => o))` | 25 | 0.3% |
| `isaAbs((i => ((i => (i => (i => i))) => i)), body: o)` | 25 | 0.3% |
| `isaAbs((i => ((i => (i => i)) => (i => (i => i)))), body: ((i => ((i => (i => i)) => (i => (i => i)))) => o))` | 53 | 0.6% |
| `isaAbs((i => ((i => (i => i)) => (i => (i => i)))), body: o)` | 53 | 0.6% |
| `isaAbs((i => ((i => (i => i)) => (i => i))), body: ((i => ((i => (i => i)) => (i => i))) => o))` | 2044 | 21.7% |
| `isaAbs((i => ((i => (i => i)) => (i => i))), body: o)` | 2044 | 21.7% |
| `isaAbs((i => ((i => (i => i)) => i)), body: ((i => ((i => (i => i)) => i)) => o))` | 3706 | 39.3% |
| `isaAbs((i => ((i => (i => i)) => i)), body: o)` | 3706 | 39.3% |
| `isaAbs((i => ((i => (i => o)) => i)), body: ((i => ((i => (i => o)) => i)) => o))` | 7313 | 77.6% |
| `isaAbs((i => ((i => (i => o)) => i)), body: o)` | 7313 | 77.6% |
| `isaAbs((i => ((i => i) => (i => i))), body: ((i => ((i => i) => (i => i))) => o))` | 3854 | 40.9% |
| `isaAbs((i => ((i => i) => (i => i))), body: o)` | 3854 | 40.9% |
| `isaAbs((i => ((i => i) => i)), body: ((i => ((i => i) => i)) => o))` | 6215 | 66.0% |
| `isaAbs((i => ((i => i) => i)), body: o)` | 6215 | 66.0% |
| `isaAbs((i => ((i => i) => o)), body: ((i => ((i => i) => o)) => o))` | 4841 | 51.4% |
| `isaAbs((i => ((i => i) => o)), body: o)` | 4841 | 51.4% |
| `isaAbs((i => ((i => o) => i)), body: ((i => ((i => o) => i)) => o))` | 7247 | 76.9% |
| `isaAbs((i => ((i => o) => i)), body: o)` | 7247 | 76.9% |
| `isaAbs((i => ((i => o) => o)), body: ((i => ((i => o) => o)) => o))` | 7493 | 79.5% |
| `isaAbs((i => ((i => o) => o)), body: o)` | 7493 | 79.5% |
| `isaAbs((i => (i => 'a)), body: (i => 'a))` | 3297 | 35.0% |
| `isaAbs((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), body: ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o))` | 8 | 0.1% |
| `isaAbs((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), body: o)` | 8 | 0.1% |
| `isaAbs((i => (i => ((i => (i => i)) => (i => o)))), body: ((i => (i => ((i => (i => i)) => (i => o)))) => o))` | 4068 | 43.2% |
| `isaAbs((i => (i => ((i => (i => i)) => (i => o)))), body: o)` | 4068 | 43.2% |
| `isaAbs((i => (i => ((i => (i => i)) => i))), body: ((i => (i => ((i => (i => i)) => i))) => o))` | 4061 | 43.1% |
| `isaAbs((i => (i => ((i => (i => i)) => i))), body: o)` | 4061 | 43.1% |
| `isaAbs((i => (i => ((i => (i => i)) => o))), body: ((i => (i => ((i => (i => i)) => o))) => o))` | 439 | 4.7% |
| `isaAbs((i => (i => ((i => (i => i)) => o))), body: o)` | 439 | 4.7% |
| `isaAbs((i => (i => ((i => i) => ((i => i) => (i => o))))), body: ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o))` | 7 | 0.1% |
| `isaAbs((i => (i => ((i => i) => ((i => i) => (i => o))))), body: o)` | 7 | 0.1% |
| `isaAbs((i => (i => (i => ((i => (i => i)) => i)))), body: ((i => (i => (i => ((i => (i => i)) => i)))) => o))` | 896 | 9.5% |
| `isaAbs((i => (i => (i => ((i => (i => i)) => i)))), body: o)` | 896 | 9.5% |
| `isaAbs((i => (i => (i => ((i => i) => o)))), body: ((i => (i => (i => ((i => i) => o)))) => o))` | 21 | 0.2% |
| `isaAbs((i => (i => (i => ((i => i) => o)))), body: o)` | 21 | 0.2% |
| `isaAbs((i => (i => (i => (i => (i => (i => i)))))), body: ((i => (i => (i => (i => (i => (i => i)))))) => o))` | 35 | 0.4% |
| `isaAbs((i => (i => (i => (i => (i => (i => i)))))), body: o)` | 35 | 0.4% |
| `isaAbs((i => (i => (i => (i => (i => i))))), body: ((i => (i => (i => (i => (i => i))))) => o))` | 187 | 2.0% |
| `isaAbs((i => (i => (i => (i => (i => i))))), body: o)` | 187 | 2.0% |
| `isaAbs((i => (i => (i => (i => (i => o))))), body: ((i => (i => (i => (i => (i => o))))) => o))` | 9 | 0.1% |
| `isaAbs((i => (i => (i => (i => (i => o))))), body: ((i => (i => (i => (i => i)))) => o))` | 1 | 0.0% |
| `isaAbs((i => (i => (i => (i => (i => o))))), body: o)` | 9 | 0.1% |
| `isaAbs((i => (i => (i => (i => i)))), body: ((i => (i => (i => (i => i)))) => o))` | 1108 | 11.8% |
| `isaAbs((i => (i => (i => (i => i)))), body: ((i => (i => i)) => (i => (i => i))))` | 55 | 0.6% |
| `isaAbs((i => (i => (i => (i => i)))), body: ((i => (i => i)) => (i => i)))` | 24 | 0.3% |
| `isaAbs((i => (i => (i => (i => i)))), body: o)` | 1109 | 11.8% |
| `isaAbs((i => (i => (i => (i => o)))), body: ((i => (i => (i => (i => o)))) => o))` | 114 | 1.2% |
| `isaAbs((i => (i => (i => (i => o)))), body: ((i => (i => (i => i))) => o))` | 2 | 0.0% |
| `isaAbs((i => (i => (i => (i => o)))), body: o)` | 114 | 1.2% |
| `isaAbs((i => (i => (i => i))), body: ((i => (i => (i => i))) => o))` | 3075 | 32.6% |
| `isaAbs((i => (i => (i => i))), body: ((i => (i => i)) => (i => i)))` | 10 | 0.1% |
| `isaAbs((i => (i => (i => i))), body: (i => (i => i)))` | 103 | 1.1% |
| `isaAbs((i => (i => (i => i))), body: (i => i))` | 1097 | 11.6% |
| `isaAbs((i => (i => (i => i))), body: i)` | 30 | 0.3% |
| `isaAbs((i => (i => (i => i))), body: o)` | 3077 | 32.7% |
| `isaAbs((i => (i => (i => o))), body: ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))` | 136 | 1.4% |
| `isaAbs((i => (i => (i => o))), body: ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))` | 136 | 1.4% |
| `isaAbs((i => (i => (i => o))), body: ((i => (i => (i => o))) => o))` | 284 | 3.0% |
| `isaAbs((i => (i => (i => o))), body: ((i => (i => i)) => o))` | 202 | 2.1% |
| `isaAbs((i => (i => (i => o))), body: ((i => (i => o)) => (i => (i => o))))` | 136 | 1.4% |
| `isaAbs((i => (i => (i => o))), body: (i => (i => (i => o))))` | 441 | 4.7% |
| `isaAbs((i => (i => (i => o))), body: (i => (i => o)))` | 171 | 1.8% |
| `isaAbs((i => (i => (i => o))), body: (i => o))` | 222 | 2.4% |
| `isaAbs((i => (i => (i => o))), body: o)` | 284 | 3.0% |
| `isaAbs((i => (i => i)), body: ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))` | 55 | 0.6% |
| `isaAbs((i => (i => i)), body: ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))` | 24 | 0.3% |
| `isaAbs((i => (i => i)), body: ((i => (i => (i => i))) => ((i => (i => i)) => (i => i))))` | 10 | 0.1% |
| `isaAbs((i => (i => i)), body: ((i => (i => (i => i))) => (i => i)))` | 37 | 0.4% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))` | 55 | 0.6% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))))` | 24 | 0.3% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))` | 21 | 0.2% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => (i => i)))` | 23 | 0.2% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => i))` | 9 | 0.1% |
| `isaAbs((i => (i => i)), body: ((i => (i => i)) => o))` | 6923 | 73.5% |
| `isaAbs((i => (i => i)), body: ((i => i) => (i => i)))` | 965 | 10.2% |
| `isaAbs((i => (i => i)), body: (i => ((i => (i => i)) => (i => i))))` | 35 | 0.4% |
| `isaAbs((i => (i => i)), body: (i => (i => i)))` | 110 | 1.2% |
| `isaAbs((i => (i => i)), body: (i => i))` | 3439 | 36.5% |
| `isaAbs((i => (i => i)), body: (i => o))` | 5033 | 53.4% |
| `isaAbs((i => (i => i)), body: i)` | 5018 | 53.3% |
| `isaAbs((i => (i => i)), body: o)` | 6944 | 73.7% |
| `isaAbs((i => (i => o)), body: ((i => (i => o)) => o))` | 7387 | 78.4% |
| `isaAbs((i => (i => o)), body: ((i => i) => o))` | 149 | 1.6% |
| `isaAbs((i => (i => o)), body: (i => (i => (i => (i => o)))))` | 341 | 3.6% |
| `isaAbs((i => (i => o)), body: (i => (i => (i => o))))` | 323 | 3.4% |
| `isaAbs((i => (i => o)), body: (i => (i => o)))` | 348 | 3.7% |
| `isaAbs((i => (i => o)), body: (i => o))` | 421 | 4.5% |
| `isaAbs((i => (i => o)), body: i)` | 8957 | 95.1% |
| `isaAbs((i => (i => o)), body: o)` | 7524 | 79.9% |
| `isaAbs((i => i), body: ((i => (i => (i => i))) => (i => i)))` | 92 | 1.0% |
| `isaAbs((i => i), body: ((i => (i => i)) => ((i => (i => i)) => (i => i))))` | 23 | 0.2% |
| `isaAbs((i => i), body: ((i => i) => (i => i)))` | 2872 | 30.5% |
| `isaAbs((i => i), body: ((i => i) => (i => o)))` | 7 | 0.1% |
| `isaAbs((i => i), body: ((i => i) => o))` | 6847 | 72.7% |
| `isaAbs((i => i), body: (i => (i => i)))` | 442 | 4.7% |
| `isaAbs((i => i), body: (i => i))` | 5180 | 55.0% |
| `isaAbs((i => i), body: (i => o))` | 7 | 0.1% |
| `isaAbs((i => i), body: i)` | 7209 | 76.5% |
| `isaAbs((i => i), body: o)` | 6991 | 74.2% |
| `isaAbs((i => o), body: ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))` | 1 | 0.0% |
| `isaAbs((i => o), body: ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))` | 1 | 0.0% |
| `isaAbs((i => o), body: ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))` | 136 | 1.4% |
| `isaAbs((i => o), body: ((i => (i => (i => o))) => ((i => (i => i)) => o)))` | 183 | 1.9% |
| `isaAbs((i => o), body: ((i => (i => (i => o))) => (i => (i => (i => o)))))` | 441 | 4.7% |
| `isaAbs((i => o), body: ((i => (i => (i => o))) => (i => (i => o))))` | 75 | 0.8% |
| `isaAbs((i => o), body: ((i => (i => (i => o))) => (i => o)))` | 222 | 2.4% |
| `isaAbs((i => o), body: ((i => (i => o)) => ((i => i) => o)))` | 128 | 1.4% |
| `isaAbs((i => o), body: ((i => (i => o)) => (i => (i => (i => (i => o))))))` | 341 | 3.6% |
| `isaAbs((i => o), body: ((i => (i => o)) => (i => (i => (i => o)))))` | 323 | 3.4% |
| `isaAbs((i => o), body: ((i => (i => o)) => (i => o)))` | 201 | 2.1% |
| `isaAbs((i => o), body: ((i => (i => o)) => o))` | 821 | 8.7% |
| `isaAbs((i => o), body: ((i => o) => ((i => (i => o)) => o)))` | 429 | 4.6% |
| `isaAbs((i => o), body: ((i => o) => o))` | 5713 | 60.6% |
| `isaAbs((i => o), body: (i => ((i => (i => (i => o))) => (i => (i => o)))))` | 3 | 0.0% |
| `isaAbs((i => o), body: (i => ((i => (i => o)) => ((i => i) => o))))` | 63 | 0.7% |
| `isaAbs((i => o), body: (i => ((i => (i => o)) => (i => (i => o)))))` | 348 | 3.7% |
| `isaAbs((i => o), body: (i => ((i => (i => o)) => (i => o))))` | 162 | 1.7% |
| `isaAbs((i => o), body: (i => ((i => (i => o)) => o)))` | 599 | 6.4% |
| `isaAbs((i => o), body: (i => ((i => o) => (i => o))))` | 65 | 0.7% |
| `isaAbs((i => o), body: (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))` | 60 | 0.6% |
| `isaAbs((i => o), body: (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))` | 1 | 0.0% |
| `isaAbs((i => o), body: (i => (i => (i => (i => (i => o))))))` | 186 | 2.0% |
| `isaAbs((i => o), body: (i => (i => (i => (i => o)))))` | 307 | 3.3% |
| `isaAbs((i => o), body: (i => (i => (i => o))))` | 1249 | 13.3% |
| `isaAbs((i => o), body: (i => (i => i)))` | 44 | 0.5% |
| `isaAbs((i => o), body: (i => (i => o)))` | 1170 | 12.4% |
| `isaAbs((i => o), body: (i => i))` | 446 | 4.7% |
| `isaAbs((i => o), body: (i => o))` | 1019 | 10.8% |
| `isaAbs((i => o), body: (o => (i => o)))` | 132 | 1.4% |
| `isaAbs((i => o), body: i)` | 8237 | 87.4% |
| `isaAbs((i => o), body: o)` | 8650 | 91.8% |
| `isaAbs((o => (i => (i => i))), body: ((o => (i => (i => i))) => o))` | 5018 | 53.3% |
| `isaAbs((o => (i => (i => i))), body: o)` | 5018 | 53.3% |
| `isaAbs((o => (o => o)), body: ((o => (o => o)) => o))` | 7841 | 83.2% |
| `isaAbs((o => (o => o)), body: o)` | 7841 | 83.2% |
| `isaAbs((o => i), body: ((o => i) => o))` | 882 | 9.4% |
| `isaAbs((o => i), body: o)` | 882 | 9.4% |
| `isaAbs((o => o), body: ((o => o) => o))` | 7819 | 83.0% |
| `isaAbs((o => o), body: o)` | 7819 | 83.0% |
| `isaAbs(i, body: 'a)` | 3297 | 35.0% |
| `isaAbs(i, body: ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))` | 1 | 0.0% |
| `isaAbs(i, body: ((i => (i => (i => i))) => i))` | 30 | 0.3% |
| `isaAbs(i, body: ((i => (i => (i => o))) => ((i => (i => i)) => o)))` | 60 | 0.6% |
| `isaAbs(i, body: ((i => (i => (i => o))) => (i => (i => o))))` | 3 | 0.0% |
| `isaAbs(i, body: ((i => (i => i)) => ((i => (i => i)) => i)))` | 9 | 0.1% |
| `isaAbs(i, body: ((i => (i => i)) => (i => (i => i))))` | 55 | 0.6% |
| `isaAbs(i, body: ((i => (i => i)) => (i => i)))` | 2493 | 26.5% |
| `isaAbs(i, body: ((i => (i => i)) => (i => o)))` | 5033 | 53.4% |
| `isaAbs(i, body: ((i => (i => i)) => i))` | 5018 | 53.3% |
| `isaAbs(i, body: ((i => (i => i)) => o))` | 439 | 4.7% |
| `isaAbs(i, body: ((i => (i => o)) => ((i => i) => o)))` | 63 | 0.7% |
| `isaAbs(i, body: ((i => (i => o)) => (i => (i => o))))` | 348 | 3.7% |
| `isaAbs(i, body: ((i => (i => o)) => (i => o)))` | 162 | 1.7% |
| `isaAbs(i, body: ((i => (i => o)) => i))` | 8957 | 95.1% |
| `isaAbs(i, body: ((i => (i => o)) => o))` | 599 | 6.4% |
| `isaAbs(i, body: ((i => i) => ((i => i) => (i => o))))` | 7 | 0.1% |
| `isaAbs(i, body: ((i => i) => (i => i)))` | 4781 | 50.8% |
| `isaAbs(i, body: ((i => i) => i))` | 7209 | 76.5% |
| `isaAbs(i, body: ((i => i) => o))` | 4846 | 51.4% |
| `isaAbs(i, body: ((i => o) => (i => o)))` | 65 | 0.7% |
| `isaAbs(i, body: ((i => o) => i))` | 8137 | 86.4% |
| `isaAbs(i, body: ((i => o) => o))` | 8395 | 89.1% |
| `isaAbs(i, body: (i => 'a))` | 3297 | 35.0% |
| `isaAbs(i, body: (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))` | 1 | 0.0% |
| `isaAbs(i, body: (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))` | 60 | 0.6% |
| `isaAbs(i, body: (i => ((i => (i => i)) => ((i => (i => i)) => i))))` | 9 | 0.1% |
| `isaAbs(i, body: (i => ((i => (i => i)) => (i => i))))` | 13 | 0.1% |
| `isaAbs(i, body: (i => ((i => (i => i)) => (i => o))))` | 5033 | 53.4% |
| `isaAbs(i, body: (i => ((i => (i => i)) => i)))` | 5018 | 53.3% |
| `isaAbs(i, body: (i => ((i => (i => i)) => o)))` | 439 | 4.7% |
| `isaAbs(i, body: (i => ((i => i) => ((i => i) => (i => o)))))` | 7 | 0.1% |
| `isaAbs(i, body: (i => ((i => i) => o)))` | 21 | 0.2% |
| `isaAbs(i, body: (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))` | 1 | 0.0% |
| `isaAbs(i, body: (i => (i => ((i => (i => i)) => i))))` | 947 | 10.1% |
| `isaAbs(i, body: (i => (i => ((i => i) => o))))` | 21 | 0.2% |
| `isaAbs(i, body: (i => (i => (i => (i => (i => i))))))` | 39 | 0.4% |
| `isaAbs(i, body: (i => (i => (i => (i => i)))))` | 493 | 5.2% |
| `isaAbs(i, body: (i => (i => (i => (i => o)))))` | 201 | 2.1% |
| `isaAbs(i, body: (i => (i => (i => i))))` | 2099 | 22.3% |
| `isaAbs(i, body: (i => (i => (i => o))))` | 624 | 6.6% |
| `isaAbs(i, body: (i => (i => i)))` | 3948 | 41.9% |
| `isaAbs(i, body: (i => (i => o)))` | 1797 | 19.1% |
| `isaAbs(i, body: (i => i))` | 8796 | 93.4% |
| `isaAbs(i, body: (i => o))` | 9238 | 98.1% |
| `isaAbs(i, body: i)` | 8930 | 94.8% |
| `isaAbs(i, body: o)` | 9342 | 99.2% |
| `isaAbs(o, body: (i => (i => i)))` | 5590 | 59.3% |
| `isaAbs(o, body: (i => o))` | 132 | 1.4% |
| `isaAbs(o, body: (o => o))` | 8409 | 89.3% |
| `isaAbs(o, body: i)` | 983 | 10.4% |
| `isaAbs(o, body: o)` | 8828 | 93.7% |
| `isaAllElim(o, 'a)` | 7972 | 84.6% |
| `isaAllElim(o, 'b)` | 4636 | 49.2% |
| `isaAllElim(o, ('a => 'b))` | 4626 | 49.1% |
| `isaAllElim(o, ('a => ('a => o)))` | 7578 | 80.4% |
| `isaAllElim(o, ('a => ('b => o)))` | 1195 | 12.7% |
| `isaAllElim(o, ('a => o))` | 7950 | 84.4% |
| `isaAllElim(o, ('b => 'a))` | 439 | 4.7% |
| `isaAllElim(o, ('b => ('b => o)))` | 4626 | 49.1% |
| `isaAllElim(o, ('b => (('b => 'a) => 'a)))` | 439 | 4.7% |
| `isaAllElim(o, ('b => o))` | 4634 | 49.2% |
| `isaAllElim(o, (('a => o) => o))` | 7324 | 77.7% |
| `isaAllElim(o, (('b => 'a) => 'a))` | 439 | 4.7% |
| `isaAllElim(o, (('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)))` | 439 | 4.7% |
| `isaAllElim(o, (('b => (('b => 'a) => 'a)) => o))` | 439 | 4.7% |
| `isaAllElim(o, ((('a => o) => o) => ((('a => o) => o) => o)))` | 7323 | 77.7% |
| `isaAllElim(o, ((('a => o) => o) => o))` | 7323 | 77.7% |
| `isaAllElim(o, (((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)))` | 2773 | 29.4% |
| `isaAllElim(o, (((i => (i => 'a)) => (i => 'a)) => o))` | 2773 | 29.4% |
| `isaAllElim(o, (((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)))` | 4 | 0.0% |
| `isaAllElim(o, (((i => (i => (i => i))) => (i => i)) => o))` | 4 | 0.0% |
| `isaAllElim(o, (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)))` | 38 | 0.4% |
| `isaAllElim(o, (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o))` | 38 | 0.4% |
| `isaAllElim(o, (((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)))` | 2760 | 29.3% |
| `isaAllElim(o, (((i => (i => i)) => (i => i)) => o))` | 2760 | 29.3% |
| `isaAllElim(o, (((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)))` | 2421 | 25.7% |
| `isaAllElim(o, (((i => i) => ((i => i) => (i => i))) => o))` | 2421 | 25.7% |
| `isaAllElim(o, (((i => i) => (i => i)) => (((i => i) => (i => i)) => o)))` | 514 | 5.5% |
| `isaAllElim(o, (((i => i) => (i => i)) => o))` | 514 | 5.5% |
| `isaAllElim(o, (((i => i) => o) => (((i => i) => o) => o)))` | 531 | 5.6% |
| `isaAllElim(o, (((i => i) => o) => o))` | 531 | 5.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)))` | 70 | 0.7% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o))` | 70 | 0.7% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)))` | 183 | 1.9% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o))` | 183 | 1.9% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)))` | 318 | 3.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o))` | 318 | 3.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)))` | 53 | 0.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o))` | 53 | 0.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)))` | 155 | 1.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => (i => o))) => (i => o))) => o))` | 155 | 1.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)))` | 128 | 1.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o))` | 128 | 1.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)))` | 243 | 2.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o))` | 243 | 2.6% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)))` | 225 | 2.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o))` | 225 | 2.4% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)))` | 141 | 1.5% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => (i => o))) => o))` | 141 | 1.5% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)))` | 585 | 6.2% |
| `isaAllElim(o, (((i => o) => ((i => (i => o)) => o)) => o))` | 585 | 6.2% |
| `isaAllElim(o, (((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)))` | 1163 | 12.3% |
| `isaAllElim(o, (((i => o) => ((i => o) => o)) => o))` | 1163 | 12.3% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)))` | 3 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o))` | 3 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)))` | 44 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o))` | 44 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)))` | 249 | 2.6% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o))` | 249 | 2.6% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)))` | 96 | 1.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o))` | 96 | 1.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)))` | 374 | 4.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => (i => o)) => o))) => o))` | 374 | 4.0% |
| `isaAllElim(o, (((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)))` | 46 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => ((i => o) => (i => o)))) => o))` | 46 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)))` | 41 | 0.4% |
| `isaAllElim(o, (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o))` | 41 | 0.4% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o))` | 1 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)))` | 89 | 0.9% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => (i => (i => o)))))) => o))` | 89 | 0.9% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)))` | 117 | 1.2% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => (i => o))))) => o))` | 117 | 1.2% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)))` | 1025 | 10.9% |
| `isaAllElim(o, (((i => o) => (i => (i => (i => o)))) => o))` | 1025 | 10.9% |
| `isaAllElim(o, (((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)))` | 44 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => (i => i))) => o))` | 44 | 0.5% |
| `isaAllElim(o, (((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)))` | 945 | 10.0% |
| `isaAllElim(o, (((i => o) => (i => (i => o))) => o))` | 945 | 10.0% |
| `isaAllElim(o, (((i => o) => (i => i)) => (((i => o) => (i => i)) => o)))` | 2 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => i)) => o))` | 2 | 0.0% |
| `isaAllElim(o, (((i => o) => (i => o)) => (((i => o) => (i => o)) => o)))` | 670 | 7.1% |
| `isaAllElim(o, (((i => o) => (i => o)) => o))` | 670 | 7.1% |
| `isaAllElim(o, (((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)))` | 92 | 1.0% |
| `isaAllElim(o, (((i => o) => (o => (i => o))) => o))` | 92 | 1.0% |
| `isaAllElim(o, (((i => o) => i) => (((i => o) => i) => o)))` | 5274 | 56.0% |
| `isaAllElim(o, (((i => o) => i) => o))` | 5274 | 56.0% |
| `isaAllElim(o, (((i => o) => o) => (((i => o) => o) => o)))` | 4100 | 43.5% |
| `isaAllElim(o, (((i => o) => o) => o))` | 4102 | 43.5% |
| `isaAllElim(o, ((i => 'a) => ((i => 'a) => o)))` | 2739 | 29.1% |
| `isaAllElim(o, ((i => 'a) => o))` | 2739 | 29.1% |
| `isaAllElim(o, ((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)))` | 25 | 0.3% |
| `isaAllElim(o, ((i => ((i => (i => (i => i))) => i)) => o))` | 25 | 0.3% |
| `isaAllElim(o, ((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)))` | 53 | 0.6% |
| `isaAllElim(o, ((i => ((i => (i => i)) => (i => (i => i)))) => o))` | 53 | 0.6% |
| `isaAllElim(o, ((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)))` | 2044 | 21.7% |
| `isaAllElim(o, ((i => ((i => (i => i)) => (i => i))) => o))` | 2044 | 21.7% |
| `isaAllElim(o, ((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)))` | 3706 | 39.3% |
| `isaAllElim(o, ((i => ((i => (i => i)) => i)) => o))` | 3706 | 39.3% |
| `isaAllElim(o, ((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)))` | 7313 | 77.6% |
| `isaAllElim(o, ((i => ((i => (i => o)) => i)) => o))` | 7313 | 77.6% |
| `isaAllElim(o, ((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)))` | 3854 | 40.9% |
| `isaAllElim(o, ((i => ((i => i) => (i => i))) => o))` | 3854 | 40.9% |
| `isaAllElim(o, ((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)))` | 6215 | 66.0% |
| `isaAllElim(o, ((i => ((i => i) => i)) => o))` | 6215 | 66.0% |
| `isaAllElim(o, ((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)))` | 4841 | 51.4% |
| `isaAllElim(o, ((i => ((i => i) => o)) => o))` | 4841 | 51.4% |
| `isaAllElim(o, ((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)))` | 7247 | 76.9% |
| `isaAllElim(o, ((i => ((i => o) => i)) => o))` | 7247 | 76.9% |
| `isaAllElim(o, ((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)))` | 7493 | 79.5% |
| `isaAllElim(o, ((i => ((i => o) => o)) => o))` | 7493 | 79.5% |
| `isaAllElim(o, ((i => (i => 'a)) => (i => 'a)))` | 2773 | 29.4% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)))` | 8 | 0.1% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o))` | 8 | 0.1% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)))` | 4068 | 43.2% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => (i => o)))) => o))` | 4068 | 43.2% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)))` | 4061 | 43.1% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => i))) => o))` | 4061 | 43.1% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)))` | 439 | 4.7% |
| `isaAllElim(o, ((i => (i => ((i => (i => i)) => o))) => o))` | 439 | 4.7% |
| `isaAllElim(o, ((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)))` | 7 | 0.1% |
| `isaAllElim(o, ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o))` | 7 | 0.1% |
| `isaAllElim(o, ((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)))` | 896 | 9.5% |
| `isaAllElim(o, ((i => (i => (i => ((i => (i => i)) => i)))) => o))` | 896 | 9.5% |
| `isaAllElim(o, ((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)))` | 21 | 0.2% |
| `isaAllElim(o, ((i => (i => (i => ((i => i) => o)))) => o))` | 21 | 0.2% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)))` | 35 | 0.4% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => (i => i)))))) => o))` | 35 | 0.4% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)))` | 187 | 2.0% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => i))))) => o))` | 187 | 2.0% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)))` | 9 | 0.1% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))` | 1 | 0.0% |
| `isaAllElim(o, ((i => (i => (i => (i => (i => o))))) => o))` | 9 | 0.1% |
| `isaAllElim(o, ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)))` | 1108 | 11.8% |
| `isaAllElim(o, ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))` | 38 | 0.4% |
| `isaAllElim(o, ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))` | 24 | 0.3% |
| `isaAllElim(o, ((i => (i => (i => (i => i)))) => o))` | 1109 | 11.8% |
| `isaAllElim(o, ((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)))` | 114 | 1.2% |
| `isaAllElim(o, ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))` | 2 | 0.0% |
| `isaAllElim(o, ((i => (i => (i => (i => o)))) => o))` | 114 | 1.2% |
| `isaAllElim(o, ((i => (i => (i => i))) => ((i => (i => (i => i))) => o)))` | 3075 | 32.6% |
| `isaAllElim(o, ((i => (i => (i => i))) => ((i => (i => i)) => (i => i))))` | 10 | 0.1% |
| `isaAllElim(o, ((i => (i => (i => i))) => (i => (i => i))))` | 103 | 1.1% |
| `isaAllElim(o, ((i => (i => (i => i))) => (i => i)))` | 1096 | 11.6% |
| `isaAllElim(o, ((i => (i => (i => i))) => i))` | 25 | 0.3% |
| `isaAllElim(o, ((i => (i => (i => i))) => o))` | 3077 | 32.7% |
| `isaAllElim(o, ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))` | 70 | 0.7% |
| `isaAllElim(o, ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))` | 70 | 0.7% |
| `isaAllElim(o, ((i => (i => (i => o))) => ((i => (i => (i => o))) => o)))` | 284 | 3.0% |
| `isaAllElim(o, ((i => (i => (i => o))) => ((i => (i => i)) => o)))` | 185 | 2.0% |
| `isaAllElim(o, ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))` | 70 | 0.7% |
| `isaAllElim(o, ((i => (i => (i => o))) => (i => (i => (i => o)))))` | 318 | 3.4% |
| `isaAllElim(o, ((i => (i => (i => o))) => (i => (i => o))))` | 149 | 1.6% |
| `isaAllElim(o, ((i => (i => (i => o))) => (i => o)))` | 156 | 1.7% |
| `isaAllElim(o, ((i => (i => (i => o))) => o))` | 284 | 3.0% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))` | 38 | 0.4% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))))` | 24 | 0.3% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))))` | 10 | 0.1% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))` | 37 | 0.4% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))))` | 38 | 0.4% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))))` | 24 | 0.3% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))))` | 21 | 0.2% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => (i => i))))` | 23 | 0.2% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => i)))` | 8 | 0.1% |
| `isaAllElim(o, ((i => (i => i)) => ((i => (i => i)) => o)))` | 6923 | 73.5% |
| `isaAllElim(o, ((i => (i => i)) => ((i => i) => (i => i))))` | 965 | 10.2% |
| `isaAllElim(o, ((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))))` | 35 | 0.4% |
| `isaAllElim(o, ((i => (i => i)) => (i => (i => i))))` | 91 | 1.0% |
| `isaAllElim(o, ((i => (i => i)) => (i => i)))` | 2884 | 30.6% |
| `isaAllElim(o, ((i => (i => i)) => (i => o)))` | 4068 | 43.2% |
| `isaAllElim(o, ((i => (i => i)) => i))` | 4065 | 43.2% |
| `isaAllElim(o, ((i => (i => i)) => o))` | 6927 | 73.5% |
| `isaAllElim(o, ((i => (i => o)) => ((i => (i => o)) => o)))` | 7387 | 78.4% |
| `isaAllElim(o, ((i => (i => o)) => ((i => i) => o)))` | 132 | 1.4% |
| `isaAllElim(o, ((i => (i => o)) => (i => (i => (i => (i => o))))))` | 243 | 2.6% |
| `isaAllElim(o, ((i => (i => o)) => (i => (i => (i => o)))))` | 225 | 2.4% |
| `isaAllElim(o, ((i => (i => o)) => (i => (i => o))))` | 250 | 2.7% |
| `isaAllElim(o, ((i => (i => o)) => (i => o)))` | 344 | 3.7% |
| `isaAllElim(o, ((i => (i => o)) => i))` | 7313 | 77.6% |
| `isaAllElim(o, ((i => (i => o)) => o))` | 7404 | 78.6% |
| `isaAllElim(o, ((i => i) => ((i => (i => (i => i))) => (i => i))))` | 92 | 1.0% |
| `isaAllElim(o, ((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))))` | 23 | 0.2% |
| `isaAllElim(o, ((i => i) => ((i => i) => (i => i))))` | 2421 | 25.7% |
| `isaAllElim(o, ((i => i) => ((i => i) => (i => o))))` | 7 | 0.1% |
| `isaAllElim(o, ((i => i) => ((i => i) => o)))` | 6847 | 72.7% |
| `isaAllElim(o, ((i => i) => (i => (i => i))))` | 442 | 4.7% |
| `isaAllElim(o, ((i => i) => (i => i)))` | 4223 | 44.8% |
| `isaAllElim(o, ((i => i) => (i => o)))` | 7 | 0.1% |
| `isaAllElim(o, ((i => i) => i))` | 6229 | 66.1% |
| `isaAllElim(o, ((i => i) => o))` | 6955 | 73.8% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))))` | 1 | 0.0% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))` | 1 | 0.0% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))))` | 70 | 0.7% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))))` | 183 | 1.9% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))))` | 318 | 3.4% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => o))) => (i => (i => o)))))` | 53 | 0.6% |
| `isaAllElim(o, ((i => o) => ((i => (i => (i => o))) => (i => o))))` | 155 | 1.6% |
| `isaAllElim(o, ((i => o) => ((i => (i => o)) => ((i => i) => o))))` | 128 | 1.4% |
| `isaAllElim(o, ((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))))` | 243 | 2.6% |
| `isaAllElim(o, ((i => o) => ((i => (i => o)) => (i => (i => (i => o))))))` | 225 | 2.4% |
| `isaAllElim(o, ((i => o) => ((i => (i => o)) => (i => o))))` | 141 | 1.5% |
| `isaAllElim(o, ((i => o) => ((i => (i => o)) => o)))` | 597 | 6.3% |
| `isaAllElim(o, ((i => o) => ((i => o) => ((i => (i => o)) => o))))` | 429 | 4.6% |
| `isaAllElim(o, ((i => o) => ((i => o) => o)))` | 5453 | 57.9% |
| `isaAllElim(o, ((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))))` | 3 | 0.0% |
| `isaAllElim(o, ((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))))` | 44 | 0.5% |
| `isaAllElim(o, ((i => o) => (i => ((i => (i => o)) => (i => (i => o))))))` | 249 | 2.6% |
| `isaAllElim(o, ((i => o) => (i => ((i => (i => o)) => (i => o)))))` | 96 | 1.0% |
| `isaAllElim(o, ((i => o) => (i => ((i => (i => o)) => o))))` | 374 | 4.0% |
| `isaAllElim(o, ((i => o) => (i => ((i => o) => (i => o)))))` | 46 | 0.5% |
| `isaAllElim(o, ((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))))` | 41 | 0.4% |
| `isaAllElim(o, ((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))))` | 1 | 0.0% |
| `isaAllElim(o, ((i => o) => (i => (i => (i => (i => (i => o)))))))` | 89 | 0.9% |
| `isaAllElim(o, ((i => o) => (i => (i => (i => (i => o))))))` | 225 | 2.4% |
| `isaAllElim(o, ((i => o) => (i => (i => (i => o)))))` | 1026 | 10.9% |
| `isaAllElim(o, ((i => o) => (i => (i => i))))` | 44 | 0.5% |
| `isaAllElim(o, ((i => o) => (i => (i => o))))` | 946 | 10.0% |
| `isaAllElim(o, ((i => o) => (i => i)))` | 445 | 4.7% |
| `isaAllElim(o, ((i => o) => (i => o)))` | 838 | 8.9% |
| `isaAllElim(o, ((i => o) => (o => (i => o))))` | 92 | 1.0% |
| `isaAllElim(o, ((i => o) => i))` | 7257 | 77.0% |
| `isaAllElim(o, ((i => o) => o))` | 7746 | 82.2% |
| `isaAllElim(o, ((o => (i => (i => i))) => ((o => (i => (i => i))) => o)))` | 5018 | 53.3% |
| `isaAllElim(o, ((o => (i => (i => i))) => o))` | 5018 | 53.3% |
| `isaAllElim(o, ((o => (o => o)) => ((o => (o => o)) => o)))` | 7841 | 83.2% |
| `isaAllElim(o, ((o => (o => o)) => o))` | 7841 | 83.2% |
| `isaAllElim(o, ((o => i) => ((o => i) => o)))` | 882 | 9.4% |
| `isaAllElim(o, ((o => i) => o))` | 882 | 9.4% |
| `isaAllElim(o, ((o => o) => ((o => o) => o)))` | 7819 | 83.0% |
| `isaAllElim(o, ((o => o) => o))` | 7819 | 83.0% |
| `isaAllElim(o, (i => 'a))` | 2773 | 29.4% |
| `isaAllElim(o, (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))` | 1 | 0.0% |
| `isaAllElim(o, (i => ((i => (i => (i => i))) => i)))` | 25 | 0.3% |
| `isaAllElim(o, (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))` | 41 | 0.4% |
| `isaAllElim(o, (i => ((i => (i => (i => o))) => (i => (i => o)))))` | 3 | 0.0% |
| `isaAllElim(o, (i => ((i => (i => i)) => ((i => (i => i)) => i))))` | 8 | 0.1% |
| `isaAllElim(o, (i => ((i => (i => i)) => (i => (i => i)))))` | 53 | 0.6% |
| `isaAllElim(o, (i => ((i => (i => i)) => (i => i))))` | 2100 | 22.3% |
| `isaAllElim(o, (i => ((i => (i => i)) => (i => o))))` | 4068 | 43.2% |
| `isaAllElim(o, (i => ((i => (i => i)) => i)))` | 4064 | 43.1% |
| `isaAllElim(o, (i => ((i => (i => i)) => o)))` | 439 | 4.7% |
| `isaAllElim(o, (i => ((i => (i => o)) => ((i => i) => o))))` | 44 | 0.5% |
| `isaAllElim(o, (i => ((i => (i => o)) => (i => (i => o)))))` | 249 | 2.6% |
| `isaAllElim(o, (i => ((i => (i => o)) => (i => o))))` | 96 | 1.0% |
| `isaAllElim(o, (i => ((i => (i => o)) => i)))` | 7313 | 77.6% |
| `isaAllElim(o, (i => ((i => (i => o)) => o)))` | 374 | 4.0% |
| `isaAllElim(o, (i => ((i => i) => ((i => i) => (i => o)))))` | 7 | 0.1% |
| `isaAllElim(o, (i => ((i => i) => (i => i))))` | 3854 | 40.9% |
| `isaAllElim(o, (i => ((i => i) => i)))` | 6226 | 66.1% |
| `isaAllElim(o, (i => ((i => i) => o)))` | 4845 | 51.4% |
| `isaAllElim(o, (i => ((i => o) => (i => o))))` | 46 | 0.5% |
| `isaAllElim(o, (i => ((i => o) => i)))` | 7247 | 76.9% |
| `isaAllElim(o, (i => ((i => o) => o)))` | 7494 | 79.6% |
| `isaAllElim(o, (i => (i => 'a)))` | 2773 | 29.4% |
| `isaAllElim(o, (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))` | 1 | 0.0% |
| `isaAllElim(o, (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))` | 41 | 0.4% |
| `isaAllElim(o, (i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))))` | 8 | 0.1% |
| `isaAllElim(o, (i => (i => ((i => (i => i)) => (i => i)))))` | 13 | 0.1% |
| `isaAllElim(o, (i => (i => ((i => (i => i)) => (i => o)))))` | 4068 | 43.2% |
| `isaAllElim(o, (i => (i => ((i => (i => i)) => i))))` | 4062 | 43.1% |
| `isaAllElim(o, (i => (i => ((i => (i => i)) => o))))` | 439 | 4.7% |
| `isaAllElim(o, (i => (i => ((i => i) => ((i => i) => (i => o))))))` | 7 | 0.1% |
| `isaAllElim(o, (i => (i => ((i => i) => o))))` | 21 | 0.2% |
| `isaAllElim(o, (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))` | 1 | 0.0% |
| `isaAllElim(o, (i => (i => (i => ((i => (i => i)) => i)))))` | 896 | 9.5% |
| `isaAllElim(o, (i => (i => (i => ((i => i) => o)))))` | 21 | 0.2% |
| `isaAllElim(o, (i => (i => (i => (i => (i => (i => i)))))))` | 35 | 0.4% |
| `isaAllElim(o, (i => (i => (i => (i => (i => i))))))` | 341 | 3.6% |
| `isaAllElim(o, (i => (i => (i => (i => (i => o))))))` | 99 | 1.1% |
| `isaAllElim(o, (i => (i => (i => (i => i)))))` | 1733 | 18.4% |
| `isaAllElim(o, (i => (i => (i => (i => o)))))` | 435 | 4.6% |
| `isaAllElim(o, (i => (i => (i => i))))` | 3237 | 34.4% |
| `isaAllElim(o, (i => (i => (i => o))))` | 1482 | 15.7% |
| `isaAllElim(o, (i => (i => i)))` | 7133 | 75.7% |
| `isaAllElim(o, (i => (i => o)))` | 8027 | 85.2% |
| `isaAllElim(o, (i => i))` | 7693 | 81.7% |
| `isaAllElim(o, (i => o))` | 8423 | 89.4% |
| `isaAllElim(o, (o => (i => (i => i))))` | 5020 | 53.3% |
| `isaAllElim(o, (o => (i => o)))` | 92 | 1.0% |
| `isaAllElim(o, (o => (o => o)))` | 8323 | 88.4% |
| `isaAllElim(o, (o => i))` | 883 | 9.4% |
| `isaAllElim(o, (o => o))` | 8432 | 89.5% |
| `isaAllElim(o, i)` | 8951 | 95.0% |
| `isaAllElim(o, o)` | 8838 | 93.8% |
| `isaAllIntro('a, body: o)` | 7971 | 84.6% |
| `isaAllIntro('b, body: o)` | 2990 | 31.7% |
| `isaAllIntro(('a => 'b), body: o)` | 4626 | 49.1% |
| `isaAllIntro(('a => ('b => o)), body: o)` | 1195 | 12.7% |
| `isaAllIntro(('a => o), body: o)` | 7941 | 84.3% |
| `isaAllIntro(('b => 'a), body: o)` | 439 | 4.7% |
| `isaAllIntro(('b => (('b => 'a) => 'a)), body: o)` | 439 | 4.7% |
| `isaAllIntro((('a => o) => o), body: o)` | 7323 | 77.7% |
| `isaAllIntro(((i => (i => 'a)) => (i => 'a)), body: o)` | 2773 | 29.4% |
| `isaAllIntro(((i => (i => (i => i))) => (i => i)), body: o)` | 4 | 0.0% |
| `isaAllIntro(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), body: o)` | 38 | 0.4% |
| `isaAllIntro(((i => (i => i)) => (i => i)), body: o)` | 2760 | 29.3% |
| `isaAllIntro(((i => i) => ((i => i) => (i => i))), body: o)` | 2421 | 25.7% |
| `isaAllIntro(((i => i) => (i => i)), body: o)` | 514 | 5.5% |
| `isaAllIntro(((i => i) => o), body: o)` | 531 | 5.6% |
| `isaAllIntro(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), body: o)` | 1 | 0.0% |
| `isaAllIntro(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), body: o)` | 1 | 0.0% |
| `isaAllIntro(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), body: o)` | 70 | 0.7% |
| `isaAllIntro(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), body: o)` | 183 | 1.9% |
| `isaAllIntro(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), body: o)` | 318 | 3.4% |
| `isaAllIntro(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), body: o)` | 53 | 0.6% |
| `isaAllIntro(((i => o) => ((i => (i => (i => o))) => (i => o))), body: o)` | 155 | 1.6% |
| `isaAllIntro(((i => o) => ((i => (i => o)) => ((i => i) => o))), body: o)` | 128 | 1.4% |
| `isaAllIntro(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), body: o)` | 243 | 2.6% |
| `isaAllIntro(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), body: o)` | 225 | 2.4% |
| `isaAllIntro(((i => o) => ((i => (i => o)) => (i => o))), body: o)` | 141 | 1.5% |
| `isaAllIntro(((i => o) => ((i => (i => o)) => o)), body: o)` | 585 | 6.2% |
| `isaAllIntro(((i => o) => ((i => o) => ((i => (i => o)) => o))), body: o)` | 429 | 4.6% |
| `isaAllIntro(((i => o) => ((i => o) => o)), body: o)` | 1163 | 12.3% |
| `isaAllIntro(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), body: o)` | 3 | 0.0% |
| `isaAllIntro(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), body: o)` | 44 | 0.5% |
| `isaAllIntro(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), body: o)` | 249 | 2.6% |
| `isaAllIntro(((i => o) => (i => ((i => (i => o)) => (i => o)))), body: o)` | 96 | 1.0% |
| `isaAllIntro(((i => o) => (i => ((i => (i => o)) => o))), body: o)` | 374 | 4.0% |
| `isaAllIntro(((i => o) => (i => ((i => o) => (i => o)))), body: o)` | 46 | 0.5% |
| `isaAllIntro(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), body: o)` | 41 | 0.4% |
| `isaAllIntro(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), body: o)` | 1 | 0.0% |
| `isaAllIntro(((i => o) => (i => (i => (i => (i => (i => o)))))), body: o)` | 89 | 0.9% |
| `isaAllIntro(((i => o) => (i => (i => (i => (i => o))))), body: o)` | 225 | 2.4% |
| `isaAllIntro(((i => o) => (i => (i => (i => o)))), body: o)` | 1026 | 10.9% |
| `isaAllIntro(((i => o) => (i => (i => i))), body: o)` | 44 | 0.5% |
| `isaAllIntro(((i => o) => (i => (i => o))), body: o)` | 946 | 10.0% |
| `isaAllIntro(((i => o) => (i => i)), body: o)` | 438 | 4.6% |
| `isaAllIntro(((i => o) => (i => o)), body: o)` | 827 | 8.8% |
| `isaAllIntro(((i => o) => (o => (i => o))), body: o)` | 92 | 1.0% |
| `isaAllIntro(((i => o) => i), body: o)` | 5274 | 56.0% |
| `isaAllIntro(((i => o) => o), body: o)` | 4185 | 44.4% |
| `isaAllIntro((i => ((i => (i => (i => i))) => i)), body: o)` | 25 | 0.3% |
| `isaAllIntro((i => ((i => (i => i)) => (i => (i => i)))), body: o)` | 53 | 0.6% |
| `isaAllIntro((i => ((i => (i => i)) => (i => i))), body: o)` | 2044 | 21.7% |
| `isaAllIntro((i => ((i => (i => i)) => i)), body: o)` | 3706 | 39.3% |
| `isaAllIntro((i => ((i => (i => o)) => i)), body: o)` | 7313 | 77.6% |
| `isaAllIntro((i => ((i => i) => (i => i))), body: o)` | 3854 | 40.9% |
| `isaAllIntro((i => ((i => i) => i)), body: o)` | 6215 | 66.0% |
| `isaAllIntro((i => ((i => i) => o)), body: o)` | 4841 | 51.4% |
| `isaAllIntro((i => ((i => o) => i)), body: o)` | 7247 | 76.9% |
| `isaAllIntro((i => ((i => o) => o)), body: o)` | 7493 | 79.5% |
| `isaAllIntro((i => (i => 'a)), body: o)` | 2773 | 29.4% |
| `isaAllIntro((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), body: o)` | 8 | 0.1% |
| `isaAllIntro((i => (i => ((i => (i => i)) => (i => o)))), body: o)` | 4068 | 43.2% |
| `isaAllIntro((i => (i => ((i => (i => i)) => i))), body: o)` | 4061 | 43.1% |
| `isaAllIntro((i => (i => ((i => (i => i)) => o))), body: o)` | 439 | 4.7% |
| `isaAllIntro((i => (i => ((i => i) => ((i => i) => (i => o))))), body: o)` | 7 | 0.1% |
| `isaAllIntro((i => (i => (i => ((i => (i => i)) => i)))), body: o)` | 896 | 9.5% |
| `isaAllIntro((i => (i => (i => ((i => i) => o)))), body: o)` | 21 | 0.2% |
| `isaAllIntro((i => (i => (i => (i => (i => (i => i)))))), body: o)` | 35 | 0.4% |
| `isaAllIntro((i => (i => (i => (i => (i => i))))), body: o)` | 340 | 3.6% |
| `isaAllIntro((i => (i => (i => (i => (i => o))))), body: o)` | 10 | 0.1% |
| `isaAllIntro((i => (i => (i => (i => i)))), body: o)` | 1635 | 17.4% |
| `isaAllIntro((i => (i => (i => (i => o)))), body: o)` | 166 | 1.8% |
| `isaAllIntro((i => (i => (i => i))), body: o)` | 3110 | 33.0% |
| `isaAllIntro((i => (i => (i => o))), body: o)` | 958 | 10.2% |
| `isaAllIntro((i => (i => i)), body: o)` | 7012 | 74.4% |
| `isaAllIntro((i => (i => o)), body: o)` | 7514 | 79.8% |
| `isaAllIntro((i => i), body: o)` | 7172 | 76.1% |
| `isaAllIntro((i => o), body: o)` | 7948 | 84.4% |
| `isaAllIntro((o => (i => (i => i))), body: o)` | 5018 | 53.3% |
| `isaAllIntro((o => (o => o)), body: o)` | 7841 | 83.2% |
| `isaAllIntro((o => i), body: o)` | 882 | 9.4% |
| `isaAllIntro((o => o), body: o)` | 7819 | 83.0% |
| `isaAllIntro(dummy, body: o)` | 28 | 0.3% |
| `isaAllIntro(i, body: o)` | 8951 | 95.0% |
| `isaAllIntro(o, body: o)` | 8205 | 87.1% |
| `isaBound('a)` | 9179 | 97.4% |
| `isaBound('b)` | 4636 | 49.2% |
| `isaBound(('a => 'b))` | 4655 | 49.4% |
| `isaBound(('a => ('a => o)))` | 7578 | 80.4% |
| `isaBound(('a => ('b => o)))` | 1195 | 12.7% |
| `isaBound(('a => o))` | 9167 | 97.3% |
| `isaBound(('b => 'a))` | 439 | 4.7% |
| `isaBound(('b => ('b => o)))` | 4626 | 49.1% |
| `isaBound(('b => (('b => 'a) => 'a)))` | 439 | 4.7% |
| `isaBound(('b => o))` | 4634 | 49.2% |
| `isaBound((('a => o) => o))` | 7324 | 77.7% |
| `isaBound((('b => 'a) => 'a))` | 439 | 4.7% |
| `isaBound((('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)))` | 439 | 4.7% |
| `isaBound((('b => (('b => 'a) => 'a)) => o))` | 439 | 4.7% |
| `isaBound(((('a => o) => o) => ((('a => o) => o) => o)))` | 7323 | 77.7% |
| `isaBound(((('a => o) => o) => o))` | 7323 | 77.7% |
| `isaBound((((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)))` | 2773 | 29.4% |
| `isaBound((((i => (i => 'a)) => (i => 'a)) => o))` | 2773 | 29.4% |
| `isaBound((((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)))` | 4 | 0.0% |
| `isaBound((((i => (i => (i => i))) => (i => i)) => o))` | 4 | 0.0% |
| `isaBound((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)))` | 38 | 0.4% |
| `isaBound((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o))` | 38 | 0.4% |
| `isaBound((((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)))` | 2760 | 29.3% |
| `isaBound((((i => (i => i)) => (i => i)) => o))` | 2760 | 29.3% |
| `isaBound((((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)))` | 2421 | 25.7% |
| `isaBound((((i => i) => ((i => i) => (i => i))) => o))` | 2421 | 25.7% |
| `isaBound((((i => i) => (i => i)) => (((i => i) => (i => i)) => o)))` | 514 | 5.5% |
| `isaBound((((i => i) => (i => i)) => o))` | 514 | 5.5% |
| `isaBound((((i => i) => o) => (((i => i) => o) => o)))` | 531 | 5.6% |
| `isaBound((((i => i) => o) => o))` | 531 | 5.6% |
| `isaBound((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)))` | 1 | 0.0% |
| `isaBound((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o))` | 1 | 0.0% |
| `isaBound((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)))` | 1 | 0.0% |
| `isaBound((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o))` | 1 | 0.0% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)))` | 70 | 0.7% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o))` | 70 | 0.7% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)))` | 183 | 1.9% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o))` | 183 | 1.9% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)))` | 318 | 3.4% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o))` | 318 | 3.4% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)))` | 53 | 0.6% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o))` | 53 | 0.6% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)))` | 155 | 1.6% |
| `isaBound((((i => o) => ((i => (i => (i => o))) => (i => o))) => o))` | 155 | 1.6% |
| `isaBound((((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)))` | 128 | 1.4% |
| `isaBound((((i => o) => ((i => (i => o)) => ((i => i) => o))) => o))` | 128 | 1.4% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)))` | 243 | 2.6% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o))` | 243 | 2.6% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)))` | 225 | 2.4% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o))` | 225 | 2.4% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)))` | 141 | 1.5% |
| `isaBound((((i => o) => ((i => (i => o)) => (i => o))) => o))` | 141 | 1.5% |
| `isaBound((((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)))` | 585 | 6.2% |
| `isaBound((((i => o) => ((i => (i => o)) => o)) => o))` | 585 | 6.2% |
| `isaBound((((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)))` | 1163 | 12.3% |
| `isaBound((((i => o) => ((i => o) => o)) => o))` | 1163 | 12.3% |
| `isaBound((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)))` | 3 | 0.0% |
| `isaBound((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o))` | 3 | 0.0% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)))` | 44 | 0.5% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o))` | 44 | 0.5% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)))` | 249 | 2.6% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o))` | 249 | 2.6% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)))` | 96 | 1.0% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => (i => o)))) => o))` | 96 | 1.0% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)))` | 374 | 4.0% |
| `isaBound((((i => o) => (i => ((i => (i => o)) => o))) => o))` | 374 | 4.0% |
| `isaBound((((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)))` | 46 | 0.5% |
| `isaBound((((i => o) => (i => ((i => o) => (i => o)))) => o))` | 46 | 0.5% |
| `isaBound((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)))` | 41 | 0.4% |
| `isaBound((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o))` | 41 | 0.4% |
| `isaBound((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)))` | 1 | 0.0% |
| `isaBound((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o))` | 1 | 0.0% |
| `isaBound((((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)))` | 89 | 0.9% |
| `isaBound((((i => o) => (i => (i => (i => (i => (i => o)))))) => o))` | 89 | 0.9% |
| `isaBound((((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)))` | 117 | 1.2% |
| `isaBound((((i => o) => (i => (i => (i => (i => o))))) => o))` | 117 | 1.2% |
| `isaBound((((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)))` | 1025 | 10.9% |
| `isaBound((((i => o) => (i => (i => (i => o)))) => o))` | 1025 | 10.9% |
| `isaBound((((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)))` | 44 | 0.5% |
| `isaBound((((i => o) => (i => (i => i))) => o))` | 44 | 0.5% |
| `isaBound((((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)))` | 945 | 10.0% |
| `isaBound((((i => o) => (i => (i => o))) => o))` | 945 | 10.0% |
| `isaBound((((i => o) => (i => i)) => (((i => o) => (i => i)) => o)))` | 2 | 0.0% |
| `isaBound((((i => o) => (i => i)) => o))` | 2 | 0.0% |
| `isaBound((((i => o) => (i => o)) => (((i => o) => (i => o)) => o)))` | 670 | 7.1% |
| `isaBound((((i => o) => (i => o)) => o))` | 670 | 7.1% |
| `isaBound((((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)))` | 92 | 1.0% |
| `isaBound((((i => o) => (o => (i => o))) => o))` | 92 | 1.0% |
| `isaBound((((i => o) => i) => (((i => o) => i) => o)))` | 5274 | 56.0% |
| `isaBound((((i => o) => i) => o))` | 5274 | 56.0% |
| `isaBound((((i => o) => o) => (((i => o) => o) => o)))` | 4100 | 43.5% |
| `isaBound((((i => o) => o) => o))` | 4102 | 43.5% |
| `isaBound(((i => 'a) => ((i => 'a) => o)))` | 2739 | 29.1% |
| `isaBound(((i => 'a) => o))` | 2739 | 29.1% |
| `isaBound(((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)))` | 25 | 0.3% |
| `isaBound(((i => ((i => (i => (i => i))) => i)) => o))` | 25 | 0.3% |
| `isaBound(((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)))` | 53 | 0.6% |
| `isaBound(((i => ((i => (i => i)) => (i => (i => i)))) => o))` | 53 | 0.6% |
| `isaBound(((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)))` | 2044 | 21.7% |
| `isaBound(((i => ((i => (i => i)) => (i => i))) => o))` | 2044 | 21.7% |
| `isaBound(((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)))` | 3706 | 39.3% |
| `isaBound(((i => ((i => (i => i)) => i)) => o))` | 3706 | 39.3% |
| `isaBound(((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)))` | 7313 | 77.6% |
| `isaBound(((i => ((i => (i => o)) => i)) => o))` | 7313 | 77.6% |
| `isaBound(((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)))` | 3854 | 40.9% |
| `isaBound(((i => ((i => i) => (i => i))) => o))` | 3854 | 40.9% |
| `isaBound(((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)))` | 6215 | 66.0% |
| `isaBound(((i => ((i => i) => i)) => o))` | 6215 | 66.0% |
| `isaBound(((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)))` | 4841 | 51.4% |
| `isaBound(((i => ((i => i) => o)) => o))` | 4841 | 51.4% |
| `isaBound(((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)))` | 7247 | 76.9% |
| `isaBound(((i => ((i => o) => i)) => o))` | 7247 | 76.9% |
| `isaBound(((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)))` | 7493 | 79.5% |
| `isaBound(((i => ((i => o) => o)) => o))` | 7493 | 79.5% |
| `isaBound(((i => (i => 'a)) => (i => 'a)))` | 2773 | 29.4% |
| `isaBound(((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)))` | 8 | 0.1% |
| `isaBound(((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o))` | 8 | 0.1% |
| `isaBound(((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)))` | 4068 | 43.2% |
| `isaBound(((i => (i => ((i => (i => i)) => (i => o)))) => o))` | 4068 | 43.2% |
| `isaBound(((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)))` | 4061 | 43.1% |
| `isaBound(((i => (i => ((i => (i => i)) => i))) => o))` | 4061 | 43.1% |
| `isaBound(((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)))` | 439 | 4.7% |
| `isaBound(((i => (i => ((i => (i => i)) => o))) => o))` | 439 | 4.7% |
| `isaBound(((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)))` | 7 | 0.1% |
| `isaBound(((i => (i => ((i => i) => ((i => i) => (i => o))))) => o))` | 7 | 0.1% |
| `isaBound(((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)))` | 896 | 9.5% |
| `isaBound(((i => (i => (i => ((i => (i => i)) => i)))) => o))` | 896 | 9.5% |
| `isaBound(((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)))` | 21 | 0.2% |
| `isaBound(((i => (i => (i => ((i => i) => o)))) => o))` | 21 | 0.2% |
| `isaBound(((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)))` | 35 | 0.4% |
| `isaBound(((i => (i => (i => (i => (i => (i => i)))))) => o))` | 35 | 0.4% |
| `isaBound(((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)))` | 187 | 2.0% |
| `isaBound(((i => (i => (i => (i => (i => i))))) => o))` | 187 | 2.0% |
| `isaBound(((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)))` | 9 | 0.1% |
| `isaBound(((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))` | 1 | 0.0% |
| `isaBound(((i => (i => (i => (i => (i => o))))) => o))` | 9 | 0.1% |
| `isaBound(((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)))` | 1108 | 11.8% |
| `isaBound(((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))` | 38 | 0.4% |
| `isaBound(((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))` | 24 | 0.3% |
| `isaBound(((i => (i => (i => (i => i)))) => o))` | 1109 | 11.8% |
| `isaBound(((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)))` | 114 | 1.2% |
| `isaBound(((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))` | 2 | 0.0% |
| `isaBound(((i => (i => (i => (i => o)))) => o))` | 114 | 1.2% |
| `isaBound(((i => (i => (i => i))) => ((i => (i => (i => i))) => o)))` | 3075 | 32.6% |
| `isaBound(((i => (i => (i => i))) => ((i => (i => i)) => (i => i))))` | 10 | 0.1% |
| `isaBound(((i => (i => (i => i))) => (i => (i => i))))` | 103 | 1.1% |
| `isaBound(((i => (i => (i => i))) => (i => i)))` | 1096 | 11.6% |
| `isaBound(((i => (i => (i => i))) => i))` | 25 | 0.3% |
| `isaBound(((i => (i => (i => i))) => o))` | 3077 | 32.7% |
| `isaBound(((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))` | 70 | 0.7% |
| `isaBound(((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))` | 70 | 0.7% |
| `isaBound(((i => (i => (i => o))) => ((i => (i => (i => o))) => o)))` | 284 | 3.0% |
| `isaBound(((i => (i => (i => o))) => ((i => (i => i)) => o)))` | 185 | 2.0% |
| `isaBound(((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))` | 70 | 0.7% |
| `isaBound(((i => (i => (i => o))) => (i => (i => (i => o)))))` | 318 | 3.4% |
| `isaBound(((i => (i => (i => o))) => (i => (i => o))))` | 149 | 1.6% |
| `isaBound(((i => (i => (i => o))) => (i => o)))` | 156 | 1.7% |
| `isaBound(((i => (i => (i => o))) => o))` | 284 | 3.0% |
| `isaBound(((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))` | 38 | 0.4% |
| `isaBound(((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))))` | 24 | 0.3% |
| `isaBound(((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))))` | 10 | 0.1% |
| `isaBound(((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))` | 37 | 0.4% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))))` | 38 | 0.4% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))))` | 24 | 0.3% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))))` | 21 | 0.2% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => (i => i))))` | 23 | 0.2% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => i)))` | 8 | 0.1% |
| `isaBound(((i => (i => i)) => ((i => (i => i)) => o)))` | 6923 | 73.5% |
| `isaBound(((i => (i => i)) => ((i => i) => (i => i))))` | 965 | 10.2% |
| `isaBound(((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))))` | 35 | 0.4% |
| `isaBound(((i => (i => i)) => (i => (i => i))))` | 91 | 1.0% |
| `isaBound(((i => (i => i)) => (i => i)))` | 2884 | 30.6% |
| `isaBound(((i => (i => i)) => (i => o)))` | 4068 | 43.2% |
| `isaBound(((i => (i => i)) => i))` | 4065 | 43.2% |
| `isaBound(((i => (i => i)) => o))` | 6927 | 73.5% |
| `isaBound(((i => (i => o)) => ((i => (i => o)) => o)))` | 7387 | 78.4% |
| `isaBound(((i => (i => o)) => ((i => i) => o)))` | 132 | 1.4% |
| `isaBound(((i => (i => o)) => (i => (i => (i => (i => o))))))` | 243 | 2.6% |
| `isaBound(((i => (i => o)) => (i => (i => (i => o)))))` | 225 | 2.4% |
| `isaBound(((i => (i => o)) => (i => (i => o))))` | 250 | 2.7% |
| `isaBound(((i => (i => o)) => (i => o)))` | 344 | 3.7% |
| `isaBound(((i => (i => o)) => i))` | 7313 | 77.6% |
| `isaBound(((i => (i => o)) => o))` | 7404 | 78.6% |
| `isaBound(((i => i) => ((i => (i => (i => i))) => (i => i))))` | 92 | 1.0% |
| `isaBound(((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))))` | 23 | 0.2% |
| `isaBound(((i => i) => ((i => i) => (i => i))))` | 2421 | 25.7% |
| `isaBound(((i => i) => ((i => i) => (i => o))))` | 7 | 0.1% |
| `isaBound(((i => i) => ((i => i) => o)))` | 6847 | 72.7% |
| `isaBound(((i => i) => (i => (i => i))))` | 442 | 4.7% |
| `isaBound(((i => i) => (i => i)))` | 4223 | 44.8% |
| `isaBound(((i => i) => (i => o)))` | 7 | 0.1% |
| `isaBound(((i => i) => i))` | 6229 | 66.1% |
| `isaBound(((i => i) => o))` | 6955 | 73.8% |
| `isaBound(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))))` | 1 | 0.0% |
| `isaBound(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))` | 1 | 0.0% |
| `isaBound(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))))` | 70 | 0.7% |
| `isaBound(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))))` | 183 | 1.9% |
| `isaBound(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))))` | 318 | 3.4% |
| `isaBound(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))))` | 53 | 0.6% |
| `isaBound(((i => o) => ((i => (i => (i => o))) => (i => o))))` | 155 | 1.6% |
| `isaBound(((i => o) => ((i => (i => o)) => ((i => i) => o))))` | 128 | 1.4% |
| `isaBound(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))))` | 243 | 2.6% |
| `isaBound(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))))` | 225 | 2.4% |
| `isaBound(((i => o) => ((i => (i => o)) => (i => o))))` | 141 | 1.5% |
| `isaBound(((i => o) => ((i => (i => o)) => o)))` | 597 | 6.3% |
| `isaBound(((i => o) => ((i => o) => ((i => (i => o)) => o))))` | 429 | 4.6% |
| `isaBound(((i => o) => ((i => o) => o)))` | 5453 | 57.9% |
| `isaBound(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))))` | 3 | 0.0% |
| `isaBound(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))))` | 44 | 0.5% |
| `isaBound(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))))` | 249 | 2.6% |
| `isaBound(((i => o) => (i => ((i => (i => o)) => (i => o)))))` | 96 | 1.0% |
| `isaBound(((i => o) => (i => ((i => (i => o)) => o))))` | 374 | 4.0% |
| `isaBound(((i => o) => (i => ((i => o) => (i => o)))))` | 46 | 0.5% |
| `isaBound(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))))` | 41 | 0.4% |
| `isaBound(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))))` | 1 | 0.0% |
| `isaBound(((i => o) => (i => (i => (i => (i => (i => o)))))))` | 89 | 0.9% |
| `isaBound(((i => o) => (i => (i => (i => (i => o))))))` | 225 | 2.4% |
| `isaBound(((i => o) => (i => (i => (i => o)))))` | 1026 | 10.9% |
| `isaBound(((i => o) => (i => (i => i))))` | 44 | 0.5% |
| `isaBound(((i => o) => (i => (i => o))))` | 946 | 10.0% |
| `isaBound(((i => o) => (i => i)))` | 445 | 4.7% |
| `isaBound(((i => o) => (i => o)))` | 838 | 8.9% |
| `isaBound(((i => o) => (o => (i => o))))` | 92 | 1.0% |
| `isaBound(((i => o) => i))` | 7257 | 77.0% |
| `isaBound(((i => o) => o))` | 7746 | 82.2% |
| `isaBound(((o => (i => (i => i))) => ((o => (i => (i => i))) => o)))` | 5018 | 53.3% |
| `isaBound(((o => (i => (i => i))) => o))` | 5018 | 53.3% |
| `isaBound(((o => (o => o)) => ((o => (o => o)) => o)))` | 7841 | 83.2% |
| `isaBound(((o => (o => o)) => o))` | 7841 | 83.2% |
| `isaBound(((o => i) => ((o => i) => o)))` | 882 | 9.4% |
| `isaBound(((o => i) => o))` | 882 | 9.4% |
| `isaBound(((o => o) => ((o => o) => o)))` | 7819 | 83.0% |
| `isaBound(((o => o) => o))` | 7819 | 83.0% |
| `isaBound((i => 'a))` | 2773 | 29.4% |
| `isaBound((i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))` | 1 | 0.0% |
| `isaBound((i => ((i => (i => (i => i))) => i)))` | 25 | 0.3% |
| `isaBound((i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))` | 41 | 0.4% |
| `isaBound((i => ((i => (i => (i => o))) => (i => (i => o)))))` | 3 | 0.0% |
| `isaBound((i => ((i => (i => i)) => ((i => (i => i)) => i))))` | 8 | 0.1% |
| `isaBound((i => ((i => (i => i)) => (i => (i => i)))))` | 53 | 0.6% |
| `isaBound((i => ((i => (i => i)) => (i => i))))` | 2100 | 22.3% |
| `isaBound((i => ((i => (i => i)) => (i => o))))` | 4068 | 43.2% |
| `isaBound((i => ((i => (i => i)) => i)))` | 4064 | 43.1% |
| `isaBound((i => ((i => (i => i)) => o)))` | 439 | 4.7% |
| `isaBound((i => ((i => (i => o)) => ((i => i) => o))))` | 44 | 0.5% |
| `isaBound((i => ((i => (i => o)) => (i => (i => o)))))` | 249 | 2.6% |
| `isaBound((i => ((i => (i => o)) => (i => o))))` | 96 | 1.0% |
| `isaBound((i => ((i => (i => o)) => i)))` | 7313 | 77.6% |
| `isaBound((i => ((i => (i => o)) => o)))` | 374 | 4.0% |
| `isaBound((i => ((i => i) => ((i => i) => (i => o)))))` | 7 | 0.1% |
| `isaBound((i => ((i => i) => (i => i))))` | 3854 | 40.9% |
| `isaBound((i => ((i => i) => i)))` | 6226 | 66.1% |
| `isaBound((i => ((i => i) => o)))` | 4845 | 51.4% |
| `isaBound((i => ((i => o) => (i => o))))` | 46 | 0.5% |
| `isaBound((i => ((i => o) => i)))` | 7247 | 76.9% |
| `isaBound((i => ((i => o) => o)))` | 7494 | 79.6% |
| `isaBound((i => (i => 'a)))` | 3297 | 35.0% |
| `isaBound((i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))` | 1 | 0.0% |
| `isaBound((i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))` | 41 | 0.4% |
| `isaBound((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))))` | 8 | 0.1% |
| `isaBound((i => (i => ((i => (i => i)) => (i => i)))))` | 13 | 0.1% |
| `isaBound((i => (i => ((i => (i => i)) => (i => o)))))` | 4068 | 43.2% |
| `isaBound((i => (i => ((i => (i => i)) => i))))` | 4062 | 43.1% |
| `isaBound((i => (i => ((i => (i => i)) => o))))` | 439 | 4.7% |
| `isaBound((i => (i => ((i => i) => ((i => i) => (i => o))))))` | 7 | 0.1% |
| `isaBound((i => (i => ((i => i) => o))))` | 21 | 0.2% |
| `isaBound((i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))` | 1 | 0.0% |
| `isaBound((i => (i => (i => ((i => (i => i)) => i)))))` | 896 | 9.5% |
| `isaBound((i => (i => (i => ((i => i) => o)))))` | 21 | 0.2% |
| `isaBound((i => (i => (i => (i => (i => (i => i)))))))` | 35 | 0.4% |
| `isaBound((i => (i => (i => (i => (i => i))))))` | 471 | 5.0% |
| `isaBound((i => (i => (i => (i => (i => o))))))` | 99 | 1.1% |
| `isaBound((i => (i => (i => (i => i)))))` | 1859 | 19.7% |
| `isaBound((i => (i => (i => (i => o)))))` | 435 | 4.6% |
| `isaBound((i => (i => (i => i))))` | 3582 | 38.0% |
| `isaBound((i => (i => (i => o))))` | 1561 | 16.6% |
| `isaBound((i => (i => i)))` | 7705 | 81.8% |
| `isaBound((i => (i => o)))` | 9170 | 97.3% |
| `isaBound((i => i))` | 8258 | 87.7% |
| `isaBound((i => o))` | 8838 | 93.8% |
| `isaBound((o => (i => (i => i))))` | 5020 | 53.3% |
| `isaBound((o => (i => o)))` | 92 | 1.0% |
| `isaBound((o => (o => o)))` | 8323 | 88.4% |
| `isaBound((o => i))` | 883 | 9.4% |
| `isaBound((o => o))` | 8432 | 89.5% |
| `isaBound(i)` | 9352 | 99.3% |
| `isaBound(o)` | 9034 | 95.9% |
| `isaConst(declared, (i => (i => i)), args: [i, i])` | 25 | 0.3% |
| `isaConst(declared, (i => (i => o)), args: [i, i])` | 50 | 0.5% |
| `isaConst(declared, (i => i), args: [i])` | 6 | 0.1% |
| `isaConst(declared, i, args: [])` | 275 | 2.9% |
| `isaConst(defined fol, ('a => ('a => o)), args: ['a, 'a])` | 105 | 1.1% |
| `isaConst(defined fol, (('a => o) => o), args: [('a => o)])` | 3947 | 41.9% |
| `isaConst(defined fol, ((i => o) => o), args: [(i => o)])` | 3947 | 41.9% |
| `isaConst(defined fol, (i => (i => o)), args: [i, i])` | 105 | 1.1% |
| `isaConst(defined fol, (o => (o => o)), args: [o, o])` | 4022 | 42.7% |
| `isaConst(defined ifol, ('a => (('a => 'b) => 'b)), args: ['a, ('a => 'b)])` | 508 | 5.4% |
| `isaConst(defined ifol, ('b => (('b => 'a) => 'a)), args: ['b, ('b => 'a)])` | 439 | 4.7% |
| `isaConst(defined ifol, (('a => o) => o), args: [('a => o)])` | 8959 | 95.1% |
| `isaConst(defined ifol, ((i => o) => o), args: [(i => o)])` | 8958 | 95.1% |
| `isaConst(defined ifol, (i => ((i => i) => i)), args: [i, (i => i)])` | 508 | 5.4% |
| `isaConst(defined ifol, (o => (o => o)), args: [o, o])` | 8099 | 86.0% |
| `isaConst(defined ifol, (o => o), args: [o])` | 8473 | 89.9% |
| `isaConst(defined ifol, o, args: [])` | 7619 | 80.9% |
| `isaConst(defined pure, ('a => o), args: ['a])` | 28 | 0.3% |
| `isaConst(defined pure, (i => o), args: [i])` | 28 | 0.3% |
| `isaConst(defined pure, (o => (o => o)), args: [o, o])` | 7700 | 81.7% |
| `isaConst(defined pure, (o => o), args: [o])` | 8174 | 86.8% |
| `isaConst(defined zf, (('a => o) => o), args: [('a => o)])` | 439 | 4.7% |
| `isaConst(defined zf, (((i => o) => o) => o), args: [((i => o) => o)])` | 436 | 4.6% |
| `isaConst(defined zf, ((i => (i => 'a)) => (i => 'a)), args: [(i => (i => 'a)), i])` | 3297 | 35.0% |
| `isaConst(defined zf, ((i => (i => (i => i))) => (i => ((i => (i => (i => (i => i)))) => (i => i)))), args: [(i => (i => (i => i))), i, (i => (i => (i => (i => i)))), i])` | 41 | 0.4% |
| `isaConst(defined zf, ((i => (i => (i => i))) => (i => (i => i))), args: [(i => (i => (i => i))), i, i])` | 146 | 1.5% |
| `isaConst(defined zf, ((i => (i => (i => i))) => (i => i)), args: [(i => (i => (i => i))), i])` | 5 | 0.1% |
| `isaConst(defined zf, ((i => (i => (i => o))) => (i => (i => o))), args: [(i => (i => (i => o))), i, i])` | 108 | 1.1% |
| `isaConst(defined zf, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), args: [(i => (i => i)), (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i, i])` | 55 | 0.6% |
| `isaConst(defined zf, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))), args: [(i => (i => i)), (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i])` | 1058 | 11.2% |
| `isaConst(defined zf, ((i => (i => i)) => ((i => (i => i)) => ((i => (i => i)) => ((i => i) => (i => i))))), args: [(i => (i => i)), (i => (i => i)), (i => (i => i)), (i => i), i])` | 1070 | 11.4% |
| `isaConst(defined zf, ((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))), args: [(i => (i => i)), i, (i => (i => i)), i])` | 49 | 0.5% |
| `isaConst(defined zf, ((i => (i => i)) => (i => i)), args: [(i => (i => i)), i])` | 3857 | 40.9% |
| `isaConst(defined zf, ((i => (i => o)) => (i => o)), args: [(i => (i => o)), i])` | 849 | 9.0% |
| `isaConst(defined zf, ((i => i) => ((i => (i => (i => (i => i)))) => (i => i))), args: [(i => i), (i => (i => (i => (i => i)))), i])` | 5 | 0.1% |
| `isaConst(defined zf, ((i => i) => ((i => (i => (i => i))) => ((i => i) => (i => i)))), args: [(i => i), (i => (i => (i => i))), (i => i), i])` | 65 | 0.7% |
| `isaConst(defined zf, ((i => i) => ((i => (i => i)) => ((i => (i => (i => (i => (i => i))))) => (i => i)))), args: [(i => i), (i => (i => i)), (i => (i => (i => (i => (i => i))))), i])` | 207 | 2.2% |
| `isaConst(defined zf, ((i => i) => ((i => (i => i)) => (i => i))), args: [(i => i), (i => (i => i)), i])` | 11 | 0.1% |
| `isaConst(defined zf, ((i => i) => ((i => i) => ((i => (i => (i => i))) => ((i => (i => (i => (i => (i => i))))) => (i => i))))), args: [(i => i), (i => i), (i => (i => (i => i))), (i => (i => (i => (i => (i => i))))), i])` | 39 | 0.4% |
| `isaConst(defined zf, ((i => i) => ((i => i) => ((i => (i => (i => i))) => ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => (i => i)))))), args: [(i => i), (i => i), (i => (i => (i => i))), (i => (i => (i => (i => i)))), (i => (i => (i => (i => i)))), i])` | 11 | 0.1% |
| `isaConst(defined zf, ((i => i) => ((i => i) => ((i => (i => (i => i))) => (i => i)))), args: [(i => i), (i => i), (i => (i => (i => i))), i])` | 215 | 2.3% |
| `isaConst(defined zf, ((i => i) => ((i => i) => ((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))))), args: [(i => i), (i => i), (i => (i => i)), (i => (i => (i => i))), (i => (i => i)), i])` | 23 | 0.2% |
| `isaConst(defined zf, ((i => i) => ((i => i) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))), args: [(i => i), (i => i), (i => (i => i)), (i => (i => (i => i))), i])` | 49 | 0.5% |
| `isaConst(defined zf, ((i => i) => ((i => i) => (i => i))), args: [(i => i), (i => i), i])` | 2872 | 30.5% |
| `isaConst(defined zf, ((i => i) => ((i => o) => ((i => (i => o)) => ((i => o) => o)))), args: [(i => i), (i => o), (i => (i => o)), (i => o)])` | 436 | 4.6% |
| `isaConst(defined zf, ((i => i) => (i => (i => i))), args: [(i => i), i, i])` | 692 | 7.3% |
| `isaConst(defined zf, ((i => i) => (i => i)), args: [(i => i), i])` | 641 | 6.8% |
| `isaConst(defined zf, ((i => i) => o), args: [(i => i)])` | 557 | 5.9% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), args: [(i => o), (i => (i => (i => (i => (i => o))))), (i => (i => (i => (i => i))))])` | 1 | 0.0% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), args: [(i => o), (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), args: [(i => o), (i => (i => (i => o))), (i => (i => (i => o))), (i => (i => (i => o))), (i => (i => o)), i, i])` | 136 | 1.4% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), args: [(i => o), (i => (i => (i => o))), (i => (i => i))])` | 183 | 1.9% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), args: [(i => o), (i => (i => (i => o))), i, i, i])` | 441 | 4.7% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), args: [(i => o), (i => (i => (i => o))), i, i])` | 75 | 0.8% |
| `isaConst(defined zf, ((i => o) => ((i => (i => (i => o))) => (i => o))), args: [(i => o), (i => (i => (i => o))), i])` | 222 | 2.4% |
| `isaConst(defined zf, ((i => o) => ((i => (i => i)) => ((i => (i => (i => o))) => ((i => (i => i)) => ((i => (i => (i => o))) => ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => o)))) => ((i => (i => i)) => ((i => (i => (i => o))) => o))))))))), args: [(i => o), (i => (i => i)), (i => (i => (i => o))), (i => (i => i)), (i => (i => (i => o))), (i => (i => (i => (i => i)))), (i => (i => (i => (i => o)))), (i => (i => i)), (i => (i => (i => o)))])` | 50 | 0.5% |
| `isaConst(defined zf, ((i => o) => ((i => (i => o)) => ((i => i) => o))), args: [(i => o), (i => (i => o)), (i => i)])` | 128 | 1.4% |
| `isaConst(defined zf, ((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), args: [(i => o), (i => (i => o)), i, i, i, i])` | 341 | 3.6% |
| `isaConst(defined zf, ((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), args: [(i => o), (i => (i => o)), i, i, i])` | 323 | 3.4% |
| `isaConst(defined zf, ((i => o) => ((i => (i => o)) => (i => o))), args: [(i => o), (i => (i => o)), i])` | 201 | 2.1% |
| `isaConst(defined zf, ((i => o) => ((i => (i => o)) => o)), args: [(i => o), (i => (i => o))])` | 809 | 8.6% |
| `isaConst(defined zf, ((i => o) => ((i => o) => o)), args: [(i => o), (i => o)])` | 1427 | 15.1% |
| `isaConst(defined zf, ((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), args: [(i => o), i, (i => (i => (i => o))), i, i])` | 3 | 0.0% |
| `isaConst(defined zf, ((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), args: [(i => o), i, (i => (i => o)), (i => i)])` | 63 | 0.7% |
| `isaConst(defined zf, ((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), args: [(i => o), i, (i => (i => o)), i, i])` | 348 | 3.7% |
| `isaConst(defined zf, ((i => o) => (i => ((i => (i => o)) => (i => o)))), args: [(i => o), i, (i => (i => o)), i])` | 162 | 1.7% |
| `isaConst(defined zf, ((i => o) => (i => ((i => (i => o)) => o))), args: [(i => o), i, (i => (i => o))])` | 599 | 6.4% |
| `isaConst(defined zf, ((i => o) => (i => ((i => o) => (i => o)))), args: [(i => o), i, (i => o), i])` | 65 | 0.7% |
| `isaConst(defined zf, ((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), args: [(i => o), i, i, (i => (i => (i => o))), (i => (i => i))])` | 60 | 0.6% |
| `isaConst(defined zf, ((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), args: [(i => o), i, i, i, (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaConst(defined zf, ((i => o) => (i => (i => (i => (i => (i => o)))))), args: [(i => o), i, i, i, i, i])` | 186 | 2.0% |
| `isaConst(defined zf, ((i => o) => (i => (i => (i => (i => o))))), args: [(i => o), i, i, i, i])` | 199 | 2.1% |
| `isaConst(defined zf, ((i => o) => (i => (i => (i => o)))), args: [(i => o), i, i, i])` | 1248 | 13.2% |
| `isaConst(defined zf, ((i => o) => (i => (i => i))), args: [(i => o), i, i])` | 44 | 0.5% |
| `isaConst(defined zf, ((i => o) => (i => (i => o))), args: [(i => o), i, i])` | 1169 | 12.4% |
| `isaConst(defined zf, ((i => o) => (i => i)), args: [(i => o), i])` | 22 | 0.2% |
| `isaConst(defined zf, ((i => o) => (i => o)), args: [(i => o), i])` | 851 | 9.0% |
| `isaConst(defined zf, ((i => o) => (o => (i => o))), args: [(i => o), o, i])` | 132 | 1.4% |
| `isaConst(defined zf, ((i => o) => i), args: [(i => o)])` | 6527 | 69.3% |
| `isaConst(defined zf, ((i => o) => o), args: [(i => o)])` | 1071 | 11.4% |
| `isaConst(defined zf, (i => ((i => (i => (i => (i => (i => i))))) => (i => i))), args: [i, (i => (i => (i => (i => (i => i))))), i])` | 26 | 0.3% |
| `isaConst(defined zf, (i => ((i => (i => (i => (i => i)))) => (i => i))), args: [i, (i => (i => (i => (i => i)))), i])` | 64 | 0.7% |
| `isaConst(defined zf, (i => ((i => (i => (i => i))) => (i => i))), args: [i, (i => (i => (i => i))), i])` | 1436 | 15.2% |
| `isaConst(defined zf, (i => ((i => (i => (i => i))) => i)), args: [i, (i => (i => (i => i)))])` | 30 | 0.3% |
| `isaConst(defined zf, (i => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => (i => i))) => ((i => (i => (i => (i => (i => i))))) => (i => i)))))), args: [i, (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => (i => i))), (i => (i => (i => (i => (i => i))))), i])` | 23 | 0.2% |
| `isaConst(defined zf, (i => ((i => (i => i)) => ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))))), args: [i, (i => (i => i)), (i => (i => i)), (i => (i => i)), (i => (i => (i => i))), i])` | 35 | 0.4% |
| `isaConst(defined zf, (i => ((i => (i => i)) => ((i => i) => (i => i)))), args: [i, (i => (i => i)), (i => i), i])` | 7 | 0.1% |
| `isaConst(defined zf, (i => ((i => (i => i)) => (i => (i => i)))), args: [i, (i => (i => i)), i, i])` | 55 | 0.6% |
| `isaConst(defined zf, (i => ((i => (i => i)) => (i => i))), args: [i, (i => (i => i)), i])` | 2961 | 31.4% |
| `isaConst(defined zf, (i => ((i => (i => i)) => i)), args: [i, (i => (i => i))])` | 4630 | 49.2% |
| `isaConst(defined zf, (i => ((i => (i => o)) => i)), args: [i, (i => (i => o))])` | 8957 | 95.1% |
| `isaConst(defined zf, (i => ((i => i) => ((i => (i => (i => (i => i)))) => (i => i)))), args: [i, (i => i), (i => (i => (i => (i => i)))), i])` | 31 | 0.3% |
| `isaConst(defined zf, (i => ((i => i) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => (i => i))))), args: [i, (i => i), (i => (i => i)), (i => (i => (i => (i => i)))), i])` | 9 | 0.1% |
| `isaConst(defined zf, (i => ((i => i) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))), args: [i, (i => i), (i => (i => i)), (i => (i => (i => i))), i])` | 19 | 0.2% |
| `isaConst(defined zf, (i => ((i => i) => ((i => (i => i)) => (i => i)))), args: [i, (i => i), (i => (i => i)), i])` | 39 | 0.4% |
| `isaConst(defined zf, (i => ((i => i) => ((i => i) => (i => i)))), args: [i, (i => i), (i => i), i])` | 15 | 0.2% |
| `isaConst(defined zf, (i => ((i => i) => (i => i))), args: [i, (i => i), i])` | 4781 | 50.8% |
| `isaConst(defined zf, (i => ((i => i) => i)), args: [i, (i => i)])` | 7209 | 76.5% |
| `isaConst(defined zf, (i => ((i => i) => o)), args: [i, (i => i)])` | 4842 | 51.4% |
| `isaConst(defined zf, (i => ((i => o) => i)), args: [i, (i => o)])` | 8137 | 86.4% |
| `isaConst(defined zf, (i => ((i => o) => o)), args: [i, (i => o)])` | 8395 | 89.1% |
| `isaConst(defined zf, (i => (i => ((i => (i => (i => (i => i)))) => (i => i)))), args: [i, i, (i => (i => (i => (i => i)))), i])` | 7 | 0.1% |
| `isaConst(defined zf, (i => (i => ((i => (i => (i => i))) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => (i => i))))))), args: [i, i, (i => (i => (i => i))), (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => (i => (i => i)))), i])` | 36 | 0.4% |
| `isaConst(defined zf, (i => (i => ((i => (i => (i => i))) => ((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i))))))), args: [i, i, (i => (i => (i => i))), (i => i), (i => (i => i)), (i => (i => i)), i])` | 50 | 0.5% |
| `isaConst(defined zf, (i => (i => ((i => (i => (i => i))) => (i => i)))), args: [i, i, (i => (i => (i => i))), i])` | 475 | 5.0% |
| `isaConst(defined zf, (i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), args: [i, i, (i => (i => i)), (i => (i => i))])` | 9 | 0.1% |
| `isaConst(defined zf, (i => (i => ((i => (i => i)) => (i => i)))), args: [i, i, (i => (i => i)), i])` | 529 | 5.6% |
| `isaConst(defined zf, (i => (i => ((i => (i => i)) => (i => o)))), args: [i, i, (i => (i => i)), i])` | 5033 | 53.4% |
| `isaConst(defined zf, (i => (i => ((i => (i => i)) => i))), args: [i, i, (i => (i => i))])` | 5018 | 53.3% |
| `isaConst(defined zf, (i => (i => ((i => (i => i)) => o))), args: [i, i, (i => (i => i))])` | 439 | 4.7% |
| `isaConst(defined zf, (i => (i => ((i => i) => ((i => i) => (i => o))))), args: [i, i, (i => i), (i => i), i])` | 7 | 0.1% |
| `isaConst(defined zf, (i => (i => (i => ((i => (i => i)) => i)))), args: [i, i, i, (i => (i => i))])` | 947 | 10.1% |
| `isaConst(defined zf, (i => (i => (i => ((i => (i => i)) => o)))), args: [i, i, i, (i => (i => i))])` | 57 | 0.6% |
| `isaConst(defined zf, (i => (i => (i => ((i => i) => o)))), args: [i, i, i, (i => i)])` | 21 | 0.2% |
| `isaConst(defined zf, (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i])` | 122 | 1.3% |
| `isaConst(defined zf, (i => (i => (i => (i => (i => (i => i)))))), args: [i, i, i, i, i, i])` | 39 | 0.4% |
| `isaConst(defined zf, (i => (i => (i => (i => (i => (i => o)))))), args: [i, i, i, i, i, i])` | 52 | 0.6% |
| `isaConst(defined zf, (i => (i => (i => (i => (i => i))))), args: [i, i, i, i, i])` | 210 | 2.2% |
| `isaConst(defined zf, (i => (i => (i => (i => (i => o))))), args: [i, i, i, i, i])` | 14 | 0.1% |
| `isaConst(defined zf, (i => (i => (i => (i => i)))), args: [i, i, i, i])` | 1164 | 12.4% |
| `isaConst(defined zf, (i => (i => (i => (i => o)))), args: [i, i, i, i])` | 177 | 1.9% |
| `isaConst(defined zf, (i => (i => (i => i))), args: [i, i, i])` | 4125 | 43.8% |
| `isaConst(defined zf, (i => (i => (i => o))), args: [i, i, i])` | 372 | 3.9% |
| `isaConst(defined zf, (i => (i => i)), args: [i, i])` | 8785 | 93.3% |
| `isaConst(defined zf, (i => (i => o)), args: [i, i])` | 8196 | 87.0% |
| `isaConst(defined zf, (i => i), args: [i])` | 8467 | 89.9% |
| `isaConst(defined zf, (i => o), args: [i])` | 6111 | 64.9% |
| `isaConst(defined zf, (o => (i => (i => i))), args: [o, i, i])` | 5590 | 59.3% |
| `isaConst(defined zf, (o => i), args: [o])` | 983 | 10.4% |
| `isaConst(defined zf, i, args: [])` | 5761 | 61.2% |
| `isaConst(defined zf, o, args: [])` | 90 | 1.0% |
| `isaConst(primitive IFOL.eq, ('a => ('a => o)), args: ['a, 'a])` | 9096 | 96.6% |
| `isaConst(primitive IFOL.eq, ('b => ('b => o)), args: ['b, 'b])` | 4626 | 49.1% |
| `isaConst(primitive IFOL.eq, (i => (i => o)), args: [i, i])` | 9284 | 98.6% |
| `isaConst(primitive Pure.eq, ('a => ('a => o)), args: ['a, 'a])` | 7752 | 82.3% |
| `isaConst(primitive Pure.eq, ('b => ('b => o)), args: ['b, 'b])` | 4628 | 49.1% |
| `isaConst(primitive Pure.eq, (('a => 'b) => (('a => 'b) => o)), args: [('a => 'b), ('a => 'b)])` | 4626 | 49.1% |
| `isaConst(primitive Pure.eq, (('a => ('a => o)) => (('a => ('a => o)) => o)), args: [('a => ('a => o)), ('a => ('a => o))])` | 7578 | 80.4% |
| `isaConst(primitive Pure.eq, (('a => (('a => 'b) => 'b)) => (('a => (('a => 'b) => 'b)) => o)), args: [('a => (('a => 'b) => 'b)), ('a => (('a => 'b) => 'b))])` | 508 | 5.4% |
| `isaConst(primitive Pure.eq, (('a => o) => (('a => o) => o)), args: [('a => o), ('a => o)])` | 7729 | 82.0% |
| `isaConst(primitive Pure.eq, (('b => 'a) => (('b => 'a) => o)), args: [('b => 'a), ('b => 'a)])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, (('b => ('b => o)) => (('b => ('b => o)) => o)), args: [('b => ('b => o)), ('b => ('b => o))])` | 4626 | 49.1% |
| `isaConst(primitive Pure.eq, (('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)), args: [('b => (('b => 'a) => 'a)), ('b => (('b => 'a) => 'a))])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, (('b => o) => (('b => o) => o)), args: [('b => o), ('b => o)])` | 4626 | 49.1% |
| `isaConst(primitive Pure.eq, ((('a => o) => o) => ((('a => o) => o) => o)), args: [(('a => o) => o), (('a => o) => o)])` | 8963 | 95.1% |
| `isaConst(primitive Pure.eq, ((('b => 'a) => 'a) => ((('b => 'a) => 'a) => o)), args: [(('b => 'a) => 'a), (('b => 'a) => 'a)])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, ((('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)) => ((('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)) => o)), args: [(('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)), (('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o))])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, ((('b => (('b => 'a) => 'a)) => o) => ((('b => (('b => 'a) => 'a)) => o) => o)), args: [(('b => (('b => 'a) => 'a)) => o), (('b => (('b => 'a) => 'a)) => o)])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, (((('a => o) => o) => ((('a => o) => o) => o)) => (((('a => o) => o) => ((('a => o) => o) => o)) => o)), args: [((('a => o) => o) => ((('a => o) => o) => o)), ((('a => o) => o) => ((('a => o) => o) => o))])` | 7323 | 77.7% |
| `isaConst(primitive Pure.eq, (((('a => o) => o) => o) => (((('a => o) => o) => o) => o)), args: [((('a => o) => o) => o), ((('a => o) => o) => o)])` | 7323 | 77.7% |
| `isaConst(primitive Pure.eq, ((((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)) => ((((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)) => o)), args: [(((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)), (((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o))])` | 2773 | 29.4% |
| `isaConst(primitive Pure.eq, ((((i => (i => 'a)) => (i => 'a)) => o) => ((((i => (i => 'a)) => (i => 'a)) => o) => o)), args: [(((i => (i => 'a)) => (i => 'a)) => o), (((i => (i => 'a)) => (i => 'a)) => o)])` | 2773 | 29.4% |
| `isaConst(primitive Pure.eq, ((((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)) => ((((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)) => o)), args: [(((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)), (((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o))])` | 4 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => (i => (i => i))) => (i => i)) => o) => ((((i => (i => (i => i))) => (i => i)) => o) => o)), args: [(((i => (i => (i => i))) => (i => i)) => o), (((i => (i => (i => i))) => (i => i)) => o)])` | 4 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)) => ((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)) => o)), args: [(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)), (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o))])` | 38 | 0.4% |
| `isaConst(primitive Pure.eq, ((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o) => ((((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o) => o)), args: [(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o), (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)])` | 38 | 0.4% |
| `isaConst(primitive Pure.eq, ((((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)) => ((((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)) => o)), args: [(((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)), (((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o))])` | 2760 | 29.3% |
| `isaConst(primitive Pure.eq, ((((i => (i => i)) => (i => i)) => o) => ((((i => (i => i)) => (i => i)) => o) => o)), args: [(((i => (i => i)) => (i => i)) => o), (((i => (i => i)) => (i => i)) => o)])` | 2760 | 29.3% |
| `isaConst(primitive Pure.eq, ((((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)) => ((((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)) => o)), args: [(((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)), (((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o))])` | 2421 | 25.7% |
| `isaConst(primitive Pure.eq, ((((i => i) => ((i => i) => (i => i))) => o) => ((((i => i) => ((i => i) => (i => i))) => o) => o)), args: [(((i => i) => ((i => i) => (i => i))) => o), (((i => i) => ((i => i) => (i => i))) => o)])` | 2421 | 25.7% |
| `isaConst(primitive Pure.eq, ((((i => i) => (i => i)) => (((i => i) => (i => i)) => o)) => ((((i => i) => (i => i)) => (((i => i) => (i => i)) => o)) => o)), args: [(((i => i) => (i => i)) => (((i => i) => (i => i)) => o)), (((i => i) => (i => i)) => (((i => i) => (i => i)) => o))])` | 514 | 5.5% |
| `isaConst(primitive Pure.eq, ((((i => i) => (i => i)) => o) => ((((i => i) => (i => i)) => o) => o)), args: [(((i => i) => (i => i)) => o), (((i => i) => (i => i)) => o)])` | 514 | 5.5% |
| `isaConst(primitive Pure.eq, ((((i => i) => o) => (((i => i) => o) => o)) => ((((i => i) => o) => (((i => i) => o) => o)) => o)), args: [(((i => i) => o) => (((i => i) => o) => o)), (((i => i) => o) => (((i => i) => o) => o))])` | 531 | 5.6% |
| `isaConst(primitive Pure.eq, ((((i => i) => o) => o) => ((((i => i) => o) => o) => o)), args: [(((i => i) => o) => o), (((i => i) => o) => o)])` | 531 | 5.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)) => ((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)), (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o) => ((((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o) => o)), args: [(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o), (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)) => ((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)), (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o) => ((((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o) => o)), args: [(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o), (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)) => ((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)), (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o))])` | 70 | 0.7% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o) => ((((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o) => o)), args: [(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o), (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)])` | 70 | 0.7% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)) => ((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)), (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o))])` | 183 | 1.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o) => ((((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o) => o)), args: [(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o), (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)])` | 183 | 1.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)) => ((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)), (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o))])` | 318 | 3.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o) => ((((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o), (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)])` | 318 | 3.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)) => ((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)), (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o))])` | 53 | 0.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o) => ((((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o), (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)])` | 53 | 0.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)) => ((((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)), (((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o))])` | 155 | 1.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => (i => o))) => (i => o))) => o) => ((((i => o) => ((i => (i => (i => o))) => (i => o))) => o) => o)), args: [(((i => o) => ((i => (i => (i => o))) => (i => o))) => o), (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)])` | 155 | 1.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)) => ((((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)) => o)), args: [(((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)), (((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o))])` | 128 | 1.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => ((i => i) => o))) => o) => ((((i => o) => ((i => (i => o)) => ((i => i) => o))) => o) => o)), args: [(((i => o) => ((i => (i => o)) => ((i => i) => o))) => o), (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)])` | 128 | 1.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)) => ((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)) => o)), args: [(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)), (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o))])` | 243 | 2.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o) => ((((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o) => o)), args: [(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o), (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)])` | 243 | 2.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)) => ((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)) => o)), args: [(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)), (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o))])` | 225 | 2.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o) => ((((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o) => o)), args: [(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o), (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)])` | 225 | 2.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)) => ((((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)) => o)), args: [(((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)), (((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o))])` | 141 | 1.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => (i => o))) => o) => ((((i => o) => ((i => (i => o)) => (i => o))) => o) => o)), args: [(((i => o) => ((i => (i => o)) => (i => o))) => o), (((i => o) => ((i => (i => o)) => (i => o))) => o)])` | 141 | 1.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)) => ((((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)) => o)), args: [(((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)), (((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o))])` | 585 | 6.2% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => (i => o)) => o)) => o) => ((((i => o) => ((i => (i => o)) => o)) => o) => o)), args: [(((i => o) => ((i => (i => o)) => o)) => o), (((i => o) => ((i => (i => o)) => o)) => o)])` | 585 | 6.2% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)) => ((((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)) => o)), args: [(((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)), (((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o))])` | 1163 | 12.3% |
| `isaConst(primitive Pure.eq, ((((i => o) => ((i => o) => o)) => o) => ((((i => o) => ((i => o) => o)) => o) => o)), args: [(((i => o) => ((i => o) => o)) => o), (((i => o) => ((i => o) => o)) => o)])` | 1163 | 12.3% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)) => ((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)) => o)), args: [(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)), (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o))])` | 3 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o) => ((((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o) => o)), args: [(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o), (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)])` | 3 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)) => ((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)) => o)), args: [(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)), (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o))])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o) => ((((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o) => o)), args: [(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o), (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)) => ((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)) => o)), args: [(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)), (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o))])` | 249 | 2.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o) => ((((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o) => o)), args: [(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o), (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)])` | 249 | 2.6% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)) => ((((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)) => o)), args: [(((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)), (((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o))])` | 96 | 1.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => (i => o)))) => o) => ((((i => o) => (i => ((i => (i => o)) => (i => o)))) => o) => o)), args: [(((i => o) => (i => ((i => (i => o)) => (i => o)))) => o), (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)])` | 96 | 1.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)) => ((((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)) => o)), args: [(((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)), (((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o))])` | 374 | 4.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => (i => o)) => o))) => o) => ((((i => o) => (i => ((i => (i => o)) => o))) => o) => o)), args: [(((i => o) => (i => ((i => (i => o)) => o))) => o), (((i => o) => (i => ((i => (i => o)) => o))) => o)])` | 374 | 4.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)) => ((((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)) => o)), args: [(((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)), (((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o))])` | 46 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => ((i => o) => (i => o)))) => o) => ((((i => o) => (i => ((i => o) => (i => o)))) => o) => o)), args: [(((i => o) => (i => ((i => o) => (i => o)))) => o), (((i => o) => (i => ((i => o) => (i => o)))) => o)])` | 46 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)) => ((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)) => o)), args: [(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)), (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o))])` | 41 | 0.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o) => ((((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o) => o)), args: [(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o), (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)])` | 41 | 0.4% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)) => ((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)) => o)), args: [(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)), (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o) => ((((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o) => o)), args: [(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o), (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)) => ((((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)) => o)), args: [(((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)), (((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o))])` | 89 | 0.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => (i => (i => o)))))) => o) => ((((i => o) => (i => (i => (i => (i => (i => o)))))) => o) => o)), args: [(((i => o) => (i => (i => (i => (i => (i => o)))))) => o), (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)])` | 89 | 0.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)) => ((((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)) => o)), args: [(((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)), (((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o))])` | 117 | 1.2% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => (i => o))))) => o) => ((((i => o) => (i => (i => (i => (i => o))))) => o) => o)), args: [(((i => o) => (i => (i => (i => (i => o))))) => o), (((i => o) => (i => (i => (i => (i => o))))) => o)])` | 117 | 1.2% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)) => ((((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)) => o)), args: [(((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)), (((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o))])` | 1025 | 10.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => (i => o)))) => o) => ((((i => o) => (i => (i => (i => o)))) => o) => o)), args: [(((i => o) => (i => (i => (i => o)))) => o), (((i => o) => (i => (i => (i => o)))) => o)])` | 1025 | 10.9% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)) => ((((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)) => o)), args: [(((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)), (((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o))])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => i))) => o) => ((((i => o) => (i => (i => i))) => o) => o)), args: [(((i => o) => (i => (i => i))) => o), (((i => o) => (i => (i => i))) => o)])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)) => ((((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)) => o)), args: [(((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)), (((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o))])` | 945 | 10.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => (i => o))) => o) => ((((i => o) => (i => (i => o))) => o) => o)), args: [(((i => o) => (i => (i => o))) => o), (((i => o) => (i => (i => o))) => o)])` | 945 | 10.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => i)) => (((i => o) => (i => i)) => o)) => ((((i => o) => (i => i)) => (((i => o) => (i => i)) => o)) => o)), args: [(((i => o) => (i => i)) => (((i => o) => (i => i)) => o)), (((i => o) => (i => i)) => (((i => o) => (i => i)) => o))])` | 2 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => i)) => o) => ((((i => o) => (i => i)) => o) => o)), args: [(((i => o) => (i => i)) => o), (((i => o) => (i => i)) => o)])` | 2 | 0.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => o)) => (((i => o) => (i => o)) => o)) => ((((i => o) => (i => o)) => (((i => o) => (i => o)) => o)) => o)), args: [(((i => o) => (i => o)) => (((i => o) => (i => o)) => o)), (((i => o) => (i => o)) => (((i => o) => (i => o)) => o))])` | 670 | 7.1% |
| `isaConst(primitive Pure.eq, ((((i => o) => (i => o)) => o) => ((((i => o) => (i => o)) => o) => o)), args: [(((i => o) => (i => o)) => o), (((i => o) => (i => o)) => o)])` | 670 | 7.1% |
| `isaConst(primitive Pure.eq, ((((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)) => ((((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)) => o)), args: [(((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)), (((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o))])` | 92 | 1.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => (o => (i => o))) => o) => ((((i => o) => (o => (i => o))) => o) => o)), args: [(((i => o) => (o => (i => o))) => o), (((i => o) => (o => (i => o))) => o)])` | 92 | 1.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => i) => (((i => o) => i) => o)) => ((((i => o) => i) => (((i => o) => i) => o)) => o)), args: [(((i => o) => i) => (((i => o) => i) => o)), (((i => o) => i) => (((i => o) => i) => o))])` | 5274 | 56.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => i) => o) => ((((i => o) => i) => o) => o)), args: [(((i => o) => i) => o), (((i => o) => i) => o)])` | 5274 | 56.0% |
| `isaConst(primitive Pure.eq, ((((i => o) => o) => (((i => o) => o) => o)) => ((((i => o) => o) => (((i => o) => o) => o)) => o)), args: [(((i => o) => o) => (((i => o) => o) => o)), (((i => o) => o) => (((i => o) => o) => o))])` | 4100 | 43.5% |
| `isaConst(primitive Pure.eq, ((((i => o) => o) => o) => ((((i => o) => o) => o) => o)), args: [(((i => o) => o) => o), (((i => o) => o) => o)])` | 4102 | 43.5% |
| `isaConst(primitive Pure.eq, (((i => 'a) => ((i => 'a) => o)) => (((i => 'a) => ((i => 'a) => o)) => o)), args: [((i => 'a) => ((i => 'a) => o)), ((i => 'a) => ((i => 'a) => o))])` | 2739 | 29.1% |
| `isaConst(primitive Pure.eq, (((i => 'a) => o) => (((i => 'a) => o) => o)), args: [((i => 'a) => o), ((i => 'a) => o)])` | 2739 | 29.1% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)) => (((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)) => o)), args: [((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)), ((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o))])` | 25 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => (i => i))) => i)) => o) => (((i => ((i => (i => (i => i))) => i)) => o) => o)), args: [((i => ((i => (i => (i => i))) => i)) => o), ((i => ((i => (i => (i => i))) => i)) => o)])` | 25 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)) => (((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)) => o)), args: [((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)), ((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o))])` | 53 | 0.6% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => (i => (i => i)))) => o) => (((i => ((i => (i => i)) => (i => (i => i)))) => o) => o)), args: [((i => ((i => (i => i)) => (i => (i => i)))) => o), ((i => ((i => (i => i)) => (i => (i => i)))) => o)])` | 53 | 0.6% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)) => (((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)) => o)), args: [((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)), ((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o))])` | 2044 | 21.7% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => (i => i))) => o) => (((i => ((i => (i => i)) => (i => i))) => o) => o)), args: [((i => ((i => (i => i)) => (i => i))) => o), ((i => ((i => (i => i)) => (i => i))) => o)])` | 2044 | 21.7% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)) => (((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)) => o)), args: [((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)), ((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o))])` | 3706 | 39.3% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => i)) => i)) => o) => (((i => ((i => (i => i)) => i)) => o) => o)), args: [((i => ((i => (i => i)) => i)) => o), ((i => ((i => (i => i)) => i)) => o)])` | 3706 | 39.3% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)) => (((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)) => o)), args: [((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)), ((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o))])` | 7313 | 77.6% |
| `isaConst(primitive Pure.eq, (((i => ((i => (i => o)) => i)) => o) => (((i => ((i => (i => o)) => i)) => o) => o)), args: [((i => ((i => (i => o)) => i)) => o), ((i => ((i => (i => o)) => i)) => o)])` | 7313 | 77.6% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)) => (((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)) => o)), args: [((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)), ((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o))])` | 3854 | 40.9% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => (i => i))) => o) => (((i => ((i => i) => (i => i))) => o) => o)), args: [((i => ((i => i) => (i => i))) => o), ((i => ((i => i) => (i => i))) => o)])` | 3854 | 40.9% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)) => (((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)) => o)), args: [((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)), ((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o))])` | 6215 | 66.0% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => i)) => o) => (((i => ((i => i) => i)) => o) => o)), args: [((i => ((i => i) => i)) => o), ((i => ((i => i) => i)) => o)])` | 6215 | 66.0% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)) => (((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)) => o)), args: [((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)), ((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o))])` | 4841 | 51.4% |
| `isaConst(primitive Pure.eq, (((i => ((i => i) => o)) => o) => (((i => ((i => i) => o)) => o) => o)), args: [((i => ((i => i) => o)) => o), ((i => ((i => i) => o)) => o)])` | 4841 | 51.4% |
| `isaConst(primitive Pure.eq, (((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)) => (((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)) => o)), args: [((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)), ((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o))])` | 7247 | 76.9% |
| `isaConst(primitive Pure.eq, (((i => ((i => o) => i)) => o) => (((i => ((i => o) => i)) => o) => o)), args: [((i => ((i => o) => i)) => o), ((i => ((i => o) => i)) => o)])` | 7247 | 76.9% |
| `isaConst(primitive Pure.eq, (((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)) => (((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)) => o)), args: [((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)), ((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o))])` | 7493 | 79.5% |
| `isaConst(primitive Pure.eq, (((i => ((i => o) => o)) => o) => (((i => ((i => o) => o)) => o) => o)), args: [((i => ((i => o) => o)) => o), ((i => ((i => o) => o)) => o)])` | 7493 | 79.5% |
| `isaConst(primitive Pure.eq, (((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)), args: [((i => (i => 'a)) => (i => 'a)), ((i => (i => 'a)) => (i => 'a))])` | 3297 | 35.0% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)) => (((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)) => o)), args: [((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)), ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o))])` | 8 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o) => (((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o) => o)), args: [((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o), ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)])` | 8 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)) => (((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)) => o)), args: [((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)), ((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o))])` | 4068 | 43.2% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => (i => o)))) => o) => (((i => (i => ((i => (i => i)) => (i => o)))) => o) => o)), args: [((i => (i => ((i => (i => i)) => (i => o)))) => o), ((i => (i => ((i => (i => i)) => (i => o)))) => o)])` | 4068 | 43.2% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)) => (((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)) => o)), args: [((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)), ((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o))])` | 4061 | 43.1% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => i))) => o) => (((i => (i => ((i => (i => i)) => i))) => o) => o)), args: [((i => (i => ((i => (i => i)) => i))) => o), ((i => (i => ((i => (i => i)) => i))) => o)])` | 4061 | 43.1% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)) => (((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)) => o)), args: [((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)), ((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o))])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => (i => i)) => o))) => o) => (((i => (i => ((i => (i => i)) => o))) => o) => o)), args: [((i => (i => ((i => (i => i)) => o))) => o), ((i => (i => ((i => (i => i)) => o))) => o)])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)) => (((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)) => o)), args: [((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)), ((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o))])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => ((i => i) => ((i => i) => (i => o))))) => o) => (((i => (i => ((i => i) => ((i => i) => (i => o))))) => o) => o)), args: [((i => (i => ((i => i) => ((i => i) => (i => o))))) => o), ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)) => (((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)) => o)), args: [((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)), ((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o))])` | 896 | 9.5% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => ((i => (i => i)) => i)))) => o) => (((i => (i => (i => ((i => (i => i)) => i)))) => o) => o)), args: [((i => (i => (i => ((i => (i => i)) => i)))) => o), ((i => (i => (i => ((i => (i => i)) => i)))) => o)])` | 896 | 9.5% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)) => (((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)) => o)), args: [((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)), ((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o))])` | 21 | 0.2% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => ((i => i) => o)))) => o) => (((i => (i => (i => ((i => i) => o)))) => o) => o)), args: [((i => (i => (i => ((i => i) => o)))) => o), ((i => (i => (i => ((i => i) => o)))) => o)])` | 21 | 0.2% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)) => (((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)) => o)), args: [((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)), ((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o))])` | 35 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => (i => i)))))) => o) => (((i => (i => (i => (i => (i => (i => i)))))) => o) => o)), args: [((i => (i => (i => (i => (i => (i => i)))))) => o), ((i => (i => (i => (i => (i => (i => i)))))) => o)])` | 35 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)) => (((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)) => o)), args: [((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)), ((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o))])` | 187 | 2.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => i))))) => o) => (((i => (i => (i => (i => (i => i))))) => o) => o)), args: [((i => (i => (i => (i => (i => i))))) => o), ((i => (i => (i => (i => (i => i))))) => o)])` | 187 | 2.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)) => (((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)) => o)), args: [((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)), ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o))])` | 9 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)) => (((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)) => o)), args: [((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)), ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => (i => o))))) => o) => (((i => (i => (i => (i => (i => o))))) => o) => o)), args: [((i => (i => (i => (i => (i => o))))) => o), ((i => (i => (i => (i => (i => o))))) => o)])` | 9 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)) => (((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)) => o)), args: [((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)), ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o))])` | 1108 | 11.8% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))) => (((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))) => o)), args: [((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))), ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))])` | 38 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))) => (((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))) => o)), args: [((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))), ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))])` | 24 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => i)))) => o) => (((i => (i => (i => (i => i)))) => o) => o)), args: [((i => (i => (i => (i => i)))) => o), ((i => (i => (i => (i => i)))) => o)])` | 1109 | 11.8% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)) => (((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)) => o)), args: [((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)), ((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o))])` | 114 | 1.2% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)) => (((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)) => o)), args: [((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)), ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))])` | 2 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => (i => o)))) => o) => (((i => (i => (i => (i => o)))) => o) => o)), args: [((i => (i => (i => (i => o)))) => o), ((i => (i => (i => (i => o)))) => o)])` | 114 | 1.2% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => ((i => (i => (i => i))) => o)) => (((i => (i => (i => i))) => ((i => (i => (i => i))) => o)) => o)), args: [((i => (i => (i => i))) => ((i => (i => (i => i))) => o)), ((i => (i => (i => i))) => ((i => (i => (i => i))) => o))])` | 3075 | 32.6% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => ((i => (i => i)) => (i => i))) => (((i => (i => (i => i))) => ((i => (i => i)) => (i => i))) => o)), args: [((i => (i => (i => i))) => ((i => (i => i)) => (i => i))), ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))])` | 10 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => (i => (i => i))) => (((i => (i => (i => i))) => (i => (i => i))) => o)), args: [((i => (i => (i => i))) => (i => (i => i))), ((i => (i => (i => i))) => (i => (i => i)))])` | 103 | 1.1% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)), args: [((i => (i => (i => i))) => (i => i)), ((i => (i => (i => i))) => (i => i))])` | 1097 | 11.6% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => i) => (((i => (i => (i => i))) => i) => o)), args: [((i => (i => (i => i))) => i), ((i => (i => (i => i))) => i)])` | 25 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => i))) => o) => (((i => (i => (i => i))) => o) => o)), args: [((i => (i => (i => i))) => o), ((i => (i => (i => i))) => o)])` | 3077 | 32.7% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))) => (((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))) => o)), args: [((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))), ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))])` | 70 | 0.7% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))) => (((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))) => o)), args: [((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))), ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))])` | 70 | 0.7% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => ((i => (i => (i => o))) => o)) => (((i => (i => (i => o))) => ((i => (i => (i => o))) => o)) => o)), args: [((i => (i => (i => o))) => ((i => (i => (i => o))) => o)), ((i => (i => (i => o))) => ((i => (i => (i => o))) => o))])` | 284 | 3.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => ((i => (i => i)) => o)) => (((i => (i => (i => o))) => ((i => (i => i)) => o)) => o)), args: [((i => (i => (i => o))) => ((i => (i => i)) => o)), ((i => (i => (i => o))) => ((i => (i => i)) => o))])` | 185 | 2.0% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))) => (((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))) => o)), args: [((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))), ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))])` | 70 | 0.7% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => (i => (i => (i => o)))) => (((i => (i => (i => o))) => (i => (i => (i => o)))) => o)), args: [((i => (i => (i => o))) => (i => (i => (i => o)))), ((i => (i => (i => o))) => (i => (i => (i => o))))])` | 318 | 3.4% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => (i => (i => o))) => (((i => (i => (i => o))) => (i => (i => o))) => o)), args: [((i => (i => (i => o))) => (i => (i => o))), ((i => (i => (i => o))) => (i => (i => o)))])` | 149 | 1.6% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => (i => o)) => (((i => (i => (i => o))) => (i => o)) => o)), args: [((i => (i => (i => o))) => (i => o)), ((i => (i => (i => o))) => (i => o))])` | 156 | 1.7% |
| `isaConst(primitive Pure.eq, (((i => (i => (i => o))) => o) => (((i => (i => (i => o))) => o) => o)), args: [((i => (i => (i => o))) => o), ((i => (i => (i => o))) => o)])` | 284 | 3.0% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))) => (((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))) => o)), args: [((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))), ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))])` | 38 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))) => (((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))) => o)), args: [((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))), ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))])` | 24 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))) => (((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))) => o)), args: [((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))), ((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i))))])` | 10 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => (i => i))) => (i => i))) => (((i => (i => i)) => ((i => (i => (i => i))) => (i => i))) => o)), args: [((i => (i => i)) => ((i => (i => (i => i))) => (i => i))), ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))])` | 37 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)), args: [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))])` | 55 | 0.6% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))) => o)), args: [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))), ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))))])` | 24 | 0.3% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))) => o)), args: [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))), ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))])` | 21 | 0.2% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => (i => i))) => (((i => (i => i)) => ((i => (i => i)) => (i => i))) => o)), args: [((i => (i => i)) => ((i => (i => i)) => (i => i))), ((i => (i => i)) => ((i => (i => i)) => (i => i)))])` | 23 | 0.2% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => i)) => (((i => (i => i)) => ((i => (i => i)) => i)) => o)), args: [((i => (i => i)) => ((i => (i => i)) => i)), ((i => (i => i)) => ((i => (i => i)) => i))])` | 8 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => (i => i)) => o)) => (((i => (i => i)) => ((i => (i => i)) => o)) => o)), args: [((i => (i => i)) => ((i => (i => i)) => o)), ((i => (i => i)) => ((i => (i => i)) => o))])` | 6923 | 73.5% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => ((i => i) => (i => i))) => (((i => (i => i)) => ((i => i) => (i => i))) => o)), args: [((i => (i => i)) => ((i => i) => (i => i))), ((i => (i => i)) => ((i => i) => (i => i)))])` | 965 | 10.2% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))) => (((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))) => o)), args: [((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))), ((i => (i => i)) => (i => ((i => (i => i)) => (i => i))))])` | 35 | 0.4% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => (i => (i => i))) => (((i => (i => i)) => (i => (i => i))) => o)), args: [((i => (i => i)) => (i => (i => i))), ((i => (i => i)) => (i => (i => i)))])` | 91 | 1.0% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)), args: [((i => (i => i)) => (i => i)), ((i => (i => i)) => (i => i))])` | 3429 | 36.4% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => (i => o)) => (((i => (i => i)) => (i => o)) => o)), args: [((i => (i => i)) => (i => o)), ((i => (i => i)) => (i => o))])` | 4068 | 43.2% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => i) => (((i => (i => i)) => i) => o)), args: [((i => (i => i)) => i), ((i => (i => i)) => i)])` | 4065 | 43.2% |
| `isaConst(primitive Pure.eq, (((i => (i => i)) => o) => (((i => (i => i)) => o) => o)), args: [((i => (i => i)) => o), ((i => (i => i)) => o)])` | 6927 | 73.5% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => ((i => (i => o)) => o)) => (((i => (i => o)) => ((i => (i => o)) => o)) => o)), args: [((i => (i => o)) => ((i => (i => o)) => o)), ((i => (i => o)) => ((i => (i => o)) => o))])` | 7387 | 78.4% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => ((i => i) => o)) => (((i => (i => o)) => ((i => i) => o)) => o)), args: [((i => (i => o)) => ((i => i) => o)), ((i => (i => o)) => ((i => i) => o))])` | 132 | 1.4% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => (i => (i => (i => (i => o))))) => (((i => (i => o)) => (i => (i => (i => (i => o))))) => o)), args: [((i => (i => o)) => (i => (i => (i => (i => o))))), ((i => (i => o)) => (i => (i => (i => (i => o)))))])` | 243 | 2.6% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => (i => (i => (i => o)))) => (((i => (i => o)) => (i => (i => (i => o)))) => o)), args: [((i => (i => o)) => (i => (i => (i => o)))), ((i => (i => o)) => (i => (i => (i => o))))])` | 225 | 2.4% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => (i => (i => o))) => (((i => (i => o)) => (i => (i => o))) => o)), args: [((i => (i => o)) => (i => (i => o))), ((i => (i => o)) => (i => (i => o)))])` | 250 | 2.7% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => (i => o)) => (((i => (i => o)) => (i => o)) => o)), args: [((i => (i => o)) => (i => o)), ((i => (i => o)) => (i => o))])` | 344 | 3.7% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => i) => (((i => (i => o)) => i) => o)), args: [((i => (i => o)) => i), ((i => (i => o)) => i)])` | 7313 | 77.6% |
| `isaConst(primitive Pure.eq, (((i => (i => o)) => o) => (((i => (i => o)) => o) => o)), args: [((i => (i => o)) => o), ((i => (i => o)) => o)])` | 7404 | 78.6% |
| `isaConst(primitive Pure.eq, (((i => i) => ((i => (i => (i => i))) => (i => i))) => (((i => i) => ((i => (i => (i => i))) => (i => i))) => o)), args: [((i => i) => ((i => (i => (i => i))) => (i => i))), ((i => i) => ((i => (i => (i => i))) => (i => i)))])` | 92 | 1.0% |
| `isaConst(primitive Pure.eq, (((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))) => (((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))) => o)), args: [((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))), ((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i))))])` | 23 | 0.2% |
| `isaConst(primitive Pure.eq, (((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)), args: [((i => i) => ((i => i) => (i => i))), ((i => i) => ((i => i) => (i => i)))])` | 2872 | 30.5% |
| `isaConst(primitive Pure.eq, (((i => i) => ((i => i) => (i => o))) => (((i => i) => ((i => i) => (i => o))) => o)), args: [((i => i) => ((i => i) => (i => o))), ((i => i) => ((i => i) => (i => o)))])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => i) => ((i => i) => o)) => (((i => i) => ((i => i) => o)) => o)), args: [((i => i) => ((i => i) => o)), ((i => i) => ((i => i) => o))])` | 6847 | 72.7% |
| `isaConst(primitive Pure.eq, (((i => i) => (i => (i => i))) => (((i => i) => (i => (i => i))) => o)), args: [((i => i) => (i => (i => i))), ((i => i) => (i => (i => i)))])` | 442 | 4.7% |
| `isaConst(primitive Pure.eq, (((i => i) => (i => i)) => (((i => i) => (i => i)) => o)), args: [((i => i) => (i => i)), ((i => i) => (i => i))])` | 4226 | 44.9% |
| `isaConst(primitive Pure.eq, (((i => i) => (i => o)) => (((i => i) => (i => o)) => o)), args: [((i => i) => (i => o)), ((i => i) => (i => o))])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, (((i => i) => i) => (((i => i) => i) => o)), args: [((i => i) => i), ((i => i) => i)])` | 6229 | 66.1% |
| `isaConst(primitive Pure.eq, (((i => i) => o) => (((i => i) => o) => o)), args: [((i => i) => o), ((i => i) => o)])` | 6973 | 74.0% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)), args: [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), ((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)), args: [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), ((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), ((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))])` | 136 | 1.4% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), ((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o)))])` | 183 | 1.9% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), ((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o)))))])` | 441 | 4.7% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), ((i => o) => ((i => (i => (i => o))) => (i => (i => o))))])` | 75 | 0.8% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => o))), ((i => o) => ((i => (i => (i => o))) => (i => o)))])` | 222 | 2.4% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)), args: [((i => o) => ((i => (i => o)) => ((i => i) => o))), ((i => o) => ((i => (i => o)) => ((i => i) => o)))])` | 128 | 1.4% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), ((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o))))))])` | 341 | 3.6% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), ((i => o) => ((i => (i => o)) => (i => (i => (i => o)))))])` | 323 | 3.4% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)), args: [((i => o) => ((i => (i => o)) => (i => o))), ((i => o) => ((i => (i => o)) => (i => o)))])` | 201 | 2.1% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)), args: [((i => o) => ((i => (i => o)) => o)), ((i => o) => ((i => (i => o)) => o))])` | 821 | 8.7% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => o) => ((i => (i => o)) => o))) => (((i => o) => ((i => o) => ((i => (i => o)) => o))) => o)), args: [((i => o) => ((i => o) => ((i => (i => o)) => o))), ((i => o) => ((i => o) => ((i => (i => o)) => o)))])` | 429 | 4.6% |
| `isaConst(primitive Pure.eq, (((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)), args: [((i => o) => ((i => o) => o)), ((i => o) => ((i => o) => o))])` | 5713 | 60.6% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)), args: [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), ((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o)))))])` | 3 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)), args: [((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), ((i => o) => (i => ((i => (i => o)) => ((i => i) => o))))])` | 63 | 0.7% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)), args: [((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), ((i => o) => (i => ((i => (i => o)) => (i => (i => o)))))])` | 348 | 3.7% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)), args: [((i => o) => (i => ((i => (i => o)) => (i => o)))), ((i => o) => (i => ((i => (i => o)) => (i => o))))])` | 162 | 1.7% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)), args: [((i => o) => (i => ((i => (i => o)) => o))), ((i => o) => (i => ((i => (i => o)) => o)))])` | 599 | 6.4% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)), args: [((i => o) => (i => ((i => o) => (i => o)))), ((i => o) => (i => ((i => o) => (i => o))))])` | 65 | 0.7% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)), args: [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), ((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))])` | 60 | 0.6% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)), args: [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), ((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)), args: [((i => o) => (i => (i => (i => (i => (i => o)))))), ((i => o) => (i => (i => (i => (i => (i => o))))))])` | 186 | 2.0% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)), args: [((i => o) => (i => (i => (i => (i => o))))), ((i => o) => (i => (i => (i => (i => o)))))])` | 199 | 2.1% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)), args: [((i => o) => (i => (i => (i => o)))), ((i => o) => (i => (i => (i => o))))])` | 1248 | 13.2% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)), args: [((i => o) => (i => (i => i))), ((i => o) => (i => (i => i)))])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)), args: [((i => o) => (i => (i => o))), ((i => o) => (i => (i => o)))])` | 1169 | 12.4% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => i)) => (((i => o) => (i => i)) => o)), args: [((i => o) => (i => i)), ((i => o) => (i => i))])` | 446 | 4.7% |
| `isaConst(primitive Pure.eq, (((i => o) => (i => o)) => (((i => o) => (i => o)) => o)), args: [((i => o) => (i => o)), ((i => o) => (i => o))])` | 1019 | 10.8% |
| `isaConst(primitive Pure.eq, (((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)), args: [((i => o) => (o => (i => o))), ((i => o) => (o => (i => o)))])` | 132 | 1.4% |
| `isaConst(primitive Pure.eq, (((i => o) => i) => (((i => o) => i) => o)), args: [((i => o) => i), ((i => o) => i)])` | 8048 | 85.4% |
| `isaConst(primitive Pure.eq, (((i => o) => o) => (((i => o) => o) => o)), args: [((i => o) => o), ((i => o) => o)])` | 7805 | 82.9% |
| `isaConst(primitive Pure.eq, (((o => (i => (i => i))) => ((o => (i => (i => i))) => o)) => (((o => (i => (i => i))) => ((o => (i => (i => i))) => o)) => o)), args: [((o => (i => (i => i))) => ((o => (i => (i => i))) => o)), ((o => (i => (i => i))) => ((o => (i => (i => i))) => o))])` | 5018 | 53.3% |
| `isaConst(primitive Pure.eq, (((o => (i => (i => i))) => o) => (((o => (i => (i => i))) => o) => o)), args: [((o => (i => (i => i))) => o), ((o => (i => (i => i))) => o)])` | 5018 | 53.3% |
| `isaConst(primitive Pure.eq, (((o => (o => o)) => ((o => (o => o)) => o)) => (((o => (o => o)) => ((o => (o => o)) => o)) => o)), args: [((o => (o => o)) => ((o => (o => o)) => o)), ((o => (o => o)) => ((o => (o => o)) => o))])` | 7841 | 83.2% |
| `isaConst(primitive Pure.eq, (((o => (o => o)) => o) => (((o => (o => o)) => o) => o)), args: [((o => (o => o)) => o), ((o => (o => o)) => o)])` | 7841 | 83.2% |
| `isaConst(primitive Pure.eq, (((o => i) => ((o => i) => o)) => (((o => i) => ((o => i) => o)) => o)), args: [((o => i) => ((o => i) => o)), ((o => i) => ((o => i) => o))])` | 882 | 9.4% |
| `isaConst(primitive Pure.eq, (((o => i) => o) => (((o => i) => o) => o)), args: [((o => i) => o), ((o => i) => o)])` | 882 | 9.4% |
| `isaConst(primitive Pure.eq, (((o => o) => ((o => o) => o)) => (((o => o) => ((o => o) => o)) => o)), args: [((o => o) => ((o => o) => o)), ((o => o) => ((o => o) => o))])` | 7819 | 83.0% |
| `isaConst(primitive Pure.eq, (((o => o) => o) => (((o => o) => o) => o)), args: [((o => o) => o), ((o => o) => o)])` | 7819 | 83.0% |
| `isaConst(primitive Pure.eq, ((i => 'a) => ((i => 'a) => o)), args: [(i => 'a), (i => 'a)])` | 2773 | 29.4% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => ((i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)), args: [(i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)), args: [(i => ((i => (i => (i => i))) => i)), (i => ((i => (i => (i => i))) => i))])` | 30 | 0.3% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => ((i => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)), args: [(i => ((i => (i => (i => o))) => ((i => (i => i)) => o))), (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))])` | 41 | 0.4% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => (i => o))) => (i => (i => o)))) => ((i => ((i => (i => (i => o))) => (i => (i => o)))) => o)), args: [(i => ((i => (i => (i => o))) => (i => (i => o)))), (i => ((i => (i => (i => o))) => (i => (i => o))))])` | 3 | 0.0% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => ((i => (i => i)) => i))) => ((i => ((i => (i => i)) => ((i => (i => i)) => i))) => o)), args: [(i => ((i => (i => i)) => ((i => (i => i)) => i))), (i => ((i => (i => i)) => ((i => (i => i)) => i)))])` | 8 | 0.1% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)), args: [(i => ((i => (i => i)) => (i => (i => i)))), (i => ((i => (i => i)) => (i => (i => i))))])` | 55 | 0.6% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)), args: [(i => ((i => (i => i)) => (i => i))), (i => ((i => (i => i)) => (i => i)))])` | 2493 | 26.5% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => (i => o))) => ((i => ((i => (i => i)) => (i => o))) => o)), args: [(i => ((i => (i => i)) => (i => o))), (i => ((i => (i => i)) => (i => o)))])` | 4068 | 43.2% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)), args: [(i => ((i => (i => i)) => i)), (i => ((i => (i => i)) => i))])` | 4978 | 52.8% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => i)) => o)) => ((i => ((i => (i => i)) => o)) => o)), args: [(i => ((i => (i => i)) => o)), (i => ((i => (i => i)) => o))])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => o)) => ((i => i) => o))) => ((i => ((i => (i => o)) => ((i => i) => o))) => o)), args: [(i => ((i => (i => o)) => ((i => i) => o))), (i => ((i => (i => o)) => ((i => i) => o)))])` | 44 | 0.5% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => o)) => (i => (i => o)))) => ((i => ((i => (i => o)) => (i => (i => o)))) => o)), args: [(i => ((i => (i => o)) => (i => (i => o)))), (i => ((i => (i => o)) => (i => (i => o))))])` | 249 | 2.6% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => o)) => (i => o))) => ((i => ((i => (i => o)) => (i => o))) => o)), args: [(i => ((i => (i => o)) => (i => o))), (i => ((i => (i => o)) => (i => o)))])` | 96 | 1.0% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)), args: [(i => ((i => (i => o)) => i)), (i => ((i => (i => o)) => i))])` | 8957 | 95.1% |
| `isaConst(primitive Pure.eq, ((i => ((i => (i => o)) => o)) => ((i => ((i => (i => o)) => o)) => o)), args: [(i => ((i => (i => o)) => o)), (i => ((i => (i => o)) => o))])` | 374 | 4.0% |
| `isaConst(primitive Pure.eq, ((i => ((i => i) => ((i => i) => (i => o)))) => ((i => ((i => i) => ((i => i) => (i => o)))) => o)), args: [(i => ((i => i) => ((i => i) => (i => o)))), (i => ((i => i) => ((i => i) => (i => o))))])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, ((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)), args: [(i => ((i => i) => (i => i))), (i => ((i => i) => (i => i)))])` | 4781 | 50.8% |
| `isaConst(primitive Pure.eq, ((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)), args: [(i => ((i => i) => i)), (i => ((i => i) => i))])` | 7209 | 76.5% |
| `isaConst(primitive Pure.eq, ((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)), args: [(i => ((i => i) => o)), (i => ((i => i) => o))])` | 4846 | 51.4% |
| `isaConst(primitive Pure.eq, ((i => ((i => o) => (i => o))) => ((i => ((i => o) => (i => o))) => o)), args: [(i => ((i => o) => (i => o))), (i => ((i => o) => (i => o)))])` | 46 | 0.5% |
| `isaConst(primitive Pure.eq, ((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)), args: [(i => ((i => o) => i)), (i => ((i => o) => i))])` | 8137 | 86.4% |
| `isaConst(primitive Pure.eq, ((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)), args: [(i => ((i => o) => o)), (i => ((i => o) => o))])` | 8395 | 89.1% |
| `isaConst(primitive Pure.eq, ((i => (i => 'a)) => ((i => (i => 'a)) => o)), args: [(i => (i => 'a)), (i => (i => 'a))])` | 2773 | 29.4% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))) => ((i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))) => o)), args: [(i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))), (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))) => ((i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))) => o)), args: [(i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))), (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))])` | 41 | 0.4% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)), args: [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), (i => (i => ((i => (i => i)) => ((i => (i => i)) => i))))])` | 9 | 0.1% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => i)) => (i => i)))) => ((i => (i => ((i => (i => i)) => (i => i)))) => o)), args: [(i => (i => ((i => (i => i)) => (i => i)))), (i => (i => ((i => (i => i)) => (i => i))))])` | 13 | 0.1% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)), args: [(i => (i => ((i => (i => i)) => (i => o)))), (i => (i => ((i => (i => i)) => (i => o))))])` | 5033 | 53.4% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)), args: [(i => (i => ((i => (i => i)) => i))), (i => (i => ((i => (i => i)) => i)))])` | 5018 | 53.3% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)), args: [(i => (i => ((i => (i => i)) => o))), (i => (i => ((i => (i => i)) => o)))])` | 439 | 4.7% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)), args: [(i => (i => ((i => i) => ((i => i) => (i => o))))), (i => (i => ((i => i) => ((i => i) => (i => o)))))])` | 7 | 0.1% |
| `isaConst(primitive Pure.eq, ((i => (i => ((i => i) => o))) => ((i => (i => ((i => i) => o))) => o)), args: [(i => (i => ((i => i) => o))), (i => (i => ((i => i) => o)))])` | 21 | 0.2% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))) => ((i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))) => o)), args: [(i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))), (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))])` | 1 | 0.0% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)), args: [(i => (i => (i => ((i => (i => i)) => i)))), (i => (i => (i => ((i => (i => i)) => i))))])` | 947 | 10.1% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)), args: [(i => (i => (i => ((i => i) => o)))), (i => (i => (i => ((i => i) => o))))])` | 21 | 0.2% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)), args: [(i => (i => (i => (i => (i => (i => i)))))), (i => (i => (i => (i => (i => (i => i))))))])` | 39 | 0.4% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)), args: [(i => (i => (i => (i => (i => i))))), (i => (i => (i => (i => (i => i)))))])` | 210 | 2.2% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)), args: [(i => (i => (i => (i => (i => o))))), (i => (i => (i => (i => (i => o)))))])` | 104 | 1.1% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)), args: [(i => (i => (i => (i => i)))), (i => (i => (i => (i => i))))])` | 1305 | 13.9% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)), args: [(i => (i => (i => (i => o)))), (i => (i => (i => (i => o))))])` | 472 | 5.0% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => i))) => ((i => (i => (i => i))) => o)), args: [(i => (i => (i => i))), (i => (i => (i => i)))])` | 3944 | 41.9% |
| `isaConst(primitive Pure.eq, ((i => (i => (i => o))) => ((i => (i => (i => o))) => o)), args: [(i => (i => (i => o))), (i => (i => (i => o)))])` | 1520 | 16.1% |
| `isaConst(primitive Pure.eq, ((i => (i => i)) => ((i => (i => i)) => o)), args: [(i => (i => i)), (i => (i => i))])` | 8788 | 93.3% |
| `isaConst(primitive Pure.eq, ((i => (i => o)) => ((i => (i => o)) => o)), args: [(i => (i => o)), (i => (i => o))])` | 8507 | 90.3% |
| `isaConst(primitive Pure.eq, ((i => i) => ((i => i) => o)), args: [(i => i), (i => i)])` | 8812 | 93.5% |
| `isaConst(primitive Pure.eq, ((i => o) => ((i => o) => o)), args: [(i => o), (i => o)])` | 8490 | 90.1% |
| `isaConst(primitive Pure.eq, ((o => (i => (i => i))) => ((o => (i => (i => i))) => o)), args: [(o => (i => (i => i))), (o => (i => (i => i)))])` | 5590 | 59.3% |
| `isaConst(primitive Pure.eq, ((o => (i => o)) => ((o => (i => o)) => o)), args: [(o => (i => o)), (o => (i => o))])` | 92 | 1.0% |
| `isaConst(primitive Pure.eq, ((o => (o => o)) => ((o => (o => o)) => o)), args: [(o => (o => o)), (o => (o => o))])` | 8409 | 89.3% |
| `isaConst(primitive Pure.eq, ((o => i) => ((o => i) => o)), args: [(o => i), (o => i)])` | 983 | 10.4% |
| `isaConst(primitive Pure.eq, ((o => o) => ((o => o) => o)), args: [(o => o), (o => o)])` | 8817 | 93.6% |
| `isaConst(primitive ZF_Base.Inf, i, args: [])` | 5262 | 55.9% |
| `isaConst(primitive ZF_Base.Pow, (i => i), args: [i])` | 8809 | 93.5% |
| `isaConst(primitive ZF_Base.PrimReplace, (i => ((i => (i => o)) => i)), args: [i, (i => (i => o))])` | 8958 | 95.1% |
| `isaConst(primitive ZF_Base.Union, (i => i), args: [i])` | 8879 | 94.3% |
| `isaConst(primitive ZF_Base.mem, (i => (i => o)), args: [i, i])` | 8617 | 91.5% |
| `isaConst(primitive ZF_Base.zero, i, args: [])` | 8835 | 93.8% |
| `isaFree('a)` | 7418 | 78.7% |
| `isaFree(('a => o))` | 7417 | 78.7% |
| `isaFree((('a => o) => (o => 'a)))` | 7290 | 77.4% |
| `isaFree((i => (i => 'a)))` | 2 | 0.0% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i)))))))))))))))))))))))` | 10 | 0.1% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))))))))` | 185 | 2.0% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))))))` | 10 | 0.1% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i)))))))))))))` | 14 | 0.1% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))` | 16 | 0.2% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => (i => i)))))))))` | 2 | 0.0% |
| `isaFree((i => (i => (i => (i => (i => (i => (i => i))))))))` | 16 | 0.2% |
| `isaFree((i => (i => (i => (i => (i => (i => i)))))))` | 4124 | 43.8% |
| `isaFree((i => (i => (i => (i => (i => i))))))` | 1259 | 13.4% |
| `isaFree((i => (i => (i => (i => i)))))` | 4363 | 46.3% |
| `isaFree((i => (i => (i => i))))` | 4944 | 52.5% |
| `isaFree((i => (i => i)))` | 5182 | 55.0% |
| `isaFree((i => (i => o)))` | 1488 | 15.8% |
| `isaFree((i => i))` | 5611 | 59.6% |
| `isaFree((i => o))` | 1362 | 14.5% |
| `isaFree((o => 'a))` | 7417 | 78.7% |
| `isaFree((o => (('a => o) => 'a)))` | 7290 | 77.4% |
| `isaFree(i)` | 6969 | 74.0% |
| `isaFree(o)` | 7085 | 75.2% |
| `isaOfClass('a)` | 7973 | 84.6% |
| `isaOfClass('b)` | 4634 | 49.2% |
| `isaOfClass(i)` | 7965 | 84.6% |
| `isaVarApp(head: ('a => 'b), args: ['a])` | 4655 | 49.4% |
| `isaVarApp(head: ('a => ('a => o)), args: ['a, 'a])` | 7578 | 80.4% |
| `isaVarApp(head: ('a => ('b => o)), args: ['a, 'b])` | 1195 | 12.7% |
| `isaVarApp(head: ('a => o), args: ['a])` | 9167 | 97.3% |
| `isaVarApp(head: ('b => 'a), args: ['b])` | 439 | 4.7% |
| `isaVarApp(head: ('b => ('b => o)), args: ['b, 'b])` | 4626 | 49.1% |
| `isaVarApp(head: ('b => (('b => 'a) => 'a)), args: ['b, ('b => 'a)])` | 439 | 4.7% |
| `isaVarApp(head: ('b => o), args: ['b])` | 4634 | 49.2% |
| `isaVarApp(head: (('a => o) => (o => 'a)), args: [('a => o), o])` | 7290 | 77.4% |
| `isaVarApp(head: (('a => o) => o), args: [('a => o)])` | 7324 | 77.7% |
| `isaVarApp(head: (('b => 'a) => 'a), args: [('b => 'a)])` | 439 | 4.7% |
| `isaVarApp(head: (('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o)), args: [('b => (('b => 'a) => 'a)), ('b => (('b => 'a) => 'a))])` | 439 | 4.7% |
| `isaVarApp(head: (('b => (('b => 'a) => 'a)) => o), args: [('b => (('b => 'a) => 'a))])` | 439 | 4.7% |
| `isaVarApp(head: ((('a => o) => o) => ((('a => o) => o) => o)), args: [(('a => o) => o), (('a => o) => o)])` | 7323 | 77.7% |
| `isaVarApp(head: ((('a => o) => o) => o), args: [(('a => o) => o)])` | 7323 | 77.7% |
| `isaVarApp(head: (((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o)), args: [((i => (i => 'a)) => (i => 'a)), ((i => (i => 'a)) => (i => 'a))])` | 2773 | 29.4% |
| `isaVarApp(head: (((i => (i => 'a)) => (i => 'a)) => o), args: [((i => (i => 'a)) => (i => 'a))])` | 2773 | 29.4% |
| `isaVarApp(head: (((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o)), args: [((i => (i => (i => i))) => (i => i)), ((i => (i => (i => i))) => (i => i))])` | 4 | 0.0% |
| `isaVarApp(head: (((i => (i => (i => i))) => (i => i)) => o), args: [((i => (i => (i => i))) => (i => i))])` | 4 | 0.0% |
| `isaVarApp(head: (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)), args: [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))])` | 38 | 0.4% |
| `isaVarApp(head: (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o), args: [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))])` | 38 | 0.4% |
| `isaVarApp(head: (((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o)), args: [((i => (i => i)) => (i => i)), ((i => (i => i)) => (i => i))])` | 2760 | 29.3% |
| `isaVarApp(head: (((i => (i => i)) => (i => i)) => o), args: [((i => (i => i)) => (i => i))])` | 2760 | 29.3% |
| `isaVarApp(head: (((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o)), args: [((i => i) => ((i => i) => (i => i))), ((i => i) => ((i => i) => (i => i)))])` | 2421 | 25.7% |
| `isaVarApp(head: (((i => i) => ((i => i) => (i => i))) => o), args: [((i => i) => ((i => i) => (i => i)))])` | 2421 | 25.7% |
| `isaVarApp(head: (((i => i) => (i => i)) => (((i => i) => (i => i)) => o)), args: [((i => i) => (i => i)), ((i => i) => (i => i))])` | 514 | 5.5% |
| `isaVarApp(head: (((i => i) => (i => i)) => o), args: [((i => i) => (i => i))])` | 514 | 5.5% |
| `isaVarApp(head: (((i => i) => o) => (((i => i) => o) => o)), args: [((i => i) => o), ((i => i) => o)])` | 531 | 5.6% |
| `isaVarApp(head: (((i => i) => o) => o), args: [((i => i) => o)])` | 531 | 5.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)), args: [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), ((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o), args: [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)), args: [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), ((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o), args: [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), ((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))])` | 70 | 0.7% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))])` | 70 | 0.7% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), ((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o)))])` | 183 | 1.9% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o), args: [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o)))])` | 183 | 1.9% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), ((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o)))))])` | 318 | 3.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o)))))])` | 318 | 3.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), ((i => o) => ((i => (i => (i => o))) => (i => (i => o))))])` | 53 | 0.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o), args: [((i => o) => ((i => (i => (i => o))) => (i => (i => o))))])` | 53 | 0.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)), args: [((i => o) => ((i => (i => (i => o))) => (i => o))), ((i => o) => ((i => (i => (i => o))) => (i => o)))])` | 155 | 1.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => (i => o))) => (i => o))) => o), args: [((i => o) => ((i => (i => (i => o))) => (i => o)))])` | 155 | 1.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)), args: [((i => o) => ((i => (i => o)) => ((i => i) => o))), ((i => o) => ((i => (i => o)) => ((i => i) => o)))])` | 128 | 1.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o), args: [((i => o) => ((i => (i => o)) => ((i => i) => o)))])` | 128 | 1.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), ((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o))))))])` | 243 | 2.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o))))))])` | 243 | 2.6% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), ((i => o) => ((i => (i => o)) => (i => (i => (i => o)))))])` | 225 | 2.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o), args: [((i => o) => ((i => (i => o)) => (i => (i => (i => o)))))])` | 225 | 2.4% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o)), args: [((i => o) => ((i => (i => o)) => (i => o))), ((i => o) => ((i => (i => o)) => (i => o)))])` | 141 | 1.5% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => (i => o))) => o), args: [((i => o) => ((i => (i => o)) => (i => o)))])` | 141 | 1.5% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o)), args: [((i => o) => ((i => (i => o)) => o)), ((i => o) => ((i => (i => o)) => o))])` | 585 | 6.2% |
| `isaVarApp(head: (((i => o) => ((i => (i => o)) => o)) => o), args: [((i => o) => ((i => (i => o)) => o))])` | 585 | 6.2% |
| `isaVarApp(head: (((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o)), args: [((i => o) => ((i => o) => o)), ((i => o) => ((i => o) => o))])` | 1163 | 12.3% |
| `isaVarApp(head: (((i => o) => ((i => o) => o)) => o), args: [((i => o) => ((i => o) => o))])` | 1163 | 12.3% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)), args: [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), ((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o)))))])` | 3 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o), args: [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o)))))])` | 3 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)), args: [((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), ((i => o) => (i => ((i => (i => o)) => ((i => i) => o))))])` | 44 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o), args: [((i => o) => (i => ((i => (i => o)) => ((i => i) => o))))])` | 44 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)), args: [((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), ((i => o) => (i => ((i => (i => o)) => (i => (i => o)))))])` | 249 | 2.6% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o), args: [((i => o) => (i => ((i => (i => o)) => (i => (i => o)))))])` | 249 | 2.6% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)), args: [((i => o) => (i => ((i => (i => o)) => (i => o)))), ((i => o) => (i => ((i => (i => o)) => (i => o))))])` | 96 | 1.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o), args: [((i => o) => (i => ((i => (i => o)) => (i => o))))])` | 96 | 1.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o)), args: [((i => o) => (i => ((i => (i => o)) => o))), ((i => o) => (i => ((i => (i => o)) => o)))])` | 374 | 4.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => (i => o)) => o))) => o), args: [((i => o) => (i => ((i => (i => o)) => o)))])` | 374 | 4.0% |
| `isaVarApp(head: (((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o)), args: [((i => o) => (i => ((i => o) => (i => o)))), ((i => o) => (i => ((i => o) => (i => o))))])` | 46 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => ((i => o) => (i => o)))) => o), args: [((i => o) => (i => ((i => o) => (i => o))))])` | 46 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)), args: [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), ((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))])` | 41 | 0.4% |
| `isaVarApp(head: (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o), args: [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))])` | 41 | 0.4% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)), args: [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), ((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o), args: [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))])` | 1 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)), args: [((i => o) => (i => (i => (i => (i => (i => o)))))), ((i => o) => (i => (i => (i => (i => (i => o))))))])` | 89 | 0.9% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => (i => (i => o)))))) => o), args: [((i => o) => (i => (i => (i => (i => (i => o))))))])` | 89 | 0.9% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o)), args: [((i => o) => (i => (i => (i => (i => o))))), ((i => o) => (i => (i => (i => (i => o)))))])` | 117 | 1.2% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => (i => o))))) => o), args: [((i => o) => (i => (i => (i => (i => o)))))])` | 117 | 1.2% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o)), args: [((i => o) => (i => (i => (i => o)))), ((i => o) => (i => (i => (i => o))))])` | 1025 | 10.9% |
| `isaVarApp(head: (((i => o) => (i => (i => (i => o)))) => o), args: [((i => o) => (i => (i => (i => o))))])` | 1025 | 10.9% |
| `isaVarApp(head: (((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o)), args: [((i => o) => (i => (i => i))), ((i => o) => (i => (i => i)))])` | 44 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => (i => i))) => o), args: [((i => o) => (i => (i => i)))])` | 44 | 0.5% |
| `isaVarApp(head: (((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o)), args: [((i => o) => (i => (i => o))), ((i => o) => (i => (i => o)))])` | 945 | 10.0% |
| `isaVarApp(head: (((i => o) => (i => (i => o))) => o), args: [((i => o) => (i => (i => o)))])` | 945 | 10.0% |
| `isaVarApp(head: (((i => o) => (i => i)) => (((i => o) => (i => i)) => o)), args: [((i => o) => (i => i)), ((i => o) => (i => i))])` | 2 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => i)) => o), args: [((i => o) => (i => i))])` | 2 | 0.0% |
| `isaVarApp(head: (((i => o) => (i => o)) => (((i => o) => (i => o)) => o)), args: [((i => o) => (i => o)), ((i => o) => (i => o))])` | 670 | 7.1% |
| `isaVarApp(head: (((i => o) => (i => o)) => o), args: [((i => o) => (i => o))])` | 670 | 7.1% |
| `isaVarApp(head: (((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o)), args: [((i => o) => (o => (i => o))), ((i => o) => (o => (i => o)))])` | 92 | 1.0% |
| `isaVarApp(head: (((i => o) => (o => (i => o))) => o), args: [((i => o) => (o => (i => o)))])` | 92 | 1.0% |
| `isaVarApp(head: (((i => o) => i) => (((i => o) => i) => o)), args: [((i => o) => i), ((i => o) => i)])` | 5274 | 56.0% |
| `isaVarApp(head: (((i => o) => i) => o), args: [((i => o) => i)])` | 5274 | 56.0% |
| `isaVarApp(head: (((i => o) => o) => (((i => o) => o) => o)), args: [((i => o) => o), ((i => o) => o)])` | 4100 | 43.5% |
| `isaVarApp(head: (((i => o) => o) => o), args: [((i => o) => o)])` | 4102 | 43.5% |
| `isaVarApp(head: ((i => 'a) => ((i => 'a) => o)), args: [(i => 'a), (i => 'a)])` | 2739 | 29.1% |
| `isaVarApp(head: ((i => 'a) => o), args: [(i => 'a)])` | 2739 | 29.1% |
| `isaVarApp(head: ((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o)), args: [(i => ((i => (i => (i => i))) => i)), (i => ((i => (i => (i => i))) => i))])` | 25 | 0.3% |
| `isaVarApp(head: ((i => ((i => (i => (i => i))) => i)) => o), args: [(i => ((i => (i => (i => i))) => i))])` | 25 | 0.3% |
| `isaVarApp(head: ((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o)), args: [(i => ((i => (i => i)) => (i => (i => i)))), (i => ((i => (i => i)) => (i => (i => i))))])` | 53 | 0.6% |
| `isaVarApp(head: ((i => ((i => (i => i)) => (i => (i => i)))) => o), args: [(i => ((i => (i => i)) => (i => (i => i))))])` | 53 | 0.6% |
| `isaVarApp(head: ((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o)), args: [(i => ((i => (i => i)) => (i => i))), (i => ((i => (i => i)) => (i => i)))])` | 2044 | 21.7% |
| `isaVarApp(head: ((i => ((i => (i => i)) => (i => i))) => o), args: [(i => ((i => (i => i)) => (i => i)))])` | 2044 | 21.7% |
| `isaVarApp(head: ((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o)), args: [(i => ((i => (i => i)) => i)), (i => ((i => (i => i)) => i))])` | 3706 | 39.3% |
| `isaVarApp(head: ((i => ((i => (i => i)) => i)) => o), args: [(i => ((i => (i => i)) => i))])` | 3706 | 39.3% |
| `isaVarApp(head: ((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o)), args: [(i => ((i => (i => o)) => i)), (i => ((i => (i => o)) => i))])` | 7313 | 77.6% |
| `isaVarApp(head: ((i => ((i => (i => o)) => i)) => o), args: [(i => ((i => (i => o)) => i))])` | 7313 | 77.6% |
| `isaVarApp(head: ((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o)), args: [(i => ((i => i) => (i => i))), (i => ((i => i) => (i => i)))])` | 3854 | 40.9% |
| `isaVarApp(head: ((i => ((i => i) => (i => i))) => o), args: [(i => ((i => i) => (i => i)))])` | 3854 | 40.9% |
| `isaVarApp(head: ((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o)), args: [(i => ((i => i) => i)), (i => ((i => i) => i))])` | 6215 | 66.0% |
| `isaVarApp(head: ((i => ((i => i) => i)) => o), args: [(i => ((i => i) => i))])` | 6215 | 66.0% |
| `isaVarApp(head: ((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o)), args: [(i => ((i => i) => o)), (i => ((i => i) => o))])` | 4841 | 51.4% |
| `isaVarApp(head: ((i => ((i => i) => o)) => o), args: [(i => ((i => i) => o))])` | 4841 | 51.4% |
| `isaVarApp(head: ((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o)), args: [(i => ((i => o) => i)), (i => ((i => o) => i))])` | 7247 | 76.9% |
| `isaVarApp(head: ((i => ((i => o) => i)) => o), args: [(i => ((i => o) => i))])` | 7247 | 76.9% |
| `isaVarApp(head: ((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o)), args: [(i => ((i => o) => o)), (i => ((i => o) => o))])` | 7493 | 79.5% |
| `isaVarApp(head: ((i => ((i => o) => o)) => o), args: [(i => ((i => o) => o))])` | 7493 | 79.5% |
| `isaVarApp(head: ((i => (i => 'a)) => (i => 'a)), args: [(i => (i => 'a)), i])` | 2773 | 29.4% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)), args: [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), (i => (i => ((i => (i => i)) => ((i => (i => i)) => i))))])` | 8 | 0.1% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o), args: [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i))))])` | 8 | 0.1% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o)), args: [(i => (i => ((i => (i => i)) => (i => o)))), (i => (i => ((i => (i => i)) => (i => o))))])` | 4068 | 43.2% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => (i => o)))) => o), args: [(i => (i => ((i => (i => i)) => (i => o))))])` | 4068 | 43.2% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o)), args: [(i => (i => ((i => (i => i)) => i))), (i => (i => ((i => (i => i)) => i)))])` | 4061 | 43.1% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => i))) => o), args: [(i => (i => ((i => (i => i)) => i)))])` | 4061 | 43.1% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o)), args: [(i => (i => ((i => (i => i)) => o))), (i => (i => ((i => (i => i)) => o)))])` | 439 | 4.7% |
| `isaVarApp(head: ((i => (i => ((i => (i => i)) => o))) => o), args: [(i => (i => ((i => (i => i)) => o)))])` | 439 | 4.7% |
| `isaVarApp(head: ((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)), args: [(i => (i => ((i => i) => ((i => i) => (i => o))))), (i => (i => ((i => i) => ((i => i) => (i => o)))))])` | 7 | 0.1% |
| `isaVarApp(head: ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o), args: [(i => (i => ((i => i) => ((i => i) => (i => o)))))])` | 7 | 0.1% |
| `isaVarApp(head: ((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o)), args: [(i => (i => (i => ((i => (i => i)) => i)))), (i => (i => (i => ((i => (i => i)) => i))))])` | 896 | 9.5% |
| `isaVarApp(head: ((i => (i => (i => ((i => (i => i)) => i)))) => o), args: [(i => (i => (i => ((i => (i => i)) => i))))])` | 896 | 9.5% |
| `isaVarApp(head: ((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o)), args: [(i => (i => (i => ((i => i) => o)))), (i => (i => (i => ((i => i) => o))))])` | 21 | 0.2% |
| `isaVarApp(head: ((i => (i => (i => ((i => i) => o)))) => o), args: [(i => (i => (i => ((i => i) => o))))])` | 21 | 0.2% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o)), args: [(i => (i => (i => (i => (i => (i => i)))))), (i => (i => (i => (i => (i => (i => i))))))])` | 35 | 0.4% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => (i => i)))))) => o), args: [(i => (i => (i => (i => (i => (i => i))))))])` | 35 | 0.4% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o)), args: [(i => (i => (i => (i => (i => i))))), (i => (i => (i => (i => (i => i)))))])` | 187 | 2.0% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => i))))) => o), args: [(i => (i => (i => (i => (i => i)))))])` | 187 | 2.0% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o)), args: [(i => (i => (i => (i => (i => o))))), (i => (i => (i => (i => (i => o)))))])` | 9 | 0.1% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)), args: [(i => (i => (i => (i => (i => o))))), (i => (i => (i => (i => i))))])` | 1 | 0.0% |
| `isaVarApp(head: ((i => (i => (i => (i => (i => o))))) => o), args: [(i => (i => (i => (i => (i => o)))))])` | 9 | 0.1% |
| `isaVarApp(head: ((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o)), args: [(i => (i => (i => (i => i)))), (i => (i => (i => (i => i))))])` | 1108 | 11.8% |
| `isaVarApp(head: ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))), args: [(i => (i => (i => (i => i)))), (i => (i => i)), i, i])` | 38 | 0.4% |
| `isaVarApp(head: ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))), args: [(i => (i => (i => (i => i)))), (i => (i => i)), i])` | 24 | 0.3% |
| `isaVarApp(head: ((i => (i => (i => (i => i)))) => o), args: [(i => (i => (i => (i => i))))])` | 1109 | 11.8% |
| `isaVarApp(head: ((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o)), args: [(i => (i => (i => (i => o)))), (i => (i => (i => (i => o))))])` | 114 | 1.2% |
| `isaVarApp(head: ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)), args: [(i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 2 | 0.0% |
| `isaVarApp(head: ((i => (i => (i => (i => o)))) => o), args: [(i => (i => (i => (i => o))))])` | 114 | 1.2% |
| `isaVarApp(head: ((i => (i => (i => i))) => ((i => (i => (i => i))) => o)), args: [(i => (i => (i => i))), (i => (i => (i => i)))])` | 3075 | 32.6% |
| `isaVarApp(head: ((i => (i => (i => i))) => ((i => (i => i)) => (i => i))), args: [(i => (i => (i => i))), (i => (i => i)), i])` | 10 | 0.1% |
| `isaVarApp(head: ((i => (i => (i => i))) => (i => (i => i))), args: [(i => (i => (i => i))), i, i])` | 103 | 1.1% |
| `isaVarApp(head: ((i => (i => (i => i))) => (i => i)), args: [(i => (i => (i => i))), i])` | 1096 | 11.6% |
| `isaVarApp(head: ((i => (i => (i => i))) => i), args: [(i => (i => (i => i)))])` | 25 | 0.3% |
| `isaVarApp(head: ((i => (i => (i => i))) => o), args: [(i => (i => (i => i)))])` | 3077 | 32.7% |
| `isaVarApp(head: ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))), args: [(i => (i => (i => o))), (i => (i => (i => o))), (i => (i => (i => o))), (i => (i => o)), i, i])` | 70 | 0.7% |
| `isaVarApp(head: ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))), args: [(i => (i => (i => o))), (i => (i => (i => o))), (i => (i => o)), i, i])` | 70 | 0.7% |
| `isaVarApp(head: ((i => (i => (i => o))) => ((i => (i => (i => o))) => o)), args: [(i => (i => (i => o))), (i => (i => (i => o)))])` | 284 | 3.0% |
| `isaVarApp(head: ((i => (i => (i => o))) => ((i => (i => i)) => o)), args: [(i => (i => (i => o))), (i => (i => i))])` | 185 | 2.0% |
| `isaVarApp(head: ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))), args: [(i => (i => (i => o))), (i => (i => o)), i, i])` | 70 | 0.7% |
| `isaVarApp(head: ((i => (i => (i => o))) => (i => (i => (i => o)))), args: [(i => (i => (i => o))), i, i, i])` | 318 | 3.4% |
| `isaVarApp(head: ((i => (i => (i => o))) => (i => (i => o))), args: [(i => (i => (i => o))), i, i])` | 149 | 1.6% |
| `isaVarApp(head: ((i => (i => (i => o))) => (i => o)), args: [(i => (i => (i => o))), i])` | 156 | 1.7% |
| `isaVarApp(head: ((i => (i => (i => o))) => o), args: [(i => (i => (i => o)))])` | 284 | 3.0% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))), args: [(i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i, i])` | 38 | 0.4% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))), args: [(i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i])` | 24 | 0.3% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))), args: [(i => (i => i)), (i => (i => (i => i))), (i => (i => i)), i])` | 10 | 0.1% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))), args: [(i => (i => i)), (i => (i => (i => i))), i])` | 37 | 0.4% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), args: [(i => (i => i)), (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i, i])` | 38 | 0.4% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))), args: [(i => (i => i)), (i => (i => i)), (i => (i => (i => (i => i)))), (i => (i => i)), i])` | 24 | 0.3% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))), args: [(i => (i => i)), (i => (i => i)), (i => (i => (i => i))), i])` | 21 | 0.2% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => (i => i))), args: [(i => (i => i)), (i => (i => i)), i])` | 23 | 0.2% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => i)), args: [(i => (i => i)), (i => (i => i))])` | 8 | 0.1% |
| `isaVarApp(head: ((i => (i => i)) => ((i => (i => i)) => o)), args: [(i => (i => i)), (i => (i => i))])` | 6923 | 73.5% |
| `isaVarApp(head: ((i => (i => i)) => ((i => i) => (i => i))), args: [(i => (i => i)), (i => i), i])` | 965 | 10.2% |
| `isaVarApp(head: ((i => (i => i)) => (i => ((i => (i => i)) => (i => i)))), args: [(i => (i => i)), i, (i => (i => i)), i])` | 35 | 0.4% |
| `isaVarApp(head: ((i => (i => i)) => (i => (i => i))), args: [(i => (i => i)), i, i])` | 91 | 1.0% |
| `isaVarApp(head: ((i => (i => i)) => (i => i)), args: [(i => (i => i)), i])` | 2884 | 30.6% |
| `isaVarApp(head: ((i => (i => i)) => (i => o)), args: [(i => (i => i)), i])` | 4068 | 43.2% |
| `isaVarApp(head: ((i => (i => i)) => i), args: [(i => (i => i))])` | 4065 | 43.2% |
| `isaVarApp(head: ((i => (i => i)) => o), args: [(i => (i => i))])` | 6927 | 73.5% |
| `isaVarApp(head: ((i => (i => o)) => ((i => (i => o)) => o)), args: [(i => (i => o)), (i => (i => o))])` | 7387 | 78.4% |
| `isaVarApp(head: ((i => (i => o)) => ((i => i) => o)), args: [(i => (i => o)), (i => i)])` | 132 | 1.4% |
| `isaVarApp(head: ((i => (i => o)) => (i => (i => (i => (i => o))))), args: [(i => (i => o)), i, i, i, i])` | 243 | 2.6% |
| `isaVarApp(head: ((i => (i => o)) => (i => (i => (i => o)))), args: [(i => (i => o)), i, i, i])` | 225 | 2.4% |
| `isaVarApp(head: ((i => (i => o)) => (i => (i => o))), args: [(i => (i => o)), i, i])` | 250 | 2.7% |
| `isaVarApp(head: ((i => (i => o)) => (i => o)), args: [(i => (i => o)), i])` | 344 | 3.7% |
| `isaVarApp(head: ((i => (i => o)) => i), args: [(i => (i => o))])` | 7313 | 77.6% |
| `isaVarApp(head: ((i => (i => o)) => o), args: [(i => (i => o))])` | 7404 | 78.6% |
| `isaVarApp(head: ((i => i) => ((i => (i => (i => i))) => (i => i))), args: [(i => i), (i => (i => (i => i))), i])` | 92 | 1.0% |
| `isaVarApp(head: ((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i)))), args: [(i => i), (i => (i => i)), (i => (i => i)), i])` | 23 | 0.2% |
| `isaVarApp(head: ((i => i) => ((i => i) => (i => i))), args: [(i => i), (i => i), i])` | 2421 | 25.7% |
| `isaVarApp(head: ((i => i) => ((i => i) => (i => o))), args: [(i => i), (i => i), i])` | 7 | 0.1% |
| `isaVarApp(head: ((i => i) => ((i => i) => o)), args: [(i => i), (i => i)])` | 6847 | 72.7% |
| `isaVarApp(head: ((i => i) => (i => (i => i))), args: [(i => i), i, i])` | 442 | 4.7% |
| `isaVarApp(head: ((i => i) => (i => i)), args: [(i => i), i])` | 4223 | 44.8% |
| `isaVarApp(head: ((i => i) => (i => o)), args: [(i => i), i])` | 7 | 0.1% |
| `isaVarApp(head: ((i => i) => i), args: [(i => i)])` | 6229 | 66.1% |
| `isaVarApp(head: ((i => i) => o), args: [(i => i)])` | 6955 | 73.8% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), args: [(i => o), (i => (i => (i => (i => (i => o))))), (i => (i => (i => (i => i))))])` | 1 | 0.0% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), args: [(i => o), (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), args: [(i => o), (i => (i => (i => o))), (i => (i => (i => o))), (i => (i => (i => o))), (i => (i => o)), i, i])` | 70 | 0.7% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), args: [(i => o), (i => (i => (i => o))), (i => (i => i))])` | 183 | 1.9% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), args: [(i => o), (i => (i => (i => o))), i, i, i])` | 318 | 3.4% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), args: [(i => o), (i => (i => (i => o))), i, i])` | 53 | 0.6% |
| `isaVarApp(head: ((i => o) => ((i => (i => (i => o))) => (i => o))), args: [(i => o), (i => (i => (i => o))), i])` | 155 | 1.6% |
| `isaVarApp(head: ((i => o) => ((i => (i => o)) => ((i => i) => o))), args: [(i => o), (i => (i => o)), (i => i)])` | 128 | 1.4% |
| `isaVarApp(head: ((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), args: [(i => o), (i => (i => o)), i, i, i, i])` | 243 | 2.6% |
| `isaVarApp(head: ((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), args: [(i => o), (i => (i => o)), i, i, i])` | 225 | 2.4% |
| `isaVarApp(head: ((i => o) => ((i => (i => o)) => (i => o))), args: [(i => o), (i => (i => o)), i])` | 141 | 1.5% |
| `isaVarApp(head: ((i => o) => ((i => (i => o)) => o)), args: [(i => o), (i => (i => o))])` | 597 | 6.3% |
| `isaVarApp(head: ((i => o) => ((i => o) => ((i => (i => o)) => o))), args: [(i => o), (i => o), (i => (i => o))])` | 429 | 4.6% |
| `isaVarApp(head: ((i => o) => ((i => o) => o)), args: [(i => o), (i => o)])` | 5453 | 57.9% |
| `isaVarApp(head: ((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), args: [(i => o), i, (i => (i => (i => o))), i, i])` | 3 | 0.0% |
| `isaVarApp(head: ((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), args: [(i => o), i, (i => (i => o)), (i => i)])` | 44 | 0.5% |
| `isaVarApp(head: ((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), args: [(i => o), i, (i => (i => o)), i, i])` | 249 | 2.6% |
| `isaVarApp(head: ((i => o) => (i => ((i => (i => o)) => (i => o)))), args: [(i => o), i, (i => (i => o)), i])` | 96 | 1.0% |
| `isaVarApp(head: ((i => o) => (i => ((i => (i => o)) => o))), args: [(i => o), i, (i => (i => o))])` | 374 | 4.0% |
| `isaVarApp(head: ((i => o) => (i => ((i => o) => (i => o)))), args: [(i => o), i, (i => o), i])` | 46 | 0.5% |
| `isaVarApp(head: ((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), args: [(i => o), i, i, (i => (i => (i => o))), (i => (i => i))])` | 41 | 0.4% |
| `isaVarApp(head: ((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), args: [(i => o), i, i, i, (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaVarApp(head: ((i => o) => (i => (i => (i => (i => (i => o)))))), args: [(i => o), i, i, i, i, i])` | 89 | 0.9% |
| `isaVarApp(head: ((i => o) => (i => (i => (i => (i => o))))), args: [(i => o), i, i, i, i])` | 225 | 2.4% |
| `isaVarApp(head: ((i => o) => (i => (i => (i => o)))), args: [(i => o), i, i, i])` | 1026 | 10.9% |
| `isaVarApp(head: ((i => o) => (i => (i => i))), args: [(i => o), i, i])` | 44 | 0.5% |
| `isaVarApp(head: ((i => o) => (i => (i => o))), args: [(i => o), i, i])` | 946 | 10.0% |
| `isaVarApp(head: ((i => o) => (i => i)), args: [(i => o), i])` | 445 | 4.7% |
| `isaVarApp(head: ((i => o) => (i => o)), args: [(i => o), i])` | 838 | 8.9% |
| `isaVarApp(head: ((i => o) => (o => (i => o))), args: [(i => o), o, i])` | 92 | 1.0% |
| `isaVarApp(head: ((i => o) => i), args: [(i => o)])` | 7257 | 77.0% |
| `isaVarApp(head: ((i => o) => o), args: [(i => o)])` | 7746 | 82.2% |
| `isaVarApp(head: ((o => (i => (i => i))) => ((o => (i => (i => i))) => o)), args: [(o => (i => (i => i))), (o => (i => (i => i)))])` | 5018 | 53.3% |
| `isaVarApp(head: ((o => (i => (i => i))) => o), args: [(o => (i => (i => i)))])` | 5018 | 53.3% |
| `isaVarApp(head: ((o => (o => o)) => ((o => (o => o)) => o)), args: [(o => (o => o)), (o => (o => o))])` | 7841 | 83.2% |
| `isaVarApp(head: ((o => (o => o)) => o), args: [(o => (o => o))])` | 7841 | 83.2% |
| `isaVarApp(head: ((o => i) => ((o => i) => o)), args: [(o => i), (o => i)])` | 882 | 9.4% |
| `isaVarApp(head: ((o => i) => o), args: [(o => i)])` | 882 | 9.4% |
| `isaVarApp(head: ((o => o) => ((o => o) => o)), args: [(o => o), (o => o)])` | 7819 | 83.0% |
| `isaVarApp(head: ((o => o) => o), args: [(o => o)])` | 7819 | 83.0% |
| `isaVarApp(head: (i => 'a), args: [i])` | 2773 | 29.4% |
| `isaVarApp(head: (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), args: [i, (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaVarApp(head: (i => ((i => (i => (i => i))) => i)), args: [i, (i => (i => (i => i)))])` | 25 | 0.3% |
| `isaVarApp(head: (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))), args: [i, (i => (i => (i => o))), (i => (i => i))])` | 41 | 0.4% |
| `isaVarApp(head: (i => ((i => (i => (i => o))) => (i => (i => o)))), args: [i, (i => (i => (i => o))), i, i])` | 3 | 0.0% |
| `isaVarApp(head: (i => ((i => (i => i)) => ((i => (i => i)) => i))), args: [i, (i => (i => i)), (i => (i => i))])` | 8 | 0.1% |
| `isaVarApp(head: (i => ((i => (i => i)) => (i => (i => i)))), args: [i, (i => (i => i)), i, i])` | 53 | 0.6% |
| `isaVarApp(head: (i => ((i => (i => i)) => (i => i))), args: [i, (i => (i => i)), i])` | 2100 | 22.3% |
| `isaVarApp(head: (i => ((i => (i => i)) => (i => o))), args: [i, (i => (i => i)), i])` | 4068 | 43.2% |
| `isaVarApp(head: (i => ((i => (i => i)) => i)), args: [i, (i => (i => i))])` | 4064 | 43.1% |
| `isaVarApp(head: (i => ((i => (i => i)) => o)), args: [i, (i => (i => i))])` | 439 | 4.7% |
| `isaVarApp(head: (i => ((i => (i => o)) => ((i => i) => o))), args: [i, (i => (i => o)), (i => i)])` | 44 | 0.5% |
| `isaVarApp(head: (i => ((i => (i => o)) => (i => (i => o)))), args: [i, (i => (i => o)), i, i])` | 249 | 2.6% |
| `isaVarApp(head: (i => ((i => (i => o)) => (i => o))), args: [i, (i => (i => o)), i])` | 96 | 1.0% |
| `isaVarApp(head: (i => ((i => (i => o)) => i)), args: [i, (i => (i => o))])` | 7313 | 77.6% |
| `isaVarApp(head: (i => ((i => (i => o)) => o)), args: [i, (i => (i => o))])` | 374 | 4.0% |
| `isaVarApp(head: (i => ((i => i) => ((i => i) => (i => o)))), args: [i, (i => i), (i => i), i])` | 7 | 0.1% |
| `isaVarApp(head: (i => ((i => i) => (i => i))), args: [i, (i => i), i])` | 3854 | 40.9% |
| `isaVarApp(head: (i => ((i => i) => i)), args: [i, (i => i)])` | 6226 | 66.1% |
| `isaVarApp(head: (i => ((i => i) => o)), args: [i, (i => i)])` | 4845 | 51.4% |
| `isaVarApp(head: (i => ((i => o) => (i => o))), args: [i, (i => o), i])` | 46 | 0.5% |
| `isaVarApp(head: (i => ((i => o) => i)), args: [i, (i => o)])` | 7247 | 76.9% |
| `isaVarApp(head: (i => ((i => o) => o)), args: [i, (i => o)])` | 7494 | 79.6% |
| `isaVarApp(head: (i => (i => 'a)), args: [i, i])` | 3299 | 35.0% |
| `isaVarApp(head: (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))), args: [i, i, (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaVarApp(head: (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))), args: [i, i, (i => (i => (i => o))), (i => (i => i))])` | 41 | 0.4% |
| `isaVarApp(head: (i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), args: [i, i, (i => (i => i)), (i => (i => i))])` | 8 | 0.1% |
| `isaVarApp(head: (i => (i => ((i => (i => i)) => (i => i)))), args: [i, i, (i => (i => i)), i])` | 13 | 0.1% |
| `isaVarApp(head: (i => (i => ((i => (i => i)) => (i => o)))), args: [i, i, (i => (i => i)), i])` | 4068 | 43.2% |
| `isaVarApp(head: (i => (i => ((i => (i => i)) => i))), args: [i, i, (i => (i => i))])` | 4062 | 43.1% |
| `isaVarApp(head: (i => (i => ((i => (i => i)) => o))), args: [i, i, (i => (i => i))])` | 439 | 4.7% |
| `isaVarApp(head: (i => (i => ((i => i) => ((i => i) => (i => o))))), args: [i, i, (i => i), (i => i), i])` | 7 | 0.1% |
| `isaVarApp(head: (i => (i => ((i => i) => o))), args: [i, i, (i => i)])` | 21 | 0.2% |
| `isaVarApp(head: (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))), args: [i, i, i, (i => (i => (i => (i => o)))), (i => (i => (i => i)))])` | 1 | 0.0% |
| `isaVarApp(head: (i => (i => (i => ((i => (i => i)) => i)))), args: [i, i, i, (i => (i => i))])` | 896 | 9.5% |
| `isaVarApp(head: (i => (i => (i => ((i => i) => o)))), args: [i, i, i, (i => i)])` | 21 | 0.2% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i)))))))))))))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i])` | 10 | 0.1% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i])` | 185 | 2.0% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i, i, i, i, i])` | 10 | 0.1% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i)))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i, i])` | 14 | 0.1% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => (i => i))))))))))), args: [i, i, i, i, i, i, i, i, i, i, i])` | 16 | 0.2% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => (i => i)))))))), args: [i, i, i, i, i, i, i, i])` | 2 | 0.0% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => (i => i))))))), args: [i, i, i, i, i, i, i])` | 16 | 0.2% |
| `isaVarApp(head: (i => (i => (i => (i => (i => (i => i)))))), args: [i, i, i, i, i, i])` | 4125 | 43.8% |
| `isaVarApp(head: (i => (i => (i => (i => (i => i))))), args: [i, i, i, i, i])` | 1646 | 17.5% |
| `isaVarApp(head: (i => (i => (i => (i => (i => o))))), args: [i, i, i, i, i])` | 99 | 1.1% |
| `isaVarApp(head: (i => (i => (i => (i => i)))), args: [i, i, i, i])` | 4580 | 48.6% |
| `isaVarApp(head: (i => (i => (i => (i => o)))), args: [i, i, i, i])` | 435 | 4.6% |
| `isaVarApp(head: (i => (i => (i => i))), args: [i, i, i])` | 5745 | 61.0% |
| `isaVarApp(head: (i => (i => (i => o))), args: [i, i, i])` | 1561 | 16.6% |
| `isaVarApp(head: (i => (i => i)), args: [i, i])` | 7752 | 82.3% |
| `isaVarApp(head: (i => (i => o)), args: [i, i])` | 9170 | 97.3% |
| `isaVarApp(head: (i => i), args: [i])` | 8261 | 87.7% |
| `isaVarApp(head: (i => o), args: [i])` | 8838 | 93.8% |
| `isaVarApp(head: (o => 'a), args: [o])` | 7417 | 78.7% |
| `isaVarApp(head: (o => (('a => o) => 'a)), args: [o, ('a => o)])` | 7290 | 77.4% |
| `isaVarApp(head: (o => (i => (i => i))), args: [o, i, i])` | 5020 | 53.3% |
| `isaVarApp(head: (o => (i => o)), args: [o, i])` | 92 | 1.0% |
| `isaVarApp(head: (o => (o => o)), args: [o, o])` | 8323 | 88.4% |
| `isaVarApp(head: (o => i), args: [o])` | 883 | 9.4% |
| `isaVarApp(head: (o => o), args: [o])` | 8432 | 89.5% |
| `use(axiom AC.AC, [], o)` | 51 | 0.5% |
| `use(axiom FOL.classical, [], o)` | 7756 | 82.3% |
| `use(axiom IFOL.FalseE, [], o)` | 7820 | 83.0% |
| `use(axiom IFOL.allI, ['a], o)` | 7610 | 80.8% |
| `use(axiom IFOL.conjI, [], o)` | 8042 | 85.4% |
| `use(axiom IFOL.conjunct1, [], o)` | 7893 | 83.8% |
| `use(axiom IFOL.conjunct2, [], o)` | 7759 | 82.4% |
| `use(axiom IFOL.disjE, [], o)` | 7496 | 79.6% |
| `use(axiom IFOL.disjI1, [], o)` | 7496 | 79.6% |
| `use(axiom IFOL.disjI2, [], o)` | 7496 | 79.6% |
| `use(axiom IFOL.eq_reflection, ['a], o)` | 7751 | 82.3% |
| `use(axiom IFOL.exE, ['a], o)` | 7495 | 79.6% |
| `use(axiom IFOL.exI, ['a], o)` | 7497 | 79.6% |
| `use(axiom IFOL.iff_reflection, [], o)` | 7572 | 80.4% |
| `use(axiom IFOL.impI, [], o)` | 8047 | 85.4% |
| `use(axiom IFOL.mp, [], o)` | 7960 | 84.5% |
| `use(axiom IFOL.refl, ['a], o)` | 7767 | 82.5% |
| `use(axiom IFOL.spec, ['a], o)` | 7668 | 81.4% |
| `use(axiom IFOL.subst, ['a], o)` | 7607 | 80.8% |
| `use(axiom Pure.abstract_rule, ['a, o], o)` | 3067 | 32.6% |
| `use(axiom Pure.abstract_rule, [(i => (i => o)), o], o)` | 429 | 4.6% |
| `use(axiom Pure.abstract_rule, [(i => o), ((i => (i => o)) => o)], o)` | 429 | 4.6% |
| `use(axiom Pure.abstract_rule, [(i => o), ((i => o) => ((i => (i => o)) => o))], o)` | 429 | 4.6% |
| `use(axiom Pure.abstract_rule, [(i => o), (i => (i => (i => (i => o))))], o)` | 26 | 0.3% |
| `use(axiom Pure.abstract_rule, [(i => o), (i => i)], o)` | 436 | 4.6% |
| `use(axiom Pure.abstract_rule, [(i => o), (i => o)], o)` | 430 | 4.6% |
| `use(axiom Pure.abstract_rule, [(i => o), o], o)` | 435 | 4.6% |
| `use(axiom Pure.abstract_rule, [i, (i => (i => (i => o)))], o)` | 26 | 0.3% |
| `use(axiom Pure.abstract_rule, [i, (i => (i => i))], o)` | 1205 | 12.8% |
| `use(axiom Pure.abstract_rule, [i, (i => (i => o))], o)` | 156 | 1.7% |
| `use(axiom Pure.abstract_rule, [i, (i => i)], o)` | 3034 | 32.2% |
| `use(axiom Pure.abstract_rule, [i, (i => o)], o)` | 654 | 6.9% |
| `use(axiom Pure.abstract_rule, [i, i], o)` | 4562 | 48.4% |
| `use(axiom Pure.abstract_rule, [i, o], o)` | 7626 | 81.0% |
| `use(axiom Pure.combination, ['a, 'b], o)` | 4626 | 49.1% |
| `use(axiom Pure.combination, ['a, ('a => o)], o)` | 7578 | 80.4% |
| `use(axiom Pure.combination, ['a, o], o)` | 7724 | 82.0% |
| `use(axiom Pure.combination, ['b, ('b => o)], o)` | 4626 | 49.1% |
| `use(axiom Pure.combination, ['b, (('b => 'a) => 'a)], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, ['b, o], o)` | 4626 | 49.1% |
| `use(axiom Pure.combination, [('a => o), o], o)` | 7324 | 77.7% |
| `use(axiom Pure.combination, [('b => 'a), 'a], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [('b => (('b => 'a) => 'a)), (('b => (('b => 'a) => 'a)) => o)], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [('b => (('b => 'a) => 'a)), o], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [(('a => o) => o), ((('a => o) => o) => o)], o)` | 7323 | 77.7% |
| `use(axiom Pure.combination, [(('a => o) => o), o], o)` | 7323 | 77.7% |
| `use(axiom Pure.combination, [((i => (i => 'a)) => (i => 'a)), (((i => (i => 'a)) => (i => 'a)) => o)], o)` | 2773 | 29.4% |
| `use(axiom Pure.combination, [((i => (i => 'a)) => (i => 'a)), o], o)` | 2773 | 29.4% |
| `use(axiom Pure.combination, [((i => (i => (i => i))) => (i => i)), (((i => (i => (i => i))) => (i => i)) => o)], o)` | 4 | 0.0% |
| `use(axiom Pure.combination, [((i => (i => (i => i))) => (i => i)), o], o)` | 4 | 0.0% |
| `use(axiom Pure.combination, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o)], o)` | 38 | 0.4% |
| `use(axiom Pure.combination, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))), o], o)` | 38 | 0.4% |
| `use(axiom Pure.combination, [((i => (i => i)) => (i => i)), (((i => (i => i)) => (i => i)) => o)], o)` | 2760 | 29.3% |
| `use(axiom Pure.combination, [((i => (i => i)) => (i => i)), o], o)` | 2760 | 29.3% |
| `use(axiom Pure.combination, [((i => i) => ((i => i) => (i => i))), (((i => i) => ((i => i) => (i => i))) => o)], o)` | 2421 | 25.7% |
| `use(axiom Pure.combination, [((i => i) => ((i => i) => (i => i))), o], o)` | 2421 | 25.7% |
| `use(axiom Pure.combination, [((i => i) => (i => i)), (((i => i) => (i => i)) => o)], o)` | 514 | 5.5% |
| `use(axiom Pure.combination, [((i => i) => (i => i)), o], o)` | 514 | 5.5% |
| `use(axiom Pure.combination, [((i => i) => o), (((i => i) => o) => o)], o)` | 531 | 5.6% |
| `use(axiom Pure.combination, [((i => i) => o), o], o)` | 531 | 5.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o)], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))), o], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o)], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))), o], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o)], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))), o], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o)], o)` | 183 | 1.9% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))), o], o)` | 183 | 1.9% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o)], o)` | 318 | 3.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))), o], o)` | 318 | 3.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o)], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => (i => o)))), o], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => o))), (((i => o) => ((i => (i => (i => o))) => (i => o))) => o)], o)` | 155 | 1.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => (i => o))) => (i => o))), o], o)` | 155 | 1.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => ((i => i) => o))), (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o)], o)` | 128 | 1.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => ((i => i) => o))), o], o)` | 128 | 1.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o)], o)` | 243 | 2.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))), o], o)` | 243 | 2.6% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o)], o)` | 225 | 2.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => (i => (i => o))))), o], o)` | 225 | 2.4% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => o))), (((i => o) => ((i => (i => o)) => (i => o))) => o)], o)` | 141 | 1.5% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => (i => o))), o], o)` | 141 | 1.5% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => o)), (((i => o) => ((i => (i => o)) => o)) => o)], o)` | 585 | 6.2% |
| `use(axiom Pure.combination, [((i => o) => ((i => (i => o)) => o)), o], o)` | 585 | 6.2% |
| `use(axiom Pure.combination, [((i => o) => ((i => o) => o)), (((i => o) => ((i => o) => o)) => o)], o)` | 1163 | 12.3% |
| `use(axiom Pure.combination, [((i => o) => ((i => o) => o)), o], o)` | 1163 | 12.3% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o)], o)` | 3 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))), o], o)` | 3 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o)], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))), o], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o)], o)` | 249 | 2.6% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => (i => (i => o))))), o], o)` | 249 | 2.6% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => (i => o)))), (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o)], o)` | 96 | 1.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => (i => o)))), o], o)` | 96 | 1.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => o))), (((i => o) => (i => ((i => (i => o)) => o))) => o)], o)` | 374 | 4.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => (i => o)) => o))), o], o)` | 374 | 4.0% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => o) => (i => o)))), (((i => o) => (i => ((i => o) => (i => o)))) => o)], o)` | 46 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => ((i => o) => (i => o)))), o], o)` | 46 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o)], o)` | 41 | 0.4% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))), o], o)` | 41 | 0.4% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o)], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))), o], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => (i => (i => o)))))), (((i => o) => (i => (i => (i => (i => (i => o)))))) => o)], o)` | 89 | 0.9% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => (i => (i => o)))))), o], o)` | 89 | 0.9% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => (i => o))))), (((i => o) => (i => (i => (i => (i => o))))) => o)], o)` | 117 | 1.2% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => (i => o))))), o], o)` | 117 | 1.2% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => o)))), (((i => o) => (i => (i => (i => o)))) => o)], o)` | 1025 | 10.9% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => (i => o)))), o], o)` | 1025 | 10.9% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => i))), (((i => o) => (i => (i => i))) => o)], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => i))), o], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => o))), (((i => o) => (i => (i => o))) => o)], o)` | 945 | 10.0% |
| `use(axiom Pure.combination, [((i => o) => (i => (i => o))), o], o)` | 945 | 10.0% |
| `use(axiom Pure.combination, [((i => o) => (i => i)), (((i => o) => (i => i)) => o)], o)` | 2 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => i)), o], o)` | 2 | 0.0% |
| `use(axiom Pure.combination, [((i => o) => (i => o)), (((i => o) => (i => o)) => o)], o)` | 670 | 7.1% |
| `use(axiom Pure.combination, [((i => o) => (i => o)), o], o)` | 670 | 7.1% |
| `use(axiom Pure.combination, [((i => o) => (o => (i => o))), (((i => o) => (o => (i => o))) => o)], o)` | 92 | 1.0% |
| `use(axiom Pure.combination, [((i => o) => (o => (i => o))), o], o)` | 92 | 1.0% |
| `use(axiom Pure.combination, [((i => o) => i), (((i => o) => i) => o)], o)` | 5274 | 56.0% |
| `use(axiom Pure.combination, [((i => o) => i), o], o)` | 5274 | 56.0% |
| `use(axiom Pure.combination, [((i => o) => o), (((i => o) => o) => o)], o)` | 4100 | 43.5% |
| `use(axiom Pure.combination, [((i => o) => o), o], o)` | 4102 | 43.5% |
| `use(axiom Pure.combination, [(i => 'a), ((i => 'a) => o)], o)` | 2739 | 29.1% |
| `use(axiom Pure.combination, [(i => 'a), o], o)` | 2739 | 29.1% |
| `use(axiom Pure.combination, [(i => ((i => (i => (i => i))) => i)), ((i => ((i => (i => (i => i))) => i)) => o)], o)` | 25 | 0.3% |
| `use(axiom Pure.combination, [(i => ((i => (i => (i => i))) => i)), o], o)` | 25 | 0.3% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => (i => (i => i)))), ((i => ((i => (i => i)) => (i => (i => i)))) => o)], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => (i => (i => i)))), o], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => (i => i))), ((i => ((i => (i => i)) => (i => i))) => o)], o)` | 2044 | 21.7% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => (i => i))), o], o)` | 2044 | 21.7% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => i)), ((i => ((i => (i => i)) => i)) => o)], o)` | 3706 | 39.3% |
| `use(axiom Pure.combination, [(i => ((i => (i => i)) => i)), o], o)` | 3706 | 39.3% |
| `use(axiom Pure.combination, [(i => ((i => (i => o)) => i)), ((i => ((i => (i => o)) => i)) => o)], o)` | 7313 | 77.6% |
| `use(axiom Pure.combination, [(i => ((i => (i => o)) => i)), o], o)` | 7313 | 77.6% |
| `use(axiom Pure.combination, [(i => ((i => i) => (i => i))), ((i => ((i => i) => (i => i))) => o)], o)` | 3854 | 40.9% |
| `use(axiom Pure.combination, [(i => ((i => i) => (i => i))), o], o)` | 3854 | 40.9% |
| `use(axiom Pure.combination, [(i => ((i => i) => i)), ((i => ((i => i) => i)) => o)], o)` | 6215 | 66.0% |
| `use(axiom Pure.combination, [(i => ((i => i) => i)), o], o)` | 6215 | 66.0% |
| `use(axiom Pure.combination, [(i => ((i => i) => o)), ((i => ((i => i) => o)) => o)], o)` | 4841 | 51.4% |
| `use(axiom Pure.combination, [(i => ((i => i) => o)), o], o)` | 4841 | 51.4% |
| `use(axiom Pure.combination, [(i => ((i => o) => i)), ((i => ((i => o) => i)) => o)], o)` | 7247 | 76.9% |
| `use(axiom Pure.combination, [(i => ((i => o) => i)), o], o)` | 7247 | 76.9% |
| `use(axiom Pure.combination, [(i => ((i => o) => o)), ((i => ((i => o) => o)) => o)], o)` | 7493 | 79.5% |
| `use(axiom Pure.combination, [(i => ((i => o) => o)), o], o)` | 7493 | 79.5% |
| `use(axiom Pure.combination, [(i => (i => 'a)), (i => 'a)], o)` | 2773 | 29.4% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o)], o)` | 8 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))), o], o)` | 8 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => (i => o)))), ((i => (i => ((i => (i => i)) => (i => o)))) => o)], o)` | 4068 | 43.2% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => (i => o)))), o], o)` | 4068 | 43.2% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => i))), ((i => (i => ((i => (i => i)) => i))) => o)], o)` | 4061 | 43.1% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => i))), o], o)` | 4061 | 43.1% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => o))), ((i => (i => ((i => (i => i)) => o))) => o)], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [(i => (i => ((i => (i => i)) => o))), o], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [(i => (i => ((i => i) => ((i => i) => (i => o))))), ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o)], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => ((i => i) => ((i => i) => (i => o))))), o], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => (i => ((i => (i => i)) => i)))), ((i => (i => (i => ((i => (i => i)) => i)))) => o)], o)` | 896 | 9.5% |
| `use(axiom Pure.combination, [(i => (i => (i => ((i => (i => i)) => i)))), o], o)` | 896 | 9.5% |
| `use(axiom Pure.combination, [(i => (i => (i => ((i => i) => o)))), ((i => (i => (i => ((i => i) => o)))) => o)], o)` | 21 | 0.2% |
| `use(axiom Pure.combination, [(i => (i => (i => ((i => i) => o)))), o], o)` | 21 | 0.2% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => (i => i)))))), ((i => (i => (i => (i => (i => (i => i)))))) => o)], o)` | 35 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => (i => i)))))), o], o)` | 35 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => i))))), ((i => (i => (i => (i => (i => i))))) => o)], o)` | 187 | 2.0% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => i))))), o], o)` | 187 | 2.0% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => o))))), ((i => (i => (i => (i => (i => o))))) => o)], o)` | 9 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => o))))), ((i => (i => (i => (i => i)))) => o)], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => (i => o))))), o], o)` | 9 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => i)))), ((i => (i => (i => (i => i)))) => o)], o)` | 1108 | 11.8% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => i)))), ((i => (i => i)) => (i => (i => i)))], o)` | 38 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => i)))), ((i => (i => i)) => (i => i))], o)` | 24 | 0.3% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => i)))), o], o)` | 1109 | 11.8% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => o)))), ((i => (i => (i => (i => o)))) => o)], o)` | 114 | 1.2% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => o)))), ((i => (i => (i => i))) => o)], o)` | 2 | 0.0% |
| `use(axiom Pure.combination, [(i => (i => (i => (i => o)))), o], o)` | 114 | 1.2% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), ((i => (i => (i => i))) => o)], o)` | 3075 | 32.6% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), ((i => (i => i)) => (i => i))], o)` | 10 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), (i => (i => i))], o)` | 103 | 1.1% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), (i => i)], o)` | 1096 | 11.6% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), i], o)` | 25 | 0.3% |
| `use(axiom Pure.combination, [(i => (i => (i => i))), o], o)` | 3077 | 32.7% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), ((i => (i => (i => o))) => o)], o)` | 284 | 3.0% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), ((i => (i => i)) => o)], o)` | 185 | 2.0% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), ((i => (i => o)) => (i => (i => o)))], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), (i => (i => (i => o)))], o)` | 318 | 3.4% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), (i => (i => o))], o)` | 149 | 1.6% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), (i => o)], o)` | 156 | 1.7% |
| `use(axiom Pure.combination, [(i => (i => (i => o))), o], o)` | 284 | 3.0% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))], o)` | 38 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))], o)` | 24 | 0.3% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => (i => i))) => ((i => (i => i)) => (i => i)))], o)` | 10 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => (i => i))) => (i => i))], o)` | 37 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))], o)` | 38 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i))))], o)` | 24 | 0.3% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))], o)` | 21 | 0.2% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => (i => i))], o)` | 23 | 0.2% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => i)], o)` | 8 | 0.1% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => (i => i)) => o)], o)` | 6923 | 73.5% |
| `use(axiom Pure.combination, [(i => (i => i)), ((i => i) => (i => i))], o)` | 965 | 10.2% |
| `use(axiom Pure.combination, [(i => (i => i)), (i => ((i => (i => i)) => (i => i)))], o)` | 35 | 0.4% |
| `use(axiom Pure.combination, [(i => (i => i)), (i => (i => i))], o)` | 91 | 1.0% |
| `use(axiom Pure.combination, [(i => (i => i)), (i => i)], o)` | 2884 | 30.6% |
| `use(axiom Pure.combination, [(i => (i => i)), (i => o)], o)` | 4068 | 43.2% |
| `use(axiom Pure.combination, [(i => (i => i)), i], o)` | 4065 | 43.2% |
| `use(axiom Pure.combination, [(i => (i => i)), o], o)` | 6927 | 73.5% |
| `use(axiom Pure.combination, [(i => (i => o)), ((i => (i => o)) => o)], o)` | 7387 | 78.4% |
| `use(axiom Pure.combination, [(i => (i => o)), ((i => i) => o)], o)` | 132 | 1.4% |
| `use(axiom Pure.combination, [(i => (i => o)), (i => (i => (i => (i => o))))], o)` | 243 | 2.6% |
| `use(axiom Pure.combination, [(i => (i => o)), (i => (i => (i => o)))], o)` | 225 | 2.4% |
| `use(axiom Pure.combination, [(i => (i => o)), (i => (i => o))], o)` | 250 | 2.7% |
| `use(axiom Pure.combination, [(i => (i => o)), (i => o)], o)` | 344 | 3.7% |
| `use(axiom Pure.combination, [(i => (i => o)), i], o)` | 7313 | 77.6% |
| `use(axiom Pure.combination, [(i => (i => o)), o], o)` | 7404 | 78.6% |
| `use(axiom Pure.combination, [(i => i), ((i => (i => (i => i))) => (i => i))], o)` | 92 | 1.0% |
| `use(axiom Pure.combination, [(i => i), ((i => (i => i)) => ((i => (i => i)) => (i => i)))], o)` | 23 | 0.2% |
| `use(axiom Pure.combination, [(i => i), ((i => i) => (i => i))], o)` | 2421 | 25.7% |
| `use(axiom Pure.combination, [(i => i), ((i => i) => (i => o))], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [(i => i), ((i => i) => o)], o)` | 6847 | 72.7% |
| `use(axiom Pure.combination, [(i => i), (i => (i => i))], o)` | 442 | 4.7% |
| `use(axiom Pure.combination, [(i => i), (i => i)], o)` | 4223 | 44.8% |
| `use(axiom Pure.combination, [(i => i), (i => o)], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [(i => i), i], o)` | 6229 | 66.1% |
| `use(axiom Pure.combination, [(i => i), o], o)` | 6955 | 73.8% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))], o)` | 70 | 0.7% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => o))) => ((i => (i => i)) => o))], o)` | 183 | 1.9% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => o))) => (i => (i => (i => o))))], o)` | 318 | 3.4% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => o))) => (i => (i => o)))], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => (i => o))) => (i => o))], o)` | 155 | 1.6% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => o)) => ((i => i) => o))], o)` | 128 | 1.4% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => o)) => (i => (i => (i => (i => o)))))], o)` | 243 | 2.6% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => o)) => (i => (i => (i => o))))], o)` | 225 | 2.4% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => o)) => (i => o))], o)` | 141 | 1.5% |
| `use(axiom Pure.combination, [(i => o), ((i => (i => o)) => o)], o)` | 597 | 6.3% |
| `use(axiom Pure.combination, [(i => o), ((i => o) => ((i => (i => o)) => o))], o)` | 429 | 4.6% |
| `use(axiom Pure.combination, [(i => o), ((i => o) => o)], o)` | 5453 | 57.9% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => (i => (i => o))) => (i => (i => o))))], o)` | 3 | 0.0% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => (i => o)) => ((i => i) => o)))], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => (i => o)) => (i => (i => o))))], o)` | 249 | 2.6% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => (i => o)) => (i => o)))], o)` | 96 | 1.0% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => (i => o)) => o))], o)` | 374 | 4.0% |
| `use(axiom Pure.combination, [(i => o), (i => ((i => o) => (i => o)))], o)` | 46 | 0.5% |
| `use(axiom Pure.combination, [(i => o), (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))], o)` | 41 | 0.4% |
| `use(axiom Pure.combination, [(i => o), (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [(i => o), (i => (i => (i => (i => (i => o)))))], o)` | 89 | 0.9% |
| `use(axiom Pure.combination, [(i => o), (i => (i => (i => (i => o))))], o)` | 116 | 1.2% |
| `use(axiom Pure.combination, [(i => o), (i => (i => (i => o)))], o)` | 1025 | 10.9% |
| `use(axiom Pure.combination, [(i => o), (i => (i => i))], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [(i => o), (i => (i => o))], o)` | 945 | 10.0% |
| `use(axiom Pure.combination, [(i => o), (i => i)], o)` | 445 | 4.7% |
| `use(axiom Pure.combination, [(i => o), (i => o)], o)` | 838 | 8.9% |
| `use(axiom Pure.combination, [(i => o), (o => (i => o))], o)` | 92 | 1.0% |
| `use(axiom Pure.combination, [(i => o), i], o)` | 7257 | 77.0% |
| `use(axiom Pure.combination, [(i => o), o], o)` | 7746 | 82.2% |
| `use(axiom Pure.combination, [(o => (i => (i => i))), ((o => (i => (i => i))) => o)], o)` | 5018 | 53.3% |
| `use(axiom Pure.combination, [(o => (i => (i => i))), o], o)` | 5018 | 53.3% |
| `use(axiom Pure.combination, [(o => (o => o)), ((o => (o => o)) => o)], o)` | 7841 | 83.2% |
| `use(axiom Pure.combination, [(o => (o => o)), o], o)` | 7841 | 83.2% |
| `use(axiom Pure.combination, [(o => i), ((o => i) => o)], o)` | 882 | 9.4% |
| `use(axiom Pure.combination, [(o => i), o], o)` | 882 | 9.4% |
| `use(axiom Pure.combination, [(o => o), ((o => o) => o)], o)` | 7819 | 83.0% |
| `use(axiom Pure.combination, [(o => o), o], o)` | 7819 | 83.0% |
| `use(axiom Pure.combination, [i, 'a], o)` | 1905 | 20.2% |
| `use(axiom Pure.combination, [i, ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [i, ((i => (i => (i => i))) => i)], o)` | 25 | 0.3% |
| `use(axiom Pure.combination, [i, ((i => (i => (i => o))) => ((i => (i => i)) => o))], o)` | 41 | 0.4% |
| `use(axiom Pure.combination, [i, ((i => (i => (i => o))) => (i => (i => o)))], o)` | 3 | 0.0% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => ((i => (i => i)) => i))], o)` | 8 | 0.1% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => (i => (i => i)))], o)` | 53 | 0.6% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => (i => i))], o)` | 2100 | 22.3% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => (i => o))], o)` | 4068 | 43.2% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => i)], o)` | 4064 | 43.1% |
| `use(axiom Pure.combination, [i, ((i => (i => i)) => o)], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [i, ((i => (i => o)) => ((i => i) => o))], o)` | 44 | 0.5% |
| `use(axiom Pure.combination, [i, ((i => (i => o)) => (i => (i => o)))], o)` | 249 | 2.6% |
| `use(axiom Pure.combination, [i, ((i => (i => o)) => (i => o))], o)` | 96 | 1.0% |
| `use(axiom Pure.combination, [i, ((i => (i => o)) => i)], o)` | 7313 | 77.6% |
| `use(axiom Pure.combination, [i, ((i => (i => o)) => o)], o)` | 374 | 4.0% |
| `use(axiom Pure.combination, [i, ((i => i) => ((i => i) => (i => o)))], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [i, ((i => i) => (i => i))], o)` | 3854 | 40.9% |
| `use(axiom Pure.combination, [i, ((i => i) => i)], o)` | 6226 | 66.1% |
| `use(axiom Pure.combination, [i, ((i => i) => o)], o)` | 4845 | 51.4% |
| `use(axiom Pure.combination, [i, ((i => o) => (i => o))], o)` | 46 | 0.5% |
| `use(axiom Pure.combination, [i, ((i => o) => i)], o)` | 7247 | 76.9% |
| `use(axiom Pure.combination, [i, ((i => o) => o)], o)` | 7494 | 79.6% |
| `use(axiom Pure.combination, [i, (i => 'a)], o)` | 1879 | 19.9% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))], o)` | 41 | 0.4% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => i)) => ((i => (i => i)) => i)))], o)` | 8 | 0.1% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => i)) => (i => i)))], o)` | 13 | 0.1% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => i)) => (i => o)))], o)` | 4068 | 43.2% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => i)) => i))], o)` | 4062 | 43.1% |
| `use(axiom Pure.combination, [i, (i => ((i => (i => i)) => o))], o)` | 439 | 4.7% |
| `use(axiom Pure.combination, [i, (i => ((i => i) => ((i => i) => (i => o))))], o)` | 7 | 0.1% |
| `use(axiom Pure.combination, [i, (i => ((i => i) => o))], o)` | 21 | 0.2% |
| `use(axiom Pure.combination, [i, (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))], o)` | 1 | 0.0% |
| `use(axiom Pure.combination, [i, (i => (i => ((i => (i => i)) => i)))], o)` | 896 | 9.5% |
| `use(axiom Pure.combination, [i, (i => (i => ((i => i) => o)))], o)` | 21 | 0.2% |
| `use(axiom Pure.combination, [i, (i => (i => (i => (i => (i => i)))))], o)` | 35 | 0.4% |
| `use(axiom Pure.combination, [i, (i => (i => (i => (i => i))))], o)` | 188 | 2.0% |
| `use(axiom Pure.combination, [i, (i => (i => (i => (i => o))))], o)` | 98 | 1.0% |
| `use(axiom Pure.combination, [i, (i => (i => (i => i)))], o)` | 1214 | 12.9% |
| `use(axiom Pure.combination, [i, (i => (i => (i => o)))], o)` | 416 | 4.4% |
| `use(axiom Pure.combination, [i, (i => (i => i))], o)` | 3205 | 34.0% |
| `use(axiom Pure.combination, [i, (i => (i => o))], o)` | 1390 | 14.8% |
| `use(axiom Pure.combination, [i, (i => i)], o)` | 7036 | 74.7% |
| `use(axiom Pure.combination, [i, (i => o)], o)` | 7984 | 84.8% |
| `use(axiom Pure.combination, [i, i], o)` | 7446 | 79.0% |
| `use(axiom Pure.combination, [i, o], o)` | 8099 | 86.0% |
| `use(axiom Pure.combination, [o, (i => (i => i))], o)` | 5020 | 53.3% |
| `use(axiom Pure.combination, [o, (i => o)], o)` | 92 | 1.0% |
| `use(axiom Pure.combination, [o, (o => o)], o)` | 8323 | 88.4% |
| `use(axiom Pure.combination, [o, i], o)` | 883 | 9.4% |
| `use(axiom Pure.combination, [o, o], o)` | 8432 | 89.5% |
| `use(axiom Pure.equal_elim, [], o)` | 8832 | 93.8% |
| `use(axiom Pure.equal_intr, [], o)` | 7981 | 84.7% |
| `use(axiom Pure.reflexive, ['a], o)` | 7581 | 80.5% |
| `use(axiom Pure.reflexive, ['b], o)` | 4628 | 49.1% |
| `use(axiom Pure.reflexive, [('a => 'b)], o)` | 4362 | 46.3% |
| `use(axiom Pure.reflexive, [('a => ('a => o))], o)` | 7578 | 80.4% |
| `use(axiom Pure.reflexive, [('a => o)], o)` | 7423 | 78.8% |
| `use(axiom Pure.reflexive, [('b => 'a)], o)` | 439 | 4.7% |
| `use(axiom Pure.reflexive, [('b => ('b => o))], o)` | 4626 | 49.1% |
| `use(axiom Pure.reflexive, [('b => (('b => 'a) => 'a))], o)` | 439 | 4.7% |
| `use(axiom Pure.reflexive, [(('a => o) => o)], o)` | 7324 | 77.7% |
| `use(axiom Pure.reflexive, [(('b => (('b => 'a) => 'a)) => (('b => (('b => 'a) => 'a)) => o))], o)` | 439 | 4.7% |
| `use(axiom Pure.reflexive, [((('a => o) => o) => ((('a => o) => o) => o))], o)` | 7323 | 77.7% |
| `use(axiom Pure.reflexive, [(((i => (i => 'a)) => (i => 'a)) => (((i => (i => 'a)) => (i => 'a)) => o))], o)` | 2773 | 29.4% |
| `use(axiom Pure.reflexive, [(((i => (i => (i => i))) => (i => i)) => (((i => (i => (i => i))) => (i => i)) => o))], o)` | 4 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => (((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i)))))) => o))], o)` | 38 | 0.4% |
| `use(axiom Pure.reflexive, [(((i => (i => i)) => (i => i)) => (((i => (i => i)) => (i => i)) => o))], o)` | 2760 | 29.3% |
| `use(axiom Pure.reflexive, [(((i => i) => ((i => i) => (i => i))) => (((i => i) => ((i => i) => (i => i))) => o))], o)` | 2421 | 25.7% |
| `use(axiom Pure.reflexive, [(((i => i) => (i => i)) => (((i => i) => (i => i)) => o))], o)` | 514 | 5.5% |
| `use(axiom Pure.reflexive, [(((i => i) => o) => (((i => i) => o) => o))], o)` | 531 | 5.6% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => (((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => (((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o))))))) => o))], o)` | 70 | 0.7% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => (((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o))) => o))], o)` | 183 | 1.9% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o))))) => o))], o)` | 318 | 3.4% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => (((i => o) => ((i => (i => (i => o))) => (i => (i => o)))) => o))], o)` | 53 | 0.6% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => (i => o))) => (i => o))) => (((i => o) => ((i => (i => (i => o))) => (i => o))) => o))], o)` | 155 | 1.6% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => o)) => ((i => i) => o))) => (((i => o) => ((i => (i => o)) => ((i => i) => o))) => o))], o)` | 128 | 1.4% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o)))))) => o))], o)` | 243 | 2.6% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => (((i => o) => ((i => (i => o)) => (i => (i => (i => o))))) => o))], o)` | 225 | 2.4% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => o)) => (i => o))) => (((i => o) => ((i => (i => o)) => (i => o))) => o))], o)` | 141 | 1.5% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => (i => o)) => o)) => (((i => o) => ((i => (i => o)) => o)) => o))], o)` | 585 | 6.2% |
| `use(axiom Pure.reflexive, [(((i => o) => ((i => o) => o)) => (((i => o) => ((i => o) => o)) => o))], o)` | 1163 | 12.3% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o))))) => o))], o)` | 3 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => (((i => o) => (i => ((i => (i => o)) => ((i => i) => o)))) => o))], o)` | 44 | 0.5% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => (((i => o) => (i => ((i => (i => o)) => (i => (i => o))))) => o))], o)` | 249 | 2.6% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => (i => o)) => (i => o)))) => (((i => o) => (i => ((i => (i => o)) => (i => o)))) => o))], o)` | 96 | 1.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => (i => o)) => o))) => (((i => o) => (i => ((i => (i => o)) => o))) => o))], o)` | 374 | 4.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => ((i => o) => (i => o)))) => (((i => o) => (i => ((i => o) => (i => o)))) => o))], o)` | 46 | 0.5% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => (((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o))))) => o))], o)` | 41 | 0.4% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => (((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))))) => o))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => (i => (i => (i => o)))))) => (((i => o) => (i => (i => (i => (i => (i => o)))))) => o))], o)` | 89 | 0.9% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => (i => (i => o))))) => (((i => o) => (i => (i => (i => (i => o))))) => o))], o)` | 117 | 1.2% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => (i => o)))) => (((i => o) => (i => (i => (i => o)))) => o))], o)` | 1025 | 10.9% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => i))) => (((i => o) => (i => (i => i))) => o))], o)` | 44 | 0.5% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => (i => o))) => (((i => o) => (i => (i => o))) => o))], o)` | 945 | 10.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => i)) => (((i => o) => (i => i)) => o))], o)` | 2 | 0.0% |
| `use(axiom Pure.reflexive, [(((i => o) => (i => o)) => (((i => o) => (i => o)) => o))], o)` | 670 | 7.1% |
| `use(axiom Pure.reflexive, [(((i => o) => (o => (i => o))) => (((i => o) => (o => (i => o))) => o))], o)` | 92 | 1.0% |
| `use(axiom Pure.reflexive, [(((i => o) => i) => (((i => o) => i) => o))], o)` | 5274 | 56.0% |
| `use(axiom Pure.reflexive, [(((i => o) => o) => (((i => o) => o) => o))], o)` | 4100 | 43.5% |
| `use(axiom Pure.reflexive, [(((i => o) => o) => o)], o)` | 435 | 4.6% |
| `use(axiom Pure.reflexive, [((i => 'a) => ((i => 'a) => o))], o)` | 2739 | 29.1% |
| `use(axiom Pure.reflexive, [((i => ((i => (i => (i => i))) => i)) => ((i => ((i => (i => (i => i))) => i)) => o))], o)` | 25 | 0.3% |
| `use(axiom Pure.reflexive, [((i => ((i => (i => i)) => (i => (i => i)))) => ((i => ((i => (i => i)) => (i => (i => i)))) => o))], o)` | 53 | 0.6% |
| `use(axiom Pure.reflexive, [((i => ((i => (i => i)) => (i => i))) => ((i => ((i => (i => i)) => (i => i))) => o))], o)` | 2044 | 21.7% |
| `use(axiom Pure.reflexive, [((i => ((i => (i => i)) => i)) => ((i => ((i => (i => i)) => i)) => o))], o)` | 3706 | 39.3% |
| `use(axiom Pure.reflexive, [((i => ((i => (i => o)) => i)) => ((i => ((i => (i => o)) => i)) => o))], o)` | 7313 | 77.6% |
| `use(axiom Pure.reflexive, [((i => ((i => i) => (i => i))) => ((i => ((i => i) => (i => i))) => o))], o)` | 3854 | 40.9% |
| `use(axiom Pure.reflexive, [((i => ((i => i) => i)) => ((i => ((i => i) => i)) => o))], o)` | 6215 | 66.0% |
| `use(axiom Pure.reflexive, [((i => ((i => i) => o)) => ((i => ((i => i) => o)) => o))], o)` | 4841 | 51.4% |
| `use(axiom Pure.reflexive, [((i => ((i => o) => i)) => ((i => ((i => o) => i)) => o))], o)` | 7247 | 76.9% |
| `use(axiom Pure.reflexive, [((i => ((i => o) => o)) => ((i => ((i => o) => o)) => o))], o)` | 7493 | 79.5% |
| `use(axiom Pure.reflexive, [((i => (i => 'a)) => (i => 'a))], o)` | 2773 | 29.4% |
| `use(axiom Pure.reflexive, [((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => ((i => (i => ((i => (i => i)) => ((i => (i => i)) => i)))) => o))], o)` | 8 | 0.1% |
| `use(axiom Pure.reflexive, [((i => (i => ((i => (i => i)) => (i => o)))) => ((i => (i => ((i => (i => i)) => (i => o)))) => o))], o)` | 4068 | 43.2% |
| `use(axiom Pure.reflexive, [((i => (i => ((i => (i => i)) => i))) => ((i => (i => ((i => (i => i)) => i))) => o))], o)` | 4061 | 43.1% |
| `use(axiom Pure.reflexive, [((i => (i => ((i => (i => i)) => o))) => ((i => (i => ((i => (i => i)) => o))) => o))], o)` | 439 | 4.7% |
| `use(axiom Pure.reflexive, [((i => (i => ((i => i) => ((i => i) => (i => o))))) => ((i => (i => ((i => i) => ((i => i) => (i => o))))) => o))], o)` | 7 | 0.1% |
| `use(axiom Pure.reflexive, [((i => (i => (i => ((i => (i => i)) => i)))) => ((i => (i => (i => ((i => (i => i)) => i)))) => o))], o)` | 896 | 9.5% |
| `use(axiom Pure.reflexive, [((i => (i => (i => ((i => i) => o)))) => ((i => (i => (i => ((i => i) => o)))) => o))], o)` | 21 | 0.2% |
| `use(axiom Pure.reflexive, [((i => (i => (i => (i => (i => (i => i)))))) => ((i => (i => (i => (i => (i => (i => i)))))) => o))], o)` | 35 | 0.4% |
| `use(axiom Pure.reflexive, [((i => (i => (i => (i => (i => i))))) => ((i => (i => (i => (i => (i => i))))) => o))], o)` | 187 | 2.0% |
| `use(axiom Pure.reflexive, [((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => (i => o))))) => o))], o)` | 9 | 0.1% |
| `use(axiom Pure.reflexive, [((i => (i => (i => (i => i)))) => ((i => (i => (i => (i => i)))) => o))], o)` | 1108 | 11.8% |
| `use(axiom Pure.reflexive, [((i => (i => (i => (i => o)))) => ((i => (i => (i => (i => o)))) => o))], o)` | 114 | 1.2% |
| `use(axiom Pure.reflexive, [((i => (i => (i => i))) => ((i => (i => (i => i))) => o))], o)` | 3075 | 32.6% |
| `use(axiom Pure.reflexive, [((i => (i => (i => i))) => (i => (i => i)))], o)` | 103 | 1.1% |
| `use(axiom Pure.reflexive, [((i => (i => (i => i))) => (i => i))], o)` | 981 | 10.4% |
| `use(axiom Pure.reflexive, [((i => (i => (i => o))) => ((i => (i => (i => o))) => o))], o)` | 284 | 3.0% |
| `use(axiom Pure.reflexive, [((i => (i => (i => o))) => ((i => (i => i)) => o))], o)` | 34 | 0.4% |
| `use(axiom Pure.reflexive, [((i => (i => (i => o))) => (i => (i => (i => o))))], o)` | 7 | 0.1% |
| `use(axiom Pure.reflexive, [((i => (i => (i => o))) => (i => (i => o)))], o)` | 114 | 1.2% |
| `use(axiom Pure.reflexive, [((i => (i => (i => o))) => (i => o))], o)` | 31 | 0.3% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => (i => i))) => ((i => (i => i)) => (i => i))))], o)` | 10 | 0.1% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => (i => i))) => (i => i)))], o)` | 19 | 0.2% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))], o)` | 38 | 0.4% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => i)))))], o)` | 24 | 0.3% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => i))) => (i => i))))], o)` | 21 | 0.2% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => (i => i)) => o))], o)` | 6923 | 73.5% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => ((i => i) => (i => i)))], o)` | 965 | 10.2% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => (i => ((i => (i => i)) => (i => i))))], o)` | 35 | 0.4% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => (i => i))], o)` | 2760 | 29.3% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => (i => o))], o)` | 2 | 0.0% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => i)], o)` | 3009 | 31.9% |
| `use(axiom Pure.reflexive, [((i => (i => i)) => o)], o)` | 29 | 0.3% |
| `use(axiom Pure.reflexive, [((i => (i => o)) => ((i => (i => o)) => o))], o)` | 7387 | 78.4% |
| `use(axiom Pure.reflexive, [((i => (i => o)) => ((i => i) => o))], o)` | 29 | 0.3% |
| `use(axiom Pure.reflexive, [((i => (i => o)) => (i => (i => o)))], o)` | 123 | 1.3% |
| `use(axiom Pure.reflexive, [((i => (i => o)) => (i => o))], o)` | 159 | 1.7% |
| `use(axiom Pure.reflexive, [((i => (i => o)) => o)], o)` | 8 | 0.1% |
| `use(axiom Pure.reflexive, [((i => i) => ((i => (i => (i => i))) => (i => i)))], o)` | 92 | 1.0% |
| `use(axiom Pure.reflexive, [((i => i) => ((i => (i => i)) => ((i => (i => i)) => (i => i))))], o)` | 23 | 0.2% |
| `use(axiom Pure.reflexive, [((i => i) => ((i => i) => (i => i)))], o)` | 2421 | 25.7% |
| `use(axiom Pure.reflexive, [((i => i) => ((i => i) => o))], o)` | 6847 | 72.7% |
| `use(axiom Pure.reflexive, [((i => i) => (i => (i => i)))], o)` | 442 | 4.7% |
| `use(axiom Pure.reflexive, [((i => i) => (i => i))], o)` | 3837 | 40.7% |
| `use(axiom Pure.reflexive, [((i => i) => i)], o)` | 4239 | 45.0% |
| `use(axiom Pure.reflexive, [((i => i) => o)], o)` | 2832 | 30.1% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))], o)` | 70 | 0.7% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o)))], o)` | 183 | 1.9% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o)))))], o)` | 318 | 3.4% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => o))) => (i => (i => o))))], o)` | 53 | 0.6% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => (i => o))) => (i => o)))], o)` | 155 | 1.6% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => o)) => ((i => i) => o)))], o)` | 128 | 1.4% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o))))))], o)` | 243 | 2.6% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => o)) => (i => (i => (i => o)))))], o)` | 225 | 2.4% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => o)) => (i => o)))], o)` | 141 | 1.5% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => (i => o)) => o))], o)` | 590 | 6.3% |
| `use(axiom Pure.reflexive, [((i => o) => ((i => o) => o))], o)` | 5453 | 57.9% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o)))))], o)` | 3 | 0.0% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => (i => o)) => ((i => i) => o))))], o)` | 44 | 0.5% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => (i => o)) => (i => (i => o)))))], o)` | 249 | 2.6% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => (i => o)) => (i => o))))], o)` | 96 | 1.0% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => (i => o)) => o)))], o)` | 374 | 4.0% |
| `use(axiom Pure.reflexive, [((i => o) => (i => ((i => o) => (i => o))))], o)` | 46 | 0.5% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))], o)` | 41 | 0.4% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))], o)` | 1 | 0.0% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => (i => (i => (i => o))))))], o)` | 89 | 0.9% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => (i => (i => o)))))], o)` | 117 | 1.2% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => (i => o))))], o)` | 1025 | 10.9% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => i)))], o)` | 44 | 0.5% |
| `use(axiom Pure.reflexive, [((i => o) => (i => (i => o)))], o)` | 945 | 10.0% |
| `use(axiom Pure.reflexive, [((i => o) => (i => i))], o)` | 9 | 0.1% |
| `use(axiom Pure.reflexive, [((i => o) => (i => o))], o)` | 670 | 7.1% |
| `use(axiom Pure.reflexive, [((i => o) => (o => (i => o)))], o)` | 92 | 1.0% |
| `use(axiom Pure.reflexive, [((i => o) => i)], o)` | 5323 | 56.5% |
| `use(axiom Pure.reflexive, [((i => o) => o)], o)` | 7632 | 81.0% |
| `use(axiom Pure.reflexive, [((o => (i => (i => i))) => ((o => (i => (i => i))) => o))], o)` | 5018 | 53.3% |
| `use(axiom Pure.reflexive, [((o => (o => o)) => ((o => (o => o)) => o))], o)` | 7841 | 83.2% |
| `use(axiom Pure.reflexive, [((o => i) => ((o => i) => o))], o)` | 882 | 9.4% |
| `use(axiom Pure.reflexive, [((o => o) => ((o => o) => o))], o)` | 7819 | 83.0% |
| `use(axiom Pure.reflexive, [(i => 'a)], o)` | 2739 | 29.1% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => (i => i))) => i))], o)` | 25 | 0.3% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => i)) => (i => (i => i))))], o)` | 53 | 0.6% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => i)) => (i => i)))], o)` | 2064 | 21.9% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => i)) => (i => o)))], o)` | 24 | 0.3% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => i)) => i))], o)` | 3706 | 39.3% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => o)) => (i => (i => o))))], o)` | 125 | 1.3% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => o)) => (i => o)))], o)` | 71 | 0.8% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => o)) => i))], o)` | 7313 | 77.6% |
| `use(axiom Pure.reflexive, [(i => ((i => (i => o)) => o))], o)` | 368 | 3.9% |
| `use(axiom Pure.reflexive, [(i => ((i => i) => (i => i)))], o)` | 3854 | 40.9% |
| `use(axiom Pure.reflexive, [(i => ((i => i) => i))], o)` | 6226 | 66.1% |
| `use(axiom Pure.reflexive, [(i => ((i => i) => o))], o)` | 4841 | 51.4% |
| `use(axiom Pure.reflexive, [(i => ((i => o) => (i => o)))], o)` | 10 | 0.1% |
| `use(axiom Pure.reflexive, [(i => ((i => o) => i))], o)` | 7247 | 76.9% |
| `use(axiom Pure.reflexive, [(i => ((i => o) => o))], o)` | 7494 | 79.6% |
| `use(axiom Pure.reflexive, [(i => (i => 'a))], o)` | 2773 | 29.4% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i))))], o)` | 8 | 0.1% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => (i => i)) => (i => i))))], o)` | 13 | 0.1% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => (i => i)) => (i => o))))], o)` | 4068 | 43.2% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => (i => i)) => i)))], o)` | 4061 | 43.1% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => (i => i)) => o)))], o)` | 439 | 4.7% |
| `use(axiom Pure.reflexive, [(i => (i => ((i => i) => ((i => i) => (i => o)))))], o)` | 7 | 0.1% |
| `use(axiom Pure.reflexive, [(i => (i => (i => ((i => (i => i)) => i))))], o)` | 896 | 9.5% |
| `use(axiom Pure.reflexive, [(i => (i => (i => ((i => i) => o))))], o)` | 21 | 0.2% |
| `use(axiom Pure.reflexive, [(i => (i => (i => (i => (i => (i => i))))))], o)` | 35 | 0.4% |
| `use(axiom Pure.reflexive, [(i => (i => (i => (i => (i => i)))))], o)` | 187 | 2.0% |
| `use(axiom Pure.reflexive, [(i => (i => (i => (i => (i => o)))))], o)` | 55 | 0.6% |
| `use(axiom Pure.reflexive, [(i => (i => (i => (i => i))))], o)` | 1217 | 12.9% |
| `use(axiom Pure.reflexive, [(i => (i => (i => (i => o))))], o)` | 246 | 2.6% |
| `use(axiom Pure.reflexive, [(i => (i => (i => i)))], o)` | 3093 | 32.8% |
| `use(axiom Pure.reflexive, [(i => (i => (i => o)))], o)` | 1090 | 11.6% |
| `use(axiom Pure.reflexive, [(i => (i => i))], o)` | 6953 | 73.8% |
| `use(axiom Pure.reflexive, [(i => (i => o))], o)` | 7894 | 83.8% |
| `use(axiom Pure.reflexive, [(i => i)], o)` | 7140 | 75.8% |
| `use(axiom Pure.reflexive, [(i => o)], o)` | 7781 | 82.6% |
| `use(axiom Pure.reflexive, [(o => (i => (i => i)))], o)` | 5020 | 53.3% |
| `use(axiom Pure.reflexive, [(o => (i => o))], o)` | 67 | 0.7% |
| `use(axiom Pure.reflexive, [(o => (o => o))], o)` | 8323 | 88.4% |
| `use(axiom Pure.reflexive, [(o => i)], o)` | 883 | 9.4% |
| `use(axiom Pure.reflexive, [(o => o)], o)` | 8170 | 86.7% |
| `use(axiom Pure.reflexive, [i], o)` | 8188 | 86.9% |
| `use(axiom Pure.reflexive, [o], o)` | 8334 | 88.5% |
| `use(axiom Pure.symmetric, ['a], o)` | 7417 | 78.7% |
| `use(axiom Pure.symmetric, [i], o)` | 7250 | 77.0% |
| `use(axiom Pure.symmetric, [o], o)` | 8832 | 93.8% |
| `use(axiom Pure.transitive, ['a], o)` | 1877 | 19.9% |
| `use(axiom Pure.transitive, ['b], o)` | 2237 | 23.7% |
| `use(axiom Pure.transitive, [('b => (('b => 'a) => 'a))], o)` | 439 | 4.7% |
| `use(axiom Pure.transitive, [(('a => o) => o)], o)` | 7323 | 77.7% |
| `use(axiom Pure.transitive, [((i => (i => 'a)) => (i => 'a))], o)` | 2773 | 29.4% |
| `use(axiom Pure.transitive, [((i => (i => (i => i))) => (i => i))], o)` | 4 | 0.0% |
| `use(axiom Pure.transitive, [((i => (i => i)) => ((i => (i => i)) => ((i => (i => (i => (i => i)))) => ((i => (i => i)) => (i => (i => i))))))], o)` | 38 | 0.4% |
| `use(axiom Pure.transitive, [((i => (i => i)) => (i => i))], o)` | 2760 | 29.3% |
| `use(axiom Pure.transitive, [((i => (i => o)) => o)], o)` | 422 | 4.5% |
| `use(axiom Pure.transitive, [((i => i) => ((i => i) => (i => i)))], o)` | 2421 | 25.7% |
| `use(axiom Pure.transitive, [((i => i) => (i => i))], o)` | 514 | 5.5% |
| `use(axiom Pure.transitive, [((i => i) => o)], o)` | 531 | 5.6% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => (i => (i => o))))) => ((i => (i => (i => (i => i)))) => o)))], o)` | 1 | 0.0% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o)))], o)` | 1 | 0.0% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => (i => o))) => ((i => (i => o)) => (i => (i => o)))))))], o)` | 70 | 0.7% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => o))) => ((i => (i => i)) => o)))], o)` | 183 | 1.9% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => o))) => (i => (i => (i => o)))))], o)` | 318 | 3.4% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => o))) => (i => (i => o))))], o)` | 53 | 0.6% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => (i => o))) => (i => o)))], o)` | 155 | 1.6% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => o)) => ((i => i) => o)))], o)` | 128 | 1.4% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => o)) => (i => (i => (i => (i => o))))))], o)` | 243 | 2.6% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => o)) => (i => (i => (i => o)))))], o)` | 225 | 2.4% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => o)) => (i => o)))], o)` | 141 | 1.5% |
| `use(axiom Pure.transitive, [((i => o) => ((i => (i => o)) => o))], o)` | 590 | 6.3% |
| `use(axiom Pure.transitive, [((i => o) => ((i => o) => o))], o)` | 1163 | 12.3% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => (i => (i => o))) => (i => (i => o)))))], o)` | 3 | 0.0% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => (i => o)) => ((i => i) => o))))], o)` | 44 | 0.5% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => (i => o)) => (i => (i => o)))))], o)` | 249 | 2.6% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => (i => o)) => (i => o))))], o)` | 96 | 1.0% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => (i => o)) => o)))], o)` | 374 | 4.0% |
| `use(axiom Pure.transitive, [((i => o) => (i => ((i => o) => (i => o))))], o)` | 46 | 0.5% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => ((i => (i => (i => o))) => ((i => (i => i)) => o)))))], o)` | 41 | 0.4% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => (i => ((i => (i => (i => (i => o)))) => ((i => (i => (i => i))) => o))))))], o)` | 1 | 0.0% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => (i => (i => (i => o))))))], o)` | 89 | 0.9% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => (i => (i => o)))))], o)` | 117 | 1.2% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => (i => o))))], o)` | 1025 | 10.9% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => i)))], o)` | 44 | 0.5% |
| `use(axiom Pure.transitive, [((i => o) => (i => (i => o)))], o)` | 945 | 10.0% |
| `use(axiom Pure.transitive, [((i => o) => (i => i))], o)` | 438 | 4.6% |
| `use(axiom Pure.transitive, [((i => o) => (i => o))], o)` | 827 | 8.8% |
| `use(axiom Pure.transitive, [((i => o) => (o => (i => o)))], o)` | 92 | 1.0% |
| `use(axiom Pure.transitive, [((i => o) => i)], o)` | 5274 | 56.0% |
| `use(axiom Pure.transitive, [((i => o) => o)], o)` | 4100 | 43.5% |
| `use(axiom Pure.transitive, [(i => ((i => (i => (i => i))) => i))], o)` | 25 | 0.3% |
| `use(axiom Pure.transitive, [(i => ((i => (i => i)) => (i => (i => i))))], o)` | 53 | 0.6% |
| `use(axiom Pure.transitive, [(i => ((i => (i => i)) => (i => i)))], o)` | 2044 | 21.7% |
| `use(axiom Pure.transitive, [(i => ((i => (i => i)) => i))], o)` | 3706 | 39.3% |
| `use(axiom Pure.transitive, [(i => ((i => (i => o)) => i))], o)` | 7313 | 77.6% |
| `use(axiom Pure.transitive, [(i => ((i => i) => (i => i)))], o)` | 3854 | 40.9% |
| `use(axiom Pure.transitive, [(i => ((i => i) => i))], o)` | 6215 | 66.0% |
| `use(axiom Pure.transitive, [(i => ((i => i) => o))], o)` | 4841 | 51.4% |
| `use(axiom Pure.transitive, [(i => ((i => o) => i))], o)` | 7247 | 76.9% |
| `use(axiom Pure.transitive, [(i => ((i => o) => o))], o)` | 7493 | 79.5% |
| `use(axiom Pure.transitive, [(i => (i => ((i => (i => i)) => ((i => (i => i)) => i))))], o)` | 8 | 0.1% |
| `use(axiom Pure.transitive, [(i => (i => ((i => (i => i)) => (i => o))))], o)` | 4068 | 43.2% |
| `use(axiom Pure.transitive, [(i => (i => ((i => (i => i)) => i)))], o)` | 4061 | 43.1% |
| `use(axiom Pure.transitive, [(i => (i => ((i => (i => i)) => o)))], o)` | 439 | 4.7% |
| `use(axiom Pure.transitive, [(i => (i => ((i => i) => ((i => i) => (i => o)))))], o)` | 7 | 0.1% |
| `use(axiom Pure.transitive, [(i => (i => (i => ((i => (i => i)) => i))))], o)` | 896 | 9.5% |
| `use(axiom Pure.transitive, [(i => (i => (i => ((i => i) => o))))], o)` | 21 | 0.2% |
| `use(axiom Pure.transitive, [(i => (i => (i => (i => (i => (i => i))))))], o)` | 35 | 0.4% |
| `use(axiom Pure.transitive, [(i => (i => (i => (i => (i => i)))))], o)` | 187 | 2.0% |
| `use(axiom Pure.transitive, [(i => (i => (i => (i => (i => o)))))], o)` | 9 | 0.1% |
| `use(axiom Pure.transitive, [(i => (i => (i => (i => i))))], o)` | 1082 | 11.5% |
| `use(axiom Pure.transitive, [(i => (i => (i => (i => o))))], o)` | 140 | 1.5% |
| `use(axiom Pure.transitive, [(i => (i => (i => i)))], o)` | 3075 | 32.6% |
| `use(axiom Pure.transitive, [(i => (i => (i => o)))], o)` | 266 | 2.8% |
| `use(axiom Pure.transitive, [(i => (i => i))], o)` | 6918 | 73.4% |
| `use(axiom Pure.transitive, [(i => (i => o))], o)` | 7384 | 78.4% |
| `use(axiom Pure.transitive, [(i => i)], o)` | 6838 | 72.6% |
| `use(axiom Pure.transitive, [(i => o)], o)` | 5277 | 56.0% |
| `use(axiom Pure.transitive, [(o => (i => (i => i)))], o)` | 5018 | 53.3% |
| `use(axiom Pure.transitive, [(o => (o => o))], o)` | 7841 | 83.2% |
| `use(axiom Pure.transitive, [(o => i)], o)` | 882 | 9.4% |
| `use(axiom Pure.transitive, [(o => o)], o)` | 7819 | 83.0% |
| `use(axiom Pure.transitive, [i], o)` | 6003 | 63.7% |
| `use(axiom Pure.transitive, [o], o)` | 7762 | 82.4% |
| `use(axiom ZF_Base.Pow_iff, [], o)` | 7023 | 74.6% |
| `use(axiom ZF_Base.Union_iff, [], o)` | 7069 | 75.0% |
| `use(axiom ZF_Base.extension, [], o)` | 7048 | 74.8% |
| `use(axiom ZF_Base.foundation, [], o)` | 6969 | 74.0% |
| `use(axiom ZF_Base.infinity, [], o)` | 4129 | 43.8% |
| `use(axiom ZF_Base.replacement, [], o)` | 7313 | 77.6% |
| `use(definition fol, [], o)` | 4022 | 42.7% |
| `use(definition fol, [i], o)` | 3947 | 41.9% |
| `use(definition ifol, ['a], o)` | 7966 | 84.6% |
| `use(definition ifol, ['b, 'a], o)` | 439 | 4.7% |
| `use(definition ifol, [], o)` | 7940 | 84.3% |
| `use(definition pure, ['a], o)` | 28 | 0.3% |
| `use(definition pure, [], o)` | 8174 | 86.8% |
| `use(definition zf, ['a], o)` | 2791 | 29.6% |
| `use(definition zf, [], o)` | 9303 | 98.8% |
| `use(theorem, ['a], o)` | 7974 | 84.6% |
| `use(theorem, ['b], o)` | 4634 | 49.2% |
| `use(theorem, [(i => i)], o)` | 128 | 1.4% |
| `use(theorem, [(i => o)], o)` | 741 | 7.9% |
| `use(theorem, [], o)` | 8346 | 88.6% |
| `use(theorem, [dummy], o)` | 28 | 0.3% |
| `use(theorem, [i, i], o)` | 4635 | 49.2% |
| `use(theorem, [i], o)` | 7965 | 84.6% |
| `use(theorem, [o], o)` | 345 | 3.7% |
| `use(theory axiom, [], o)` | 20 | 0.2% |
