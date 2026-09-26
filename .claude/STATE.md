# STATE — isa2fol
`HEAD` · `feature/exists-descent` · 2026-09-24.
**RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is at `~/.local/bin` — not on a non-login shell's PATH.

| command (from the repo root) | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | **`148`** |
| `ls Sources` · `ls docs` | `FolDialect IR Reader isa2fol YXML` · `CLOSURE.md FOUNDATION.md phase2_probes SOURCE_SURFACE.md` |
| `find Sources Tests -name '*.swift' \| wc -l` | `38` (4256 lines) |
| comment density of `Sources` (CLAUDE.md rule 9's script) | `4/2100 = 0.19%` |
| `grep -rnE '^\s*default:' Sources` (a switch default — rule 11) | nothing |
| `.build/release/isa2fol surface data/zf_export \| grep '^| \*\*all'` | `\| **all** \| **9420** \|` |
| `readlink ~/repos/fol-zfc-comb/bazel-bin \| sed 's\|.*bazel-out/\|\|'` | `k8-opt/bin` — and `proof_checker` is executable there |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h qualified-names` | `487c68c` (unmerged) |
| `find data/zf_export -path '*/proofs/*' -type f \| wc -l` | `38923` — else rebuild: `bash scripts/03-export-zf.sh` |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

`/home/arthur/repos/isa2fol`, branch `feature/exists-descent`, clean, **not pushed**
(`git rev-list --count origin/feature/exists-descent..HEAD`). The branch name describes
deleted work — §6. fol-zfc-comb sits on its own `comb-verifier` with an uncommitted
`MODULE.bazel.lock` that is the user's; leave both alone.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `DESIGN.md` **§2, §3, §4** | the ZF-surface dialect; the text boundary; the whole framework — §4.8 is what is still open |
| `Sources/IR/Node.swift` | `mapChildren`: the ONLY place that says which kinds bind, and in which namespace |
| `Sources/IR/Table.swift` | `sortOf`: types of values, conclusions of steps, every validation |
| `Sources/FolDialect/Render.swift` | one switch renders formulas and emits proofs as the checker's stack program |
| `docs/FOUNDATION.md` **§2** | S1–S6; everything must satisfy it |
| `CLAUDE.md` rules 1, 5, 9, 10, 11 | no fallbacks · no name mangling · comment cap · never uncapped · no `default:` |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 AND stderr is empty | the two real-checker tests in `Tests/FolDialectTests` |
| Equal content is one node; an ill-formed node cannot exist | `Table.intern` (`TableTests`, `ProofTests`) |
| A step constrains only its principal connective | `Table.sortOf`; `anIntroductionTakesPremisesOfAnyDialect` |
| No source kind reaches the text | `legalize`; `render` throws `sourceKind` |

**Standing warnings — silent if repeated:**

- **⚠ `Conditional` IS NOT `Proved`; NEVER SUM THEM.** A claim with no proof block is not
  citable — `use` fails `unknown axiom/theorem`; `Conditional` needs `proof X: UNPROVED`.
- **⚠ BINDER KNOWLEDGE LIVES ONLY IN `mapChildren`.** A second list lets the traversal, the
  index engine and `looseBound` disagree — D2's silent de Bruijn error.
- **⚠ A FOL VARIABLE IS INSTANTIATED ONLY AT A FOL VARIABLE.** An isa term inside a `folPred`
  is an S1 violation; `intern` refuses it.
- **⚠ `false`, LOWERCASE, IS ⊥.** `False` lexes as a nullary PREDICATE. Pinned by
  `probe_bottom`, which only proves if ⊥ is ⊥.
- **⚠ NO NAME MANGLING** (CLAUDE.md rule 5). Qualified names are legal in claim and predicate
  positions once `qualified-names` is merged; until then the real-checker tests use plain names.
- **⚠ AN ID IS NEVER AN ORDER OR A NAME; NEVER ITERATE A `Dictionary`/`Set` TOWARD OUTPUT** —
  Swift seeds `Hasher` per process (`DESIGN.md` §4.6).
- **⚠ `t.type(of: try t.intern(…))` READS THE TABLE BEFORE THE INTERN** — receiver evaluated
  first. Intern into a `let`, then query. Crashes, never lies.
- **⚠ BUILDING fol-zfc-comb IN DEFAULT CONFIG REPOINTS `bazel-bin` TO `k8-fastbuild`** and the
  real-checker tests lose the checker. Restore: `ln -sfn <execroot>/bazel-out/k8-opt/bin bazel-bin`.
- **⚠ fol-zfc-comb's `//src/library` DOES NOT BUILD AS CONFIGURED** (GCC 11 `-O3`
  `stringop-overflow` under `-Werror`, pre-existing); test with `--cxxopt=-Wno-error=stringop-overflow`.
- **⚠ SERIALS COLLIDE ACROSS THEORIES** — key on `(theory, serial)`.
- **⚠ A SERIAL NAMES A THEOREM ONLY WITHIN ONE BUILD.** Two builds of the export differ in 1,021
  of 3,955 named serials. Never write a serial into a test, fixture or doc — name the theorem.
- **⚠ `data/zf_export` IS ONE BUILD OR NOTHING** — rebuilt whole by `scripts/03-export-zf.sh`,
  never patched. The merged pre-2026-09-25 export mismatched `List.upt_type`, dangled 402 citations.
- **⚠ ONE PROOF FILE IS 3.1 GB** (a box inside `List.nth_upt`). A statement is the file's first
  field; `YXML.parse` reads the whole file — the reader must not.
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED**; the Rust-era design docs are
  deleted — do not restore one.

## 4. State

| claim | verified by |
|---|---|
| The framework is built: table, one traversal, index engine, passes, `legalize`, 23 proof step kinds (`use`, `hyp`, 19 fol, 2 isa — `Node.swift`), two binder namespaces, `Rule.before/after` | `Tests/IRTests` |
| `render` emits formulas and proofs the REAL checker accepts and PROVES — every rule family | `theRealCheckerProvesWhatEmissionWrites`, `theRealCheckerAcceptsWhatRenderEmits` |
| D2's five laws hold over 300 seeded formulas each | `IndexTests` |
| The tests have teeth: 5 hand mutations (`instantiate`'s k−1, `isaAbs` binder, ∃-intro index, a hypothesis binder, a fixed-variable level) are each caught | re-run by hand after touching `Index.swift`/`Node.swift`/`Render.swift` |
| In the named ZF statements every logical constant is fully applied and every binder argument is a λ | `isa-deps --logic --named` (`~/repos/isabelle-study/bin/isa-deps`, untracked there) |
| No concrete pass exists | `ls Sources/IR` |
| The statement reader reads ALL 38,923 proof files of the eight exported sessions, none malformed: 9,382 of 9,420 named theorems translate; refused 23 type variable · 14 `quantifierOverFunction` · 1 `ofclass` | `swift build -c release && .build/release/isa2fol statements data/zf_export` (36 s); `--show KIND` lists them |
| Terms read η-long and type-directed; 3 mutations of the index arithmetic are each caught | `TermTests`; mutate `Scope.bound`, `abstraction`'s extras, `etaLong`'s head |
| YXML refuses a missing, malformed or duplicate attribute by name; an optional one is read as `attributes[name]` | `aMissingAttributeIsAnErrorNotEmpty`, `anAttributeFieldWithoutEqualsIsAnError`, `aDuplicateAttributeIsAnError` |
| The reader's three decisions — own type with `'a`/`prop`; frees left open for a closing pass; per-statement outcomes, only reader refusals caught — are decided; `IRType` has no `prop` | `DESIGN.md` §2 "Three decisions"; `Sources/IR/IRType.swift` |
| `YXML` parses in ONE hash-consing pass: the 3.1 GB file reads as < 20,000 nodes in 21 s (release) | `ISA2FOL_SCALE=1 swift test -c release -Xswiftc -enable-testing --filter theLargestProofFile` |
| `data/zf_export` is one build: every named statement equals its proof file, every one of 2,986,521 citations resolves | `scratchpad/compare/compare.py`, NOT kept — the export check is unbuilt |
| The export is not reproducible byte-for-byte: two builds differ in 7,258 paths, same statements | a second `scripts/03-export-zf.sh` run, `diff -rq` |
| Every proof of the 9,420 named theorems rests on: Pure 7 axioms + 3 defs, IFOL 17 axioms + 6 defs, FOL `classical` + 4 defs, ZF_Base's 6 axioms, `AC.AC`, 5 example-session axioms, 984 definitions; 0 oracles; 0 unbound type variables at citations | `.build/release/isa2fol closure data/zf_export` (`docs/CLOSURE.md`) |
| The census has not started: no `census/isa-shapes` branch | `git branch -a \| grep census` |

## 5. Beliefs — NOT verified

- ~1–2 GB for all of ZF in one table, no sharing — a throwaway decode, not kept.
- 838 unresolved citations; 1,780,478 proof nodes — the same throwaway decode, on the MERGED export: void.
- 197 term constants in 27 levels — `~/isabelle-object-constants.md`, no handle.

## 6. Open decisions

1. **The branch.** `feature/exists-descent` names deleted work and is unpushed: rename, branch
   fresh, or merge to `main`.
2. **The checker branch `qualified-names`.** Review, merge, rebuild `proof_checker -c opt`;
   then a real-checker test can emit an Isabelle name.
3. **`UNPROVED` as `extern`.** Separate compilation needs stubs; R2 says no debt — ban at the
   final link, or per unit?
4. **Proof lowering, before any proof pass:** a `Rule` sees only (node, depth), but lowering
   `isaAllElim` needs WHICH hypothesis proves `set(t)` — a context parameter, or a custom
   `Pass`; and lowering `isaAllIntro` inserts a hypothesis binder, which needs a
   hypothesis-namespace `shift` the index engine does not have (`Index.swift:34` filters to
   terms). `ProofTests.afterRewritesAStepOnceItsPremisesAreRewritten` sidesteps both with a
   loose `hyp(0, …)`.
5. **A build-independent identity for unnamed proof boxes.** A serial names a box only within
   one build (CLAUDE.md), yet emission needs claim names and an order that are a function of
   content (`DESIGN.md` §4.6 R2). Named theorems have names; the 12,000+ unnamed boxes do not.
   Options: name a box by a hash of its statement and proof, or inline boxes into their unique
   citer where there is one. Decide before emission.

## 7. Next action

**Read proofs.** Decode each proof file's zproof into proof steps (`DESIGN.md` §4.7), on the
same `Terms`: census question 6 is settled (§4.8) — a term `ZBound` counts `ZAbst` binders only,
so `Scope` serves unchanged. Decoding MUST be memoised on `(Ref, scope)`: one box is 312 M tree
nodes over 11,604 distinct ones (`DESIGN.md` §2). **Done when** every proof file's proof reads
or refuses by name, in bounded time and memory.
