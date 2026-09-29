# STATE — isa2fol
`e624a54b` · `feature/exists-descent` · 2026-09-27.  **RUN §0 BEFORE TRUSTING ANY LINE BELOW.**

## 0. Staleness checks

`swift` is at `~/.local/bin` — not on a non-login shell's PATH. Run from the repo root.

| command | expect |
|---|---|
| `swift --version \| head -1` | `Swift version 6.4 (swift-6.4-RELEASE)` |
| `MEM=16G scripts/capped.sh swift test 2>&1 \| grep -cE '^✔ Test [a-zA-Z]+\(\) passed'` | `191` |
| `find Sources Tests -name '*.swift' \| wc -l` · total lines | `41` · `5297` |
| comment density of `Sources` (CLAUDE.md rule 9's script) | `9/2425 = 0.4%` |
| `grep -rnE '^\s*default:' Sources \| wc -l` | `0` |
| `.build/release/isa2fol read data/zf_export \| grep -A1 -E '^named'` | `proved: 9420` · `…outside the ZF sessions: 200` / `proved: 200` |
| `.build/release/isa2fol surface data/zf_export \| grep '^\| \*\*all'` | `\| **all** \| **9420** \|` |
| `find data/zf_export -path '*/proofs/*' -type f \| wc -l` | `38923` — else `bash scripts/03-export-zf.sh` |
| `readlink ~/repos/fol-zfc-comb/bazel-bin \| sed 's\|.*bazel-out/\|\|'` | `k8-opt/bin`, `proof_checker` executable there |
| `git -C ~/repos/fol-zfc-comb log -1 --format=%h qualified-names` | `487c68c` (unmerged) |

If a row disagrees, **this file is stale**: trust the code, fix this file.

## 1. Where

`/home/arthur/repos/isa2fol`, branch `feature/exists-descent`, clean, 140 commits not pushed
(`git rev-list --count origin/feature/exists-descent..HEAD`). fol-zfc-comb sits on its own
`comb-verifier` with an uncommitted `MODULE.bazel.lock` that is the user's; leave both alone.

## 2. Read these first-hand

| path | what to look for |
|---|---|
| `Sources/IR/Node.swift` | the kinds in commented groups — the first two ARE the reader's output; `dialects`; `mapChildren`, the ONLY place that says which kinds bind |
| `Sources/IR/Table.swift` | `sortOf`: a value's type, a step's conclusion (its inference rule), every validation |
| `Sources/Reader/Reader.swift` | `prove`: the conclusion-equals-statement check; `head`: every proof constructor's reading |
| `DESIGN.md` **§2, §4.3a, §4.7** | the reader's decisions; the surface ↔ dialect table and points 3 and 5; the proof layer |
| `docs/FOUNDATION.md` **§2** | S1–S6: what every pass must satisfy |

## 3. Invariants

| invariant | enforced by |
|---|---|
| A unit is valid only when the checker exits 0 AND stderr is empty | the two real-checker tests in `Tests/FolDialectTests` |
| Equal content is one node; an ill-formed node cannot exist | `Table.intern` (`TableTests`, `ProofTests`) |
| Every proof read concludes its statement, BY ID | `Reader.prove` → `MalformedExport.unproved`; `aProofConcludingSomethingElseIsMalformed` |
| The reader emits only the isa dialect | `theReaderEmitsOnlyTheIsaDialect` |
| No isa-only kind reaches the text | `legalize` (from `Node.dialects`); `render` throws `sourceKind` |

**Standing warnings — silent or misleading if repeated:**

- **⚠ `Conditional` IS NOT `Proved`; NEVER SUM THEM.** A claim with no proof block is not citable.
- **⚠ THE READER CHOOSES NOTHING.** It read at ground instances and absorbed `OFCLASS` once, and
  each lost theorems (`DESIGN.md` §4.3a 3, 5). Which types, what `OFCLASS` becomes: translation's.
- **⚠ A CITATION IS `head % terms %% discharges`** — the ∀-closure is outermost. A fixture written
  the other way round reads as `principalConnective`.
- **⚠ BINDER KNOWLEDGE LIVES ONLY IN `mapChildren`** — a second list is D2's silent de Bruijn error.
- **⚠ `false`, LOWERCASE, IS ⊥** — `False` lexes as a nullary predicate (`probe_bottom`).
- **⚠ NO NAME MANGLING** (CLAUDE.md rule 5); real-checker tests use plain names until
  `qualified-names` is merged.
- **⚠ NEVER ITERATE A `Dictionary`/`Set` TOWARD OUTPUT** — `Hasher` is seeded per process (§4.6).
- **⚠ `t.type(of: try t.intern(…))` AND `t[try t.intern(…)]` READ THE TABLE BEFORE THE INTERN** —
  intern into a `let` first. A closure capturing a table while it is mutated is the same crash.
- **⚠ REORDERING OR ADDING `Node` CASES LEAVES DEPENDENT MODULES ON THE OLD LAYOUT** in an
  incremental build — `unknownNode(%0)` or a segfault. `rm -rf .build/out/Products .build/out/Intermediates.noindex`.
- **⚠ `pgrep -f` IN A WAIT LOOP MATCHES ITS OWN COMMAND LINE** and never exits; run jobs in sequence.
- **⚠ BUILDING fol-zfc-comb IN DEFAULT CONFIG REPOINTS `bazel-bin` TO `k8-fastbuild`**; restore
  `ln -sfn <execroot>/bazel-out/k8-opt/bin bazel-bin`. Its `//src/library` needs
  `--cxxopt=-Wno-error=stringop-overflow`.
- **⚠ A SERIAL NAMES A THEOREM ONLY WITHIN ONE BUILD, AND ONLY WITHIN ITS THEORY** — key on
  `(theory, serial)`; never write one into a test, fixture or doc.
- **⚠ `data/zf_export` IS ONE BUILD OR NOTHING** — rebuilt whole, never patched.
- **⚠ ONE PROOF FILE IS 3.1 GB** — read only through the hash-consed forest and the `(Ref, scope)`
  memos; a tree walk is exponential. `transform` survives proofs only through its cache keyed on
  the NARROWED context: keyed on the full context one proof exceeds 150 M rewrites (DESIGN §4.5).
- **⚠ EVERY CORPUS FIGURE IN `FOUNDATION.md` IS UNEVIDENCED.**

## 4. State

| claim | verified by |
|---|---|
| The reader proves ALL 9,420 named theorems of the 8 exported sessions as Isabelle states them — type variables (`IRType.variable`, `dummy` one variable) and class premises (`isaOfClass`) included, nothing absorbed — plus the 200 named Pure/IFOL/FOL theorems their proofs reach; 0 refused; 6.87 M nodes in 58 s, 3.5 GB | §0's `read` row |
| A citation is `use(name, types, root)`: its type arguments kept, `root` the cited statement read at them; an unnamed box is inlined, read at its citation's types | `aCitationCarriesItsTypes`, `anUnnamedBoxIsInlined`, `aHiddenProofTypeIsATypeVariable` |
| `render` refuses a typed `use` — an instance has no claim name — so no real proof renders yet | `aCitationOfAnInstanceIsNotRendered` |
| `render` emits formulas and proofs the REAL checker proves, every rule family | `theRealCheckerProvesWhatEmissionWrites`, `theRealCheckerAcceptsWhatRenderEmits` |
| The tests have teeth: each of these mutations is caught — `instantiate`'s k−1, the `isaAbs` binder, the ∃-intro index, a hypothesis binder, a fixed-variable level; the hypothesis shift, box inlining, the conclusion check; dropping a citation's types, `dummy` as `i`, `OFCLASS`'s type; `folImplies` as fol-only | re-run by hand after touching `Index.swift`, `Node.swift`, `Render.swift`, `Reader.swift`, `Terms.swift` |
| D2's five laws hold over 300 seeded formulas each; `instantiate` reduces the redexes it makes | `IndexTests` |
| Proofs rest on: Pure 7 axioms + 3 defs, IFOL 17 axioms + 6 defs (`term_class_def` among them), FOL `classical` + 4 defs, ZF_Base's 6 axioms, `AC.AC`, 984 ZF definitions, and 5 example-session axioms with no proof anywhere (`Language.constNEE`, `Language.c_appI`, `Static.isof_app`, `LList.flip_LNil`, `LList.flip_LCons` — their theorems can only be `Conditional`); 0 oracles | `.build/release/isa2fol closure data/zf_export` (`docs/CLOSURE.md`) |
| The census counts what the reader reads, class discharges included, except the proofs of Pure/IFOL/FOL theorems | `isa2fol surface` (`docs/SOURCE_SURFACE.md`); `SurfaceTests` |
| `YXML` parses the 3.1 GB file in one hash-consing pass, < 20,000 nodes, 21 s | `ISA2FOL_SCALE=1 swift test -c release -Xswiftc -enable-testing --filter theLargestProofFile` |
| No concrete pass exists; `DESIGN.md` §4a's pass list is stale — it names `isaAtom` (no such kind) and `isaFree → folVar` (never produced) | `ls Sources/IR`; `grep -n isaAtom DESIGN.md` |
| `transform` takes many roots and caches each `(node, rule.narrow(context))` for the walk; the node sees only the narrowed context; the pipeline runs each pass over all roots and proofs in one walk | `aSharedNodeIsRewrittenOncePerContext`, `aNodeSeesOnlyTheContextItsRuleNarrowedTo`, `oneWalkOverSeveralRootsRewritesASharedNodeOnce` |
| `Rule` has a pass-chosen `Context` (default `Depth`); `visit` calls `enter(c, binder, binds)` for each BOUND child only, on the way down | `aRuleSeesTheContextItsBindersMade`; `aRuleSeesTheBinderDepthOfEachNode` |
| `IR.Statement` is `(name, root, proof)`; `Pipeline` lowers root and proof and throws `PipelineError.unproved` when a pass leaves the proof not concluding the root. Nothing builds a `Unit` from the reader's outcomes yet | `aPipelineRunsItsPassesInOrderOverEveryStatementAndItsProof`, `aPassThatBreaksAProofStopsThePipelineNamingThePassAndTheStatement`; `grep -rn 'Unit(' Sources` |

## 5. Beliefs — NOT verified

- Every one of the export's 2,986,521 citations resolves — a throwaway script, not kept; the reader
  proves only that every citation it REACHES resolves.
- 197 term constants in 27 levels — `~/isabelle-object-constants.md`, no handle.

## 6. Open decisions

1. **The branch** `feature/exists-descent` names deleted work and is unpushed: rename, branch fresh, or merge.
2. **The checker branch `qualified-names`**: review, merge, rebuild `-c opt`; then tests can emit Isabelle names.
3. **`UNPROVED` as `extern`**: ban at the final link, or per unit?
4. **Shared subproofs at emission**: emission unfolds a shared subproof per use; name them by content, never a serial.
5. **`isaFree` and `abstract`** have no producer (`Node.dialects`: no dialect): delete, or keep?
6. **Generic theorems** (translation's): which ground copies, at which types for an uncited one; a
   copy is not a bare substitution (a function type needs λ-expansion); an instance's claim name;
   which unit emits it.
7. **What lowering makes of `OFCLASS`** (translation's): ⊤ at `i`; `term_class_def` quantifies over `o`.
8. **Rename `ifolAll`/`ifolEx` → `isaAll`/`isaEx`** so the prefix names the dialect: yes or no.

## 7. Next action

The framework pieces the first pass needs are built (record, `enter`, cache). The first pass is
AGREED with the user: guard QUANTIFIED variables of type `i` only, isa → isa — `ifolAll(i, set(0) → φ)`,
`ifolEx(i, set(0) ∧ φ)`, `isaAllIntro(i, folImpliesIntro(set(0), body))`; an elimination AT A
VARIABLE is discharged by that variable's guard hypothesis; `set` is `isaConst("set", i ⇒ o, [t])`,
not `folPred`, which stays variables-only; one walk, not a fixpoint. `set(t)` for a compound `t` is
inferred LATER (closure lemmas, "we will see it later") — until then refused by name. Write it into
`DESIGN.md` §4a, replacing the stale list, with its failing test; build only after approval. Also
needed: the CLI glue building a `Unit` from the reader's outcomes.
