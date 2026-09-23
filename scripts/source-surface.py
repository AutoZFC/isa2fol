#!/usr/bin/env python3
"""Regenerate docs/SOURCE_SURFACE.md's two tables from the export.

    scripts/source-surface.py            # both tables, as markdown

Population: the named theorems of the 37 ZF.* theories.  SURFACE reading only --
a proof's own region, stopping at every named theorem, so IFOL is never unfolded
into Pure.  That cut is the whole point: it answers "what must the dialect
model", not "what does the metalogic ultimately rest on".

Needs ~/repos/isabelle-study/bin/isa-deps for the Corpus reader.  Set ISA_DEPS
to override.  It REFUSES rather than guessing if the reader is absent.
"""
import importlib.machinery, importlib.util, os, sys

ISA_DEPS = os.environ.get(
    "ISA_DEPS", os.path.expanduser("~/repos/isabelle-study/bin/isa-deps"))
if not os.path.isfile(ISA_DEPS):
    sys.exit("no isa-deps at %s -- set ISA_DEPS" % ISA_DEPS)

_spec = importlib.util.spec_from_loader(
    "isadeps", importlib.machinery.SourceFileLoader("isadeps", ISA_DEPS))
_m = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_m)

# YXML tag 0 is BOTH `Type` and `Const`, so isa-deps' constant census cannot
# tell a sort from a term constant.  These four are the sorts.
SORTS = {"ZF_Base.i", "IFOL.o", "prop", "fun"}
LOGIC = ("Pure", "IFOL", "FOL")
SYMBOL = {
    "Pure.imp": "⟹", "Pure.eq": "≡", "Pure.all": "⋀",
    "IFOL.Trueprop": "⌜⌝", "IFOL.conj": "∧", "IFOL.disj": "∨",
    "IFOL.imp": "⟶", "IFOL.iff": "⟷", "IFOL.Not": "¬", "IFOL.All": "∀",
    "IFOL.Ex": "∃", "IFOL.eq": "=", "IFOL.False": "⊥", "IFOL.True": "⊤",
    "IFOL.Ex1": "∃!",
}


def main():
    c = _m.Corpus()
    pop = len(c.zf)
    sthms, socc = c.stmt_tally()
    _, own_thms, own_occ, deep_thms = c.tally()
    logical = lambda k: k.split(".")[0] in LOGIC

    print("population: %d named ZF theorems, %d ZF.* theories\n"
          % (pop, len({n[0] for n in c.zf})))

    print("## Statements\n")
    print("| | constant | thms | % | occ |")
    print("|---|---|---:|---:|---:|")
    for k, v in sorted(((k, v) for k, v in sthms.items()
                        if logical(k) and k not in SORTS), key=lambda kv: -kv[1]):
        print("| `%s` | `%s` | %d | %.1f%% | %d |"
              % (SYMBOL.get(k, ""), k, v, 100 * v / pop, socc[k]))

    print("\n### Sorts\n")
    print("| sort | thms | % | occ |")
    print("|---|---:|---:|---:|")
    for k in sorted(SORTS, key=lambda k: -sthms.get(k, 0)):
        print("| `%s` | %d | %.1f%% | %d |"
              % (k, sthms.get(k, 0), 100 * sthms.get(k, 0) / pop, socc.get(k, 0)))

    zero = [k for k in ("Pure.conjunction", "Pure.prop", "Pure.term",
                        "Pure.sort_constraint") if sthms.get(k, 0) == 0]
    print("\nabsent from every ZF statement: %s"
          % ", ".join("`%s`" % k for k in zero))
    print("ZF mathematical constants in statements: %d distinct"
          % len([k for k in sthms if not logical(k) and k not in SORTS]))
    print("FOL constants in statements: %d"
          % len([k for k in sthms if k.startswith("FOL.")]))

    print("\n## Proofs\n")
    pure_ax = set(_m.PURE_AXIOMS)
    print("| rule | kind | thms | occ |")
    print("|---|---|---:|---:|")
    for k in sorted((k for k in c.keys
                     if k.startswith("Pure.") and own_occ.get(k, 0) > 0),
                    key=lambda k: -own_occ[k]):
        print("| `%s` | %s | %d | %d |"
              % (k, "**axiom**" if k in pure_ax else "derived",
                 own_thms[k], own_occ[k]))

    print("\n| ZF axiom | thms | occ | deep |")
    print("|---|---:|---:|---:|")
    for k in _m.ZF_AXIOMS:
        print("| `%s` | %d | %d | %.1f%% |"
              % (k, own_thms.get(k, 0), own_occ.get(k, 0),
                 100 * deep_thms.get(k, 0) / pop))

    fol = [k for k in c.keys if k.split(".")[0] in ("IFOL", "FOL")
           and own_occ.get(k, 0) > 0]
    print("\nIFOL/FOL rules cited directly: %d (%d IFOL, %d FOL), %d occurrences"
          % (len(fol), len([k for k in fol if k.startswith("IFOL.")]),
             len([k for k in fol if k.startswith("FOL.")]),
             sum(own_occ[k] for k in fol)))
    print("\n| rule | thms | occ |")
    print("|---|---:|---:|")
    for k in sorted(fol, key=lambda k: -own_occ[k])[:15]:
        print("| `%s` | %d | %d |" % (k, own_thms[k], own_occ[k]))

    dr = [k for k in c.keys if k.endswith("_def_raw") and own_occ.get(k, 0) > 0]
    print("\nobject definitions cited: %d, each exactly once: %s"
          % (len(dr), all(own_occ[k] == 1 for k in dr)))
    print("ZF theorems citing ZF theorems (NOT frontier): %d"
          % len([k for k in c.keys if own_occ.get(k, 0) > 0
                 and not k.endswith("_def_raw") and not logical(k)]))

    print("\n## Excluded by the surface cut\n")
    print("| rule | reached by | |")
    print("|---|---:|---|")
    for k in sorted((k for k in c.keys if logical(k) and own_occ.get(k, 0) == 0
                     and deep_thms.get(k, 0) > 0), key=lambda k: -deep_thms[k])[:12]:
        print("| `%s` | %.1f%% | |" % (k, 100 * deep_thms[k] / pop))
    ex = [k for k in c.keys
          if own_occ.get(k, 0) == 0 and deep_thms.get(k, 0) > 0]
    print("\ntotal excluded: %d Pure, %d IFOL/FOL, %d ZF"
          % (len([k for k in ex if k.startswith("Pure.")]),
             len([k for k in ex if k.split(".")[0] in ("IFOL", "FOL")]),
             len([k for k in ex if not logical(k)])))


if __name__ == "__main__":
    main()
