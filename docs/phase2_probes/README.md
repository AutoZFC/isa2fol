# Probes

Standalone `.fol.def` / `.fol.proof` pairs the checker verifies directly:

```
proof_checker <name>.fol.def <name>.fol.proof
```

They are **artifacts, not prose** (FOUNDATION §5). Every one here is reached by a
test in `src/`, and `gate::tests::every_probe_has_a_role` enforces that.

## The three roles

| role | ledger | what the test does |
|---|---|---|
| **chain** — the §8 dependency chain, one probe per tier | `gate::CHAIN_PROBES` | kernel-accepts, and passes L, G1 and G4 |
| **linker fixture** — a declaration the kernel must refuse | `gate::LINKER_REJECT` | L's static half passes, the kernel **rejects** |
| **evidence** — backs a specific claim in the docs | `gate::EVIDENCE_PROBES` | kernel-accepts with empty stderr |

## Two rules, both enforced

**No file here may contain `iota`, `eq_subst`, `eq_sym` or `iota_elim` — and
"only there to be rejected" is not an exemption.** 13 probes carrying `iota`
were kept once on that argument and are now deleted.
`gate::tests::no_checked_in_artifact_carries_a_banned_construct` sweeps this
directory and `base/` through G4, which `gate::shapes` alone does not cover
since it only sees *generated* units.

Required-to-reject fixtures are therefore built **in code**, never stored:
`gate::iota_but_gate_clean` is a nine-line unit that is kernel-accepted and
L/G1-clean while using `iota`, which is the whole of what
`p0_gates_do_not_imply_on_spec` needs; G4's detection of each banned token is
covered by synthetic units in `gate::shapes`. A banned construct sitting in the
tree gets cited, copied, or wired into a chain — that is the risk, and it is not
worth a fixture that code can produce.

**An artifact survives only if a test runs it.** This directory previously held
108 probes: 77 were reachable from nothing at all, 61 used `iota`, 70 had
`UNPROVED` bodies `unit::check` refuses — while FOUNDATION §5 asserted such
probes had been removed. The three ledgers are now the whole population;
`every_probe_has_a_role` fails if a probe is added without one or a ledger names
a file that is gone.

## Reading checker output

`OK: N claim(s)` counts **claims only**. A unit that declares `schema`s and
proves them reports `OK: 0 claim(s)` and is nonetheless fully verified —
`scoping_convention` is exactly that case. A zero there does not mean "proves
nothing".

## The `.py` helpers

`closure_check.py`, `compound_term_scan.py`, `metalogic_census.py` and
`zf_pair_e2e_decode.py` are one-off measurement scripts over the export, not
probes, and no test runs them. Several measurements they produced have since been
re-established as Rust tests (`export::tests::*`), which is where a measurement
belongs once it has to stay true.
