# isa2fol

isa2fol translates Isabelle/ZF into plain first-order logic. Every theorem becomes a natural-deduction proof in NBG set
theory, which the [fol-zfc](https://github.com/AutoZFC/fol-zfc-comb) kernel checks.

- 9,404 of the 9,420 named theorems in Isabelle/ZF's eight sessions translate and check.
- The target has no meta-logic, no tactics and no function symbols: three predicates (`elem`, `eq`, `set`) and NBG's
  19 axioms.

**Why do this?** See [Why bring Isabelle/ZF down to first-order logic?](https://autozfc.github.io/webpage/why-first-order/)

## Docs

- [docs/FOUNDATION.md](docs/FOUNDATION.md): the target logic and the rules the translation keeps.
- [DESIGN.md](DESIGN.md): the reader, the IR and the lowering passes.

## Running it

```bash
bash scripts/01-install-toolchain.sh     # bazelisk and fol-zfc's proof_checker
bash scripts/02-install-swift.sh         # Swift toolchain
bash scripts/03-export-zf.sh             # export Isabelle/ZF to data/zf_export
swift build -c release
.build/release/isa2fol read data/zf_export
.build/release/isa2fol lower data/zf_export --emit OUT
scripts/check-unit.sh OUT                # kernel-check the emitted unit
```

Lowering the larger sessions needs 24–57 GB of RAM.

## License

Apache License 2.0, see [LICENSE](LICENSE). Copyright 2026 the isa2fol authors.
