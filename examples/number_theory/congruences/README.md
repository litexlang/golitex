# Imported integer congruences

The project imports std/number_theory as nt. main.lit proves that 17*17 and 2*2
are congruent modulo 5, then exercises every arithmetic law, negative operands,
zero dividends, negative native divisors and modulus 1. The last proof shows
why multiplication compatibility does not allow arbitrary cancellation.
contracts.lit checks all 12 theorem signatures over arbitrary parameters.
readme/main.lit checks exactly the short std README excerpt in isolation.

Run the complete focused gate from the repository root:

```bash
python3 examples/number_theory/congruences/check.py
```

The gate checks the source, example, contracts and README; each of 15 isolated
negative projects must reject only its final statement, at the phase recorded
in negative/expected.json. Controls cover false congruence, invalid domains,
divisibility argument order, missing premises, cancellation, strengthening a
modulus and an unsupported bodyless theorem. It also checks installed imports
with no LITEX_STD_PATH override under archive and shared-data layouts and
compares all packaged std files and WiX component references.

The source and callers exclude user trust and axioms. This is a focused
number-theory library gate, not a repository-wide or Lean certification.
