# Discrete Mathematics in a Nutshell

This standalone showcase follows finite counting into a recursive binomial
coefficient and a checked proof of Pascal's identity. It reuses Litex's native
finite sets and `finite_set_size`; the recurrence is published directly as a
theorem instead of being wrapped in a one-use proposition.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell
lean showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/same_math_in_lean.lean
```

The published Litex file contains no direct trust or local axiom.
