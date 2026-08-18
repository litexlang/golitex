# Numerical Analysis in a Nutshell

This standalone showcase studies Newton's method for `x^2 - 2 = 0`, starting
from `x₀ = 1`. Its reader-facing path is deliberately short:

- `newton_iteration.lit` defines the residual, Newton step, recursive iterate,
  gap `gₙ = |xₙ² - 2|`, and comparison bound `bₙ = 4(1/4)^(2^n)`;
- `gap_bound.lit` proves `gₙ ≤ bₙ`, including the exact one-step identity
  and quadratic contraction used by the induction;
- `main.lit` shows two exact Newton updates and applies the bound at `n = 2`.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/same_math_in_lean.lean
```

The Lean file expresses the same definitions, proof, and small example over
`ℝ`. None of the results is supplied as a setting field. The Litex files
contain no direct trust or local axiom.
