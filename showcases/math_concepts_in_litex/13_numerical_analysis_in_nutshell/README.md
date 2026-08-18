# Numerical Analysis in a Nutshell

This standalone showcase studies Newton's method for `x^2 - 2 = 0`, starting
from `x₀ = 1`. Everything is kept in one `main.lit`, in this order:

- the residual, Newton step, recursive iterate, gap
  `gₙ = |xₙ² - 2|`, and comparison bound `bₙ = 4(1/4)^(2^n)`;
- the exact one-step identity, quadratic contraction, and proof of `gₙ ≤ bₙ`;
- two exact Newton updates and the concrete checkpoint `g₂ ≤ 1/64`.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/same_math_in_lean.lean
```

The Lean file expresses the same definitions, proof, and small example over
`ℝ`. None of the results is supplied as a setting field. The Litex file
contains no direct trust or local axiom.
