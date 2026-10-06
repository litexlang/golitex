# Numerical Analysis in a Nutshell

This standalone showcase studies Newton's method for `x^2 - 2 = 0`, starting
from `x₀ = 1`. Everything is kept in one `main.lit`, in this order:

- the residual, positive-real Newton update, checked executable step, recursive
  iterate, gap `gₙ = |xₙ² - 2|`, and comparison bound
  `bₙ = 4(1/4)^(2^n)`;
- the exact one-step identity, quadratic contraction, and proof of `gₙ ≤ bₙ`;
- two exact Newton updates and the concrete checkpoint `g₂ ≤ 1/64`.

```bash
target/release/litex -r showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell
target/release/litex -extractpython -f showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit
target/release/litex -extractc -f showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit
target/release/litex -strict -r showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/same_math_in_lean.lean
```

The two `# [-extract]` blocks are concatenated in source order before the
extractor verifies and emits `newton_sqrt_two_step : R -> R`. The agreement
proof between those blocks remains part of full-module verification and is not
sent to Python or C extraction. The step's explicit `x = 0` restart totalizes
the formula for this experimental backend. The proved iteration uses
`newton_sqrt_two : R+ -> R+`, starts at one, remains positive, and therefore
never takes the restart branch. The proof is over exact real arithmetic;
generated Python and C use floating point, so the proof does not cover
rounding, overflow, or NaN behavior.

The Lean file expresses the same mathematical iteration, proof, and small
example over `ℝ`; it does not model the experimental extraction wrapper. None
of the results is supplied as a setting field. The Litex file contains no
direct trust or local axiom.
