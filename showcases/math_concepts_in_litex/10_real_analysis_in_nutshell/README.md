# Real Analysis in a Nutshell

This standalone showcase makes epsilon-tail convergence explicit, proves
constant sequences converge, proves uniqueness of sequence limits, and then
uses that existence-and-uniqueness result to define a canonical `lim` selector.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/10_real_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/same_math_in_lean.lean
```

The Lean comparison defines closeness as the actual real inequality
`|a n - L| < ε` and derives uniqueness with `Nat.max` and the triangle
inequality. The published Litex file contains no direct trust or local axiom.
