# Probability and Statistics in a Nutshell

This standalone showcase moves from a two-point probability vector to
expectation, variance, linearity of expectation, and one coherent Bayes
calculation.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/same_math_in_lean.lean
```

The affine expectation theorem deliberately needs no probability-vector
premise: it is an algebraic fact about the weighted sum. The published Litex
file contains no direct trust or local axiom. The Lean comparison uses
real-valued probabilities, expectations, variance, and conditional
probability; it does not replace them with integer pairs.
