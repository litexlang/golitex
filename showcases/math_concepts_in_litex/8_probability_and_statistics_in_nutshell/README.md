# Probability and Statistics in a Nutshell

This standalone showcase moves from a two-point probability vector to
expectation, variance, a three-point least-squares center, and one coherent
Bayes calculation.

```bash
target/release/litex -strict -r showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/same_math_in_lean.lean
```

The affine expectation theorem deliberately needs no probability-vector
premise: it is an algebraic fact about the weighted sum. The least-squares
center proof uses the identity

```text
S(r) = S(mean3(a,b,c)) + 3 * (r - mean3(a,b,c))^2
```

so the remainder is visibly nonnegative for every real candidate `r`. For the
tracer data `(1, 2, 5)`, `mean3 = 8/3`, the minimum sum is `26/3`, and the
candidate `2` gives `10 = 26/3 + 4/3`.

The published Litex file contains no direct trust or local axiom. The Lean
comparison uses real-valued probabilities, expectations, variance, and
conditional probability; it does not replace them with integer pairs.

Migration status: the complete Litex file still has five failed statements
around the finite-sequence function carrier, affine expectation, and fair-coin
consumers. The equality-bridge update did not close those failures. See
[`和showcase有关.md`](../../../plan/迁移的plan/和showcase有关.md) for current
evidence. The passing least-squares and Bayes excerpts do not establish that
the full module passes.
