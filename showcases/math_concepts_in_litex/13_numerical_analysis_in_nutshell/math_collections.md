# Concept Inventory

| Concept | Litex form | Why it is here |
| --- | --- | --- |
| residual | `have fn` | names the equation error `x² - 2` |
| Newton update | positive-real `have fn` | keeps division valid and the recursive iterate positive |
| Newton iterate | inductive `have fn` | turns individual updates into a sequence indexed by `n` |
| gap | `have fn` | records `gₙ = |xₙ² - 2|` |
| comparison bound | `have fn` | records `bₙ = 4(1/4)^(2^n)` |
| gap bound | inductive `thm` | proves `gₙ ≤ bₙ` for every natural `n` |

The exact scaled-residual identity, iterate lower bound, quadratic contraction,
and bound recurrence remain supporting lemmas inside the same `main.lit`; they
are not extra concepts in the reader-facing path. The scope stops before
floating-point roundoff, stopping criteria, interpolation, quadrature,
numerical ODEs, and matrix algorithms.
