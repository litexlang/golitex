# Concept Inventory

| Concept | Litex form | Why it is here |
| --- | --- | --- |
| two-point distribution | `prop` on native `finite_seq` | smallest nontrivial sample space |
| expectation and variance | `have fn` | executable statistics |
| three-point mean | `have fn mean3` | callable arithmetic mean `(a+b+c)/3` |
| least-squares center | `prop is_least_squares_center` | compares one center with every real candidate |
| three-point SSE decomposition | `thm` | exposes the nonnegative gap `3 * (candidate - mean)^2` |
| affine combination | `have fn` on native `finite_seq` | input to a genuine linearity theorem |
| linearity of expectation | `thm` | algebraic result with no unnecessary probability premise |
| conditional probability | guarded `have fn` | exposes the nonzero denominator |
| Bayes' rule | `thm` | connects one prior, likelihood, evidence, and posterior scenario |

The first version stops before independence, random-variable algebras, laws of
large numbers, inference, continuous distributions, and a general finite-sample
sum API. The least-squares result is intentionally specialized to three real
observations so its completing-square proof remains visible.
