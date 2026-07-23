# Tao Analysis II as a Litex project

This directory is the final-product surface for the Litex translation of
Terence Tao's *Analysis II*, fourth edition. The ordered project entrypoint is
[`litex.config`](litex.config).

Run the implemented project with:

```text
target/debug/litex -runner -r textbooks/Analysis2
```

The current project exports Chapter 1 as `chap1`. Its public metric-space
surface includes:

- `$chap1::is_metric_space(X,dist)` and the concrete real, restricted,
  finite-dimensional `l1`/`l2`/`linf`, and discrete distance functions;
- `$chap1::has_metric_limit`, `$chap1::is_metric_convergent`, metric balls,
  interior, exterior, boundary, closure, and open/closed predicates;
- relative openness/closedness, subsequences, sequence limit points, Cauchy
  sequences, and complete metric spaces;
- sequential compactness, boundedness, open covers, finite subcovers, and
  nested compact intersections.

For example, the checked `metric_ball_contains_center` theorem derives

```litex
center $in \chap1::metric_ball<X, dist>(center, radius)
```

from `$chap1::is_metric_space(X,dist)` and `radius $in R_pos`.

All 32 numbered non-exercise Chapter 1 items have source-facing definitions
or theorem interfaces. The ordered project run succeeds, but the chapter is
not proof-complete: it currently contains 48 explicit `trust` statements.
Most correspond to proofs Tao assigns to exercises; others mark substantial
source proofs or finite-choice arguments not yet formalized. The `linf`
distance uses a trusted unique-maximum selection because instantiating the
more direct recursive template currently exposes a verifier name-resolution
problem. These boundaries are listed in `todo.lit` and in the working
blocker ledger under `scripts/Analysis2/`.

The mathematical interface design is maintained in
[`math_collections.md`](math_collections.md). Source inventories, translation
records, verifier captures, and blocker notes remain in
`scripts/Analysis2/`.
