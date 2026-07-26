# Tao Analysis II as a Litex project

This directory is the final-product surface for the Litex translation of
Terence Tao's *Analysis II*, fourth edition. The ordered project entrypoint is
[`litex.config`](litex.config).

Run the implemented project with:

```text
target/release/litex -compact -r textbooks/Analysis2
```

The current project exports Chapter 1 as `chap1` and the in-progress Chapter 2
as `chap2`. The Chapter 1 public metric-space surface includes:

- `$chap1::is_metric_space(X,dist)`, the concrete real, restricted,
  finite-dimensional `l1`/`l2`/`linf`, and discrete distance functions, and
  the checked defining-formula bridge `real_distance_eq_abs`;
- `$chap1::has_metric_limit`, `$chap1::is_metric_convergent`, metric balls
  with checked center-containment and membership/inequality lemmas, interior,
  exterior, boundary, closure, open/closed predicates, and the checked
  `metric_boundary_of_complement_is_boundary` bridge;
- the checked real-distance convergence equivalence, relative
  openness/closedness, subsequences, sequence limit points, Cauchy sequences,
  the checked theorems `convergent_subsequence_has_same_limit`,
  `metric_convergent_implies_cauchy`, and
  `cauchy_with_convergent_subsequence_converges`, and complete metric spaces;
- sequential compactness, boundedness, open covers, finite subcovers, and
  nested compact intersections.

For example, the checked `metric_ball_contains_center` theorem derives

```litex
center $in \chap1::metric_ball<X, dist>(center, radius)
```

from `$chap1::is_metric_space(X,dist)` and `radius $in R_pos`.

Chapter 2 currently exposes the concrete predicates
`$chap2::is_metric_delta_controlled_at`,
`$chap2::is_metric_continuous_at`, and
`$chap2::is_metric_continuous`. Its checked
`metric_continuous_implies_continuous_at` theorem projects domain continuity
to a chosen point. Theorem 2.1.4 is represented by concrete sequential and
open-neighborhood characterization predicates plus four trusted directions,
matching Tao's exercise-deferred proof boundary.
Theorem 2.1.5 has a checked sequential equivalence and concrete inverse-image
sets, while its open/closed inverse-image directions remain trusted.
Corollary 2.1.7 is checked in both its pointwise and global composition forms.
Section 2.2 currently adds a concrete real-function pairing into
`\chap1::finite_real_vector<2>` and concrete addition, subtraction,
multiplication, maximum, minimum, restricted division, and scalar maps. The
continuity statements in Lemmas 2.2.1--2.2.2 remain exercise-deferred trusts.

All 32 numbered non-exercise Chapter 1 items have source-facing definitions
or theorem interfaces. The ordered project run succeeds, but the chapter is
not proof-complete: it currently contains 28 explicit `trust` statements.
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
