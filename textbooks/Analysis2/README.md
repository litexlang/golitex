# Tao Analysis II as a Litex project

This directory is the final-product surface for the Litex translation of
Terence Tao's *Analysis II*, fourth edition. The ordered project entrypoint is
[`litex.config`](litex.config).

Run the implemented project with:

```text
target/release/litex -compact -r textbooks/Analysis2
```

The project exports all eight chapters in source order as `chap1` through
`chap8`.
The Chapter 1 public metric-space surface includes:

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
Corollary 2.2.3 exposes named pointwise arithmetic combinations. Its seven
global preservation theorems are checked; the pointwise composition
identifications remain explicit trusts.
Section 2.3 adds concrete function images, real-function boundedness and
extremum attainment, and uniform continuity. Uniform continuity implying
continuity is checked; compact images, the maximum principle, and the
compact-to-uniform direction retain explicit proof boundaries.
Section 2.4 concretely models separations, connected spaces and subsets,
real order intervals, and values lying between two real values. Its real-line
characterization, connected-image theorem, and intermediate value theorem
remain explicit source-facing proof boundaries.
Section 2.5 adds the optional topology layer: topology laws, neighborhoods,
topological sequence limits, interior/exterior/boundary, closure and closed
sets, relative topology, topological continuity, open covers, compactness,
and connectedness. These interfaces are all concrete and checkable.

Chapter 3 exposes function limits, pointwise and uniform convergence,
bounded-function spaces, relational uniform distances, uniformly Cauchy
families, function-series partial sums, sup norms, and the Weierstrass
M-test. It then gives source-facing interfaces for exchanging uniform limits
with integration and differentiation, followed by polynomial presentations,
compact support, approximations to the identity, convolution, and the staged
Weierstrass approximation theorem. Riemann integrals and continuous
derivatives use concrete local
epsilon--delta/tagged-partition definitions rather than abstract interfaces.
The value of a function limit at a point of its domain
is checked directly, and global continuity of a uniform limit is checked from
the pointwise theorem.

Chapter 4 exposes formal power-series terms and partial sums, convergence
radii, real analyticity, derivative towers and Taylor coefficients, Abel's
endpoint theorem, summation by parts, and power-series convolution. It
constructs real exponential and logarithm selections, a coordinate-based
`ComplexNumber` carrier with arithmetic, conjugation, absolute value,
reciprocal, metric, and exponential interfaces, and real and complex
trigonometric functions together with a least-positive-zero definition of
`pi_real`. For example:

```text
forall x, y R:
    power_series_term(coefficients, center, 0, x) = coefficients(0)
    complex_add((x, 0), (y, 0)) = (x + y, 0)
```

The source-assigned algebra and analysis proofs remain explicit trust
boundaries. Radius of convergence, positive-base real power, and complex
exponential-series convergence now have concrete definitions. Chapter 4's
derivative and one-sided-limit vocabulary reuses Chapter 3's typed interfaces.
Complex limit laws and the real sine/cosine value relations are concrete.

Chapter 5 adds continuous periodic complex functions, their inner product and
L2 norm, characters, trigonometric polynomials, Fourier coefficients,
periodic convolution, approximation kernels, Fourier convergence, and
Plancherel. Chapter 6 adds finite real coordinate spaces, linear maps,
matrices, total/directional/partial derivatives, the chain and Clairaut
interfaces, contractions, and inverse/implicit function theorems. Chapter 7
adds open boxes, box covers, outer measure, Caratheodory measurability,
countable additivity, and measurable functions. Chapter 8 adds simple
functions, nonnegative and signed Lebesgue integrals, monotone/dominated
convergence, Fatou, Riemann compatibility, and Fubini.

All 224 numbered non-exercise items have source-facing definitions or theorem
interfaces: 32, 24, 34, 38, 18, 26, 28, and 24 items in Chapters 1--8.
Every registered chapter file gate succeeds. The chapters are not
proof-complete:
Chapter 1 contains 28 explicit `trust` statements, Chapter 2 contains 35, and
Chapter 3 contains 30. Chapters 4--8 contain 98, 12, 12, 21, and 17,
respectively. The entire project contains no `abstract_prop`.
The Section 4.6 coordinate implementation checks addition and multiplication
commutativity directly. Remaining structured-value projection limitations are
recorded as verifier blockers and are worked around with explicit coordinate
relations; this project does not modify the kernel.
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
