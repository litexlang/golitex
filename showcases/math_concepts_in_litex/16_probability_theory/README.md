# Probability Theory

This standalone showcase gives probability the measure-theoretic foundation
that precedes the finite calculations in
`8_probability_and_statistics_in_nutshell`. Its main line is:

```text
sigma-algebra + real series convergence
  -> Kolmogorov probability space
  -> countable additivity
  -> finite additivity and the ordinary event-probability calculus
  -> conditional probability and independence
  -> measurable random variables and pushforward distributions
```

Run the checked Litex module from the repository root:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/16_probability_theory
```

Run the handwritten Lean analogy through the repository's Mathlib environment:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/16_probability_theory/same_math_in_lean.lean
```

## Public mathematical interface

- `SigmaAlgebraSetting` carries a sample space, its measurable events, and
  empty, universe, complement, binary-intersection, and countable-union laws.
  Countable union is the native
  `index_union(N+, Omega, fn(n N+) power_set(Omega) {family(n)})`; the module
  no longer maintains a parallel set-builder implementation.
- `ProbabilitySpaceSetting` adds a real-valued probability function, empty
  mass zero, total mass one, nonnegativity, and countable additivity.
- `has_series_sum` defines the right side of countable additivity by ordinary
  convergence of recursive real partial sums; there is no unconstrained total
  `infinite_sum` function.
- `probability_of_disjoint_union` derives binary finite additivity by padding
  two events with empty events and applying countable additivity. From it the
  module proves the complement and difference formulas, monotonicity,
  inclusion-exclusion, the union bound, and `0 <= P(A) <= 1`.
- `conditional_probability` is guarded by positive evidence probability, and
  `are_independent` states factorization of intersection probability.
- `is_measurable_map` and `is_random_variable` use measurable preimages.
  `is_distribution_of` relates a supplied pushforward distribution to those
  preimages rather than postulating a selected distribution constructor.

The primary derived tracer is `probability_of_disjoint_union`. It constructs
the sequence `(A, B, empty, empty, ...)`, proves that its countable union is
`A union B` through indexed-union membership witnesses, proves the
corresponding probability series sums to
`P(A) + P(B)`, and uses uniqueness of real-series sums together with
`kolmogorov_countable_additivity`. Thus finite additivity is visibly a theorem,
not an extra probability axiom. Checked consumers then recover the familiar
event calculus. Two further consumers show that independence makes
positive-probability conditioning leave probability unchanged, and that any
candidate distribution carries measurability of its underlying map.

## Exact axiom boundary

The semantic core is the Kolmogorov system: nonnegativity, total mass one, and
countable additivity on a sigma-algebra. The settings also expose universe and
binary-intersection closure and empty-event probability zero. These are
standard consequences of the smaller axiom bases, retained as conservative
projection laws so exact-carrier function applications do not need to replay
the same derivations. Binary finite additivity and every event-probability
formula listed above are proved after that boundary.

The public Litex file contains no direct `trust`, global `axiom`, or
`abstract_prop`. The settings assume supplied sigma-algebra and probability
data; the module does not construct a probability measure on every measurable
space. It also stops before Borel generation, integration, expectation,
variance, almost-sure reasoning, laws of large numbers, and central limit
theorems. Those require later measure/integration layers rather than a finite
weighted-sum surrogate.

The indexed-union sigma-algebra signature and padded two-event tracer pass the
registered file runner. The direct three-case event sequence avoids nested
template materialization, while theorem-local sequence names keep generated
instances out of child proof environments. The handwritten Lean analogy is
unchanged because its native `Set.iUnion` already expresses the same
mathematics. See `math_collections.md` for the interface rationale and
dependency graph.
