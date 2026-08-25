# Probability Theory

This standalone showcase gives probability the measure-theoretic foundation
that precedes the finite calculations in
`8_probability_and_statistics_in_nutshell`. Its main line is:

```text
sigma-algebra + real series convergence
  -> generated sigma algebras and Borel(R)
  -> Kolmogorov probability space
  -> finite and countable event-probability calculus
  -> event limits, continuity, null/almost-sure events, Borel--Cantelli
  -> conditional probability and independence
  -> Dirac, conditioned, finite atomic, and pushforward probabilities
  -> measurable random variables and their distributions
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
- `generated_sigma_algebra<X>(generators)` is the intersection of all sigma
  algebras on `X` containing `generators`. The module proves both generator
  inclusion and every sigma-algebra closure law for the constructed family.
- `borel_sigma_algebra_on_R` specializes that construction to all bounded real
  open intervals. `real_open_interval_is_borel` is its immediate membership
  consumer; bounded open intervals generate the standard Borel sigma algebra.
- `ProbabilitySpaceSetting` adds a real-valued probability function, empty
  mass zero, total mass one, nonnegativity, and countable additivity.
- `has_series_sum` defines the right side of countable additivity by ordinary
  convergence of recursive real partial sums; there is no unconstrained total
  `infinite_sum` function.
- `probability_of_disjoint_union` derives binary finite additivity by padding
  two events with empty events and applying countable additivity. From it the
  module proves the complement and difference formulas, monotonicity,
  inclusion-exclusion, the union bound, and `0 <= P(A) <= 1`.
- `event_countable_intersection_is_event` derives countable-intersection
  closure by complements. `event_tail_union_after` and
  `event_tail_intersection_after` construct event tails, while `event_limsup`
  and `event_liminf` construct the usual events that occur infinitely often
  and eventually always.
- `probability_continuous_from_below` and
  `probability_continuous_from_above` prove continuity on monotone event
  sequences. `probability_countable_subadditivity` derives the countable union
  bound from finite prefix unions and continuity from below.
- `is_null_event` and `is_almost_sure_event` expose probability-zero and
  probability-one events. The module proves downward closure of null events,
  countable closure of null events, the complement equivalence between null
  and almost-sure events, and `first_borel_cantelli`.
- `conditional_probability` is guarded by positive evidence probability, and
  `are_independent` states factorization of intersection probability.
- `dirac_probability`, `conditioned_probability_measure`, and
  `finite_atomic_probability` are actual real-valued functions on the exact
  event carrier. Their corresponding `*_is_probability_space` theorems prove
  normalization, nonnegativity, and countable additivity. The finite atomic
  proof reduces to a finite sum of weighted Dirac laws; conditioning is
  restricted to positive-probability evidence.
- `is_measurable_map` and `is_random_variable` use measurable preimages.
  `pushforward_probability` constructs `B |-> P(X^{-1}(B))` on the exact target
  event carrier. The module proves that this function is both the distribution
  of `X` and a probability space on the target sigma algebra.
- `same_math_in_lean.lean` mirrors this last construction with Mathlib's native
  `Measure.map`, including its measurable-set evaluation law and preservation
  of `IsProbabilityMeasure`.

The primary derived tracer is `probability_of_disjoint_union`. It constructs
the sequence `(A, B, empty, empty, ...)`, proves that its countable union is
`A union B` through indexed-union membership witnesses, proves the
corresponding probability series sums to
`P(A) + P(B)`, and uses uniqueness of real-series sums together with
`kolmogorov_countable_additivity`. Thus finite additivity is visibly a theorem,
not an extra probability axiom. Checked consumers then recover the familiar
event calculus. The main limit tracer is `first_borel_cantelli`: it bounds
every tail union by the corresponding remainder of a convergent probability
series, uses continuity from above, and concludes that the limsup event is
null. The independent construction tracer is
`conditioned_probability_is_probability_space`; it intersects a disjoint
family with the evidence event and transports the resulting real series
through multiplication by `1 / P(evidence)`.

## Exact axiom boundary

The semantic core is the Kolmogorov system: nonnegativity, total mass one, and
countable additivity on a sigma-algebra. The settings also expose universe and
binary-intersection closure and empty-event probability zero. These are
standard consequences of the smaller axiom bases, retained as conservative
projection laws so exact-carrier function applications do not need to replay
the same derivations. Binary finite additivity and every event-probability
formula listed above are proved after that boundary.

The public Litex file contains no direct `trust`, global `axiom`, or
`abstract_prop`. The settings assume source probability data; the module then
constructs Dirac probability on any sigma algebra and constructs conditioned,
finite atomic, and pushforward probabilities from explicit source data. It
does not claim that every measurable space admits an unrelated probability
measure, nor does it implement Caratheodory extension from a premeasure or
outer measure. Integration, expectation, variance, almost-sure convergence,
laws of large numbers, and central limit theorems remain later layers.

The generated-sigma construction, Borel specialization, event-limit layer,
three concrete probability constructions, pushforward laws, and padded
two-event finite-additivity tracer are all executable declarations in
`main.lit`. See `math_collections.md` for the interface rationale and dependency
graph.
