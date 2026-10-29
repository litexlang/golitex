# Metric sequences, completeness and contractions

The module imports `metric` and `real_series`. The former supplies the actual
carrier, real distance laws, balls and continuous/Lipschitz maps; the latter
supplies geometric real-sequence convergence for every 0 <= q < 1. The metric
module keeps its original lightweight import contract.

## Definitions and dependency order

1. `has_metric_limit(A,M,a,p)` says that for every positive epsilon, a positive
   integer cutoff makes the whole remaining sequence lie in the open ball at p.
   `a` has the exact domain N+ and codomain M.carrier; p lies in that carrier.
2. `is_metric_cauchy_tail` quantifies both indices beyond the supplied positive
   cutoff. `is_metric_cauchy` supplies such a cutoff for every positive epsilon.
   Completeness is existence of a carrier-valued limit for every such sequence.
   These definitions permit empty carriers; completeness there is vacuous.
3. Constant sequences converge, limits are unique, and convergence implies the
   Cauchy property. Pointwise equality and positive integer shifts preserve
   limits. Continuity at the limit point preserves limits; the Lipschitz result
   follows through the existing continuity theorem.
4. The actual real-line metric is constructed from `(R,real_line_distance)`.
   Its open balls are the ordinary absolute-difference intervals. Native real
   sequence limits and metric limits agree in both directions. Metric Cauchy
   implies native real Cauchy; existing real completeness then proves metric
   completeness of this actual instance.
5. `iterate<S,f,start>` is an actual recursive N-indexed function, starting at
   u(0)=start and satisfying u(n+1)=f(u(n)). `orbit_sequence` restricts the
   observations to positive indices u(1),u(2),... . No arbitrary orbit witness
   is postulated, and no function with a larger domain is retyped by assertion.
6. Lipschitz contraction gives an adjacent geometric bound by induction. Finite
   gap bounds follow by the triangle inequality and another induction. Their
   geometric upper bounds tend to zero by `real_series`, so the orbit is Cauchy.
   This is separated through the reusable vanishing-tail-bound criterion.
7. Completeness provides an orbit limit. Its continuous image and shifted orbit
   have the same limit, giving the fixed-point equation. Contraction proves
   uniqueness independently of completeness. A nonempty complete carrier then
   gives Banach unique existence. Only after this proof is the guarded actual
   `contraction_fixed_point` function constructed by unique existence.
8. Residual estimates use the triangle and Lipschitz bounds. Induction gives
   distance to any given fixed point at step n; combining these yields the
   a priori bound. Applying the residual bound at f(x) gives the a posteriori
   bound. These error theorems need a supplied fixed point, not completeness.

These are definition, well-definedness, existence, uniqueness and proof edges.
The source does not assume a fixed point in the existence theorem, and does
not assume the desired orbit convergence or geometric estimates.

## Exact domains and boundaries

A contraction has an existing real factor q with 0 <= q < 1 and the complete
Lipschitz inequality. Zero is allowed. Nonemptiness belongs to Banach existence,
not to the metric, Cauchy or completeness definitions. A supplied start already
establishes nonemptiness for the orbit theorem. At n=0 the natural power is
q^0=1, including q=0; positive-index zero-factor error bounds vanish.

The real-line model and generic source results are delivered. Arbitrary closed
subspaces of complete metrics, product metrics, metric topology, sequential
compactness, completion constructions and normed/Banach spaces remain later
work. The use of the word Banach here names the contraction theorem and does
not claim a completed functional-analysis course. Native `lim(a)` retains its
real-sequence-only contract; this module adds no metric overload.

See README.md and validation/ for the recorded clean and imported acceptance
boundaries. All source, proof journals, controls and notes stay under std/;
there is no authorization for a kernel or WD change.
