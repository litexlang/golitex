# Tao Analysis I as one Litex project

The Analysis chapter files are one project, declared by
[`litex.config`](litex.config).
The manifest exports each chapter in source order; it does not itself assert
mathematical facts.

Run the project entrance with:

```text
target/debug/litex -r textbooks/Analysis
```

Run an individual registered chapter from the project directory with:

```text
(cd textbooks/Analysis && ../../target/debug/litex -f chapter10-differentiation.lit)
```

Earlier exports are loaded by the ordered manifest.  Later chapters refer to
their public source-facing interfaces by canonical name:

```text
chap9::has_function_limit(...)
chap10::cauchy_mean_value_theorem(...)
```

There is no local-import statement or unqualified import completion.  A
chapter-local definition remains bare; every earlier chapter definition keeps
its `chapN::` qualifier, so its identity is explicit even when another export
uses the same short name.

Some similarly named source definitions remain deliberately local.  In
particular, Chapter 7 uses a non-strict series-tail convention (`<= epsilon`)
where Chapter 6 uses a strict sequence-tail convention (`< epsilon`), and
Chapter 11's monotonicity predicates are non-strict whereas Chapter 9's are
strict.  These are not duplicate interfaces to erase.

## Chapter 3 cardinality surface

Chapter 3 defines equal cardinality through a bijection and proves the
Cantor-Schroeder-Bernstein theorem as `cantor_schroeder_bernstein`: injections
in both directions produce a bijection.  The proof iterates `g(f(x))` from the
part of the first set outside `g`'s range, uses `f` on the resulting reachable
region, and uses the unique inverse of `g` on its complement.  Later chapters
can call it as `chap3::cantor_schroeder_bernstein` without importing a separate
cardinality module or assuming any form of choice.

## Chapter 6 concept-first surface

Chapter 6 separates the candidate-limit relation `$has_limit(a,L)` from the
existence property `$is_convergent_sequence(a)`, proves the named uniqueness
result `sequence_limit_unique`, and then exposes the selected value `lim(a)`
with `have fn ... by exist!`.  Limit laws such as `seq_add_converges_to`
consume `has_limit` directly; they are a sibling branch rather than a result
that depends on `lim`.

A representative use is:

```litex
forall a seq(R):
    $is_convergent_sequence(a)
    =>:
    $has_limit(a, lim(a))
```

The same chapter exposes real exponentiation through rational approximation.
`rational_power_approx_seq(x,q)` is the sequence `n |-> x^(q(n))`, and
`real_power_agrees_with_rational_power` verifies the rational case by proving
that the constant rational approximation has limit `x^q`:

```litex
by thm real_power_agrees_with_rational_power(x, q)
$has_limit(rational_power_approx_seq(x, fn(n N_pos) R {q}), x^q)
```

The corresponding human design map is in `math_collections.md`; the runtime
definition graph exposes the actual typed dependencies retained by an
executed project environment.  The Chapter 5 identification between builtin
`R` and the rational-Cauchy construction is stated explicitly through the
axioms `cauchy_sequence_representative_in_Q_exists` and
`real_cauchy_sequence_has_limit_in_R`; these are foundational compatibility
assumptions, not unfinished Chapter 5 proofs.

## Chapter 8 infinite-set interface

Chapter 8 builds on Chapter 3's bijection and finite-cardinality interfaces.
Its first layer exposes `$embeds_into`, `$is_countably_infinite`,
`$is_at_most_countable`, and `$is_uncountable`, together with closure under
subsets, images, binary unions, and Cartesian products. The source-facing
`union_of_two_countable_sets_is_countable` now verifies by an even/odd
interleaving, followed by the at-most-countable and infinite bridges.
`integers_are_countable` enumerates the range of `n |-> -n`, proves
`Z = N union (-N)`, and then applies that union theorem. The later product and
rational-countability proofs reuse these named results.  The countable-family
union theorem also verifies: it uses the explicit choice axiom to select one
injective coding graph per fiber and pairs the outer and inner natural codes.

The next layer represents countable-set sums by composing a displayed
enumeration with the summand, then relates finite absolute subsum bounds to
sums over arbitrary supports. Chapter 8 also provides Cantor's theorem,
function-valued infinite Cartesian products, explicit choice-axiom
interfaces, partial/total/well-order predicates, strong induction, and Zorn's
maximal-element principle. The detailed concept roles and dependency order
are recorded in [`math_collections.md`](math_collections.md).

Proof boundaries remain visible. Finite subsum comparison and capture,
coordinate-swap transport, nonzero-support countability, bijection change of
variables, and finite-total-order well-ordering are checked.  The remaining
`trust` is concentrated in enumeration independence, the analytic row-first
core of Fubini, Riemann rearrangement, the binary-decimal injection, and four
good-chain lemmas.  There is also a known finite-support definition defect:
the current countable-series predicate demands a bijection `N_pos -> X`, so
empty and finite supports need a separate finite-sum branch before the general
addition and zero-scalar laws can be proved.  The axiom of choice remains an
explicit `axiom`; checked callers do not erase that provenance.

## Chapter 10 differentiation interface

Chapter 10 keeps a candidate derivative, its existence predicate, and its
selected value distinct: `$has_derivative_at(X,f,x,L)`,
`$is_differentiable_at(X,f,x)`, and `derivative(X,f,x)`.  At function level,
`$is_differentiable_on(X,f)` and `$has_derivative_function_on(X,f,df)` quantify
only over Chapter 9 limit points.  `derivative_function(X,f)` is the partial
function on the differentiability locus, so it does not manufacture values at
isolated or nondifferentiable points.  Corollary 10.1.12 combines derivative
continuity at limit points with the elementary fact that every function is
continuous at an isolated domain point.

The Chapter 10 inverse-derivative theorems use
`chap9::is_inverse_pair_on` directly.  Its inverse has codomain `X`, while
Litex still permits it wherever the analysis interface accepts a real-valued
function.  The inverse function theorem is fully checked: its proof composes
the inverse with the reciprocal of the forward difference quotient on the
exact nonzero subtype.

The two directions of Proposition 10.1.7 are exposed as reusable theorems,
and the source equivalence between derivatives and Newton approximations is
also stated directly.  In Section 10.5, `lhopital_rule_first` returns one
punctured radius together with the quotient limit on that same local carrier.
`lhopital_rule_second` is the complete right-hand theorem: it returns both
denominator nonvanishing on `(a,b]` and the quotient limit.

## Chapter 11 integration surface

Chapter 11 follows the dependency chain documented in
[`math_collections.md`](math_collections.md). Its central public interfaces
are the predicates `$is_partition_of_bounded_interval`,
`$is_finer_partition_than`, `$is_piecewise_constant_on`, and
`$is_riemann_integrable_on`; their corresponding construction and value APIs
are `interval_length`, `common_refinement`,
`refinement_fiber`, `refinement_owner`, `refinement_fiber_sum`,
`piecewise_constant_integral_with_partition`,
`piecewise_constant_integral`, `upper_riemann_sum`, `lower_riemann_sum`,
`upper_riemann_integral`, `lower_riemann_integral`, and `integral_on`. The
Riemann-sum layer also exposes the set-valued object
`function_values_on_subset`, selected `upper_riemann_sum_piece` and
`lower_riemann_sum_piece` values, and theorem interfaces from a constant
majorant/minorant to each piece and then to a fixed partition sum.

Most compressed source arguments in this chapter are expanded into checked
Litex proofs. The remaining source-deferred steps are not presented as
checked: every direct `trust` says whether the source leaves the proof to an
exercise or gives a proof route with a specific step left implicit, followed
by the exact unexpanded Litex obligation. The left-endpoint integral uses the
explicit restriction `fn(y '[a,x]) R {f(y)}`. Its subinterval integrability is
checked from the already visible two-piece additivity interface. The selected
left-endpoint integral is then constructed by checked unique existence; it has
no direct trust boundary.

Its lower-level objects `partition_piece_containing`,
`upper_riemann_piece_height`, and `lower_riemann_piece_height` expose the
unique piece at a point and its sup/inf height; the sum-piece values are
verified height-times-length consequences. The canonical objects
`upper_riemann_partition_step_function` and
`lower_riemann_partition_step_function` turn those heights into actual
piecewise-constant majorant/minorant witnesses. Their fixed-partition
integrals are the selected upper/lower sums, so Proposition 11.3.12 is checked:
the Darboux extrema equal the corresponding extrema over all selected Riemann
sums. The noncanonical epsilon interface `$has_darboux_approximation` supplies
fresh lower and upper step witnesses for each requested precision. Its checked
addition transport, together with candidate-level upper/lower sum transports,
proves Theorem 11.4.1(a): integrable functions are closed under addition and
`integral_on` is additive. Sign-sensitive candidate transports prove the
scalar multiplication law, including its integral equality. The same witness
interface proves maximum closure; minimum closure follows by negation.
For nonnegative products, `riemann_integrable_nonnegative_bounded_has_clamped_darboux_approximation`
supplies brackets `0 <= h <= f <= g <= M`; their product gap is bounded by the
two input gaps weighted by `M_f` and `M_g`. This checks the nonnegative case of
Theorem 11.4.5, from which squares and arbitrary products follow.
The small-oscillation route is also checked after a partition is supplied:
piece extrema realize least-upper-bound/infimum values, each rectangle gap is
bounded by oscillation times interval length, and finite additivity turns the
piece bounds into the global Darboux gap. Consequently
`darbouxs_criterion_from_small_oscillation_partitions` has no direct trust.
The local one-indexed series notation is also connected back to Chapter 7:
`one_indexed_partial_sum_matches_chapter7` and the two series-sum transport
theorems prove that both presentations express the same convergence witness.
Corollary 11.6.5 therefore reuses Chapter 7 for positive exponents; its
nonpositive branch is checked directly with the zero test.
For Proposition 11.7.1, rational and irrational density provide witnesses in
every positive-length partition piece; zero-length pieces contribute zero.
The resulting upper sum is exactly one and lower sum exactly zero on every
partition of `[0,1]`, so both displayed Dirichlet integral values are checked.
Stieltjes layer mirrors the last three with `upper_riemann_stieltjes_integral`,
`lower_riemann_stieltjes_integral`, and `stieltjes_integral_on`; its interval
weight is `alpha_interval_length`. Its finite base now also has
`piecewise_constant_riemann_stieltjes_integral_piece_contribution`,
`piecewise_constant_riemann_stieltjes_integral_with_partition`, and
`piecewise_constant_riemann_stieltjes_integral`; the relational specifications
remain the bridge back to displayed witnesses. The relational specification
`$has_alpha_interval_length` and its theorem
`alpha_interval_length_has_value` are the stable bridge from that value to its
endpoint cases.

The ordinary `interval_length` selector now has checked existence and
uniqueness. Its uniqueness proof separates the empty case from the nonempty
midpoint theorem `nonempty_interval_endpoint_representation_unique`, so
different open/closed endpoint presentations cannot silently assign different
values.

The final Chapter 11 layer keeps the same distinction: the integral function
from a left endpoint is the value API `integral_from_left_endpoint`, while
`$is_antiderivative_of`, `$maps_closed_interval_to_closed_interval`, and
`$is_composition_on_closed_interval` are assumptions about displayed
functions. FTC, integration by parts, and change of variables are theorems.
The source-facing antiderivative uniqueness statement is also checked on every
bounded interval: subtract the two antiderivatives, restrict to the closed
subinterval between any two points, and apply the checked zero-derivative
constancy theorem. This covers open, half-open, degenerate, and empty interval
forms without a new endpoint-form API.
The left-endpoint selector is available only when the integrand is Riemann
integrable on the parent interval. The changing-domain restriction is written
directly as `fn(y '[a,x]) R {f(y)}`; the chapter checks that this restriction
is Riemann integrable. `integral_from_left_endpoint_has_value` is its stable
specification theorem. The selector is checked by unique existence even though
the types `f : '[a,b] -> R` and `x : '[a,b]` depend on the earlier parameters
`a,b`. The canonical function satisfies the pointwise global predicate by
`selected_left_endpoint_integral_is_integral_function`.

The checked finite-regrouping bridge consists of
`$is_refinement_fiber`, `refinement_fiber`, and
`refinement_fiber_partitions_coarse_piece`: it identifies the nonempty fine pieces
inside a coarse piece and proves that they partition that coarse piece. Empty
fine pieces are deliberately excluded, since they do not have a unique coarse
owner and their later contributions vanish. Conversely,
`nonempty_fine_piece_has_unique_coarse_piece` and `refinement_owner` give every
nonempty fine piece its unique coarse owner. The checked
`refinement_owner_is_in_refinement_fiber` and
`refinement_fiber_member_has_owner` make those two descriptions mutually
usable: membership in a fiber and ownership by its coarse piece agree.
`nonempty_refinement_support` removes the ownerless empty pieces, and
`refinement_fiber_family_is_finite_unique_cover` supplies the corresponding
finite unique-cover instance for generic regrouping.
The checked
`refinement_fiber_has_finite_representative` bridge supplies the finite carrier
needed by the selected inner value `refinement_fiber_sum`. The reusable
relation-first shape is `$is_finite_indexed_subfamily`,
`$has_indexed_fiber_sum`, and `$is_finite_unique_cover_of`, followed by the
checked finite-sum theorem `finite_set_sum_over_unique_cover`. A caller supplies
a shared ambient family `U`, an outer summand on `U`, and a proof for each
displayed fiber value. The source family is a subfamily of `U`, so deleting one
index changes the summation family but not the weight itself. Its proof has checked empty and
singleton cases, disjointness, residual-cover and residual-summand transport,
then an induction step using the Chapter 7 finite disjoint-union sum law. It is
a reusable finite-combinatorics theorem, not a trusted Chapter-11 numerical
API. `refinement_fiber_cover_reindexes_ambient_sum` is its checked Chapter 11
consumer: it regroups a sum over nonempty fine pieces into a sum of the
corresponding coarse-piece fibers. Later rectangle and Darboux constructions
can use `U=Pfine` and the same ambient-weight interface.

`interval_length_reindexes_over_refinement_fiber` is the next geometric
specialization: each fiber partitions its coarse piece, so its lengths sum to
the coarse length. `constant_rectangle_reindexes_over_partition` then keeps a
fixed height and distributes the corresponding rectangle over any partition
with that length equality. These declarations are the intended bridge from
finite regrouping to Proposition 11.2.13.
`partition_removal_partitions_bounded_remainder` is also checked: after a
piece is selected whose complement is a bounded interval, it transfers finite
coverage and uniqueness to the remaining pieces.
The selection chain is now explicit and checked. The prop
`$is_strictly_left_of_interval` orders disjoint nonempty bounded intervals;
`$is_pairwise_strictly_ordered_nonempty_interval_family` classifies the finite
families to which `finite_pairwise_ordered_nonempty_intervals_have_leftmost`
applies. `removing_leftmost_partition_piece_leaves_bounded_interval` proves
that the selected leftmost piece has a bounded-interval complement, while
`partition_has_removable_piece` handles empty pieces separately. These are
relations and existential theorems, not canonical endpoint or leftmost-piece
objects. The bounded-remainder proof still depends transitively on the visible
trust in `bounded_connected_subsets_are_bounded_intervals`.
`intersection_of_bounded_intervals_is_bounded_interval` uses the same
bounded-and-connected route and is also checked relative to that single
foundational boundary.
`interval_weight_is_finitely_additive_over_partition` now checks the shared
empty case, cardinality induction, residual-family step, and finite-sum
regrouping for any bounded-interval weight with an additive endpoint split.
Theorem 11.1.13 is its ordinary-length consumer and no longer contains a
theorem-wide trust. Its direct numerical trust interface is now only
`interval_length_adds_across_bounded_difference`; its geometric selection
route is checked relative to the foundational bounded-connected
characterization just noted.
`piecewise_constant_integral_with_partition_reindexes_over_refinement`
composes them with empty-piece removal and unique-cover regrouping, and
Proposition 11.2.13 then sends two partitions to their selected common
refinement. This route is checked by the full Analysis project runner. The
remaining trust on this route is therefore geometric, not a duplicate trust in
finite induction or step-integral independence.

For example, once `P` and `Q` have been shown to partition `I`, derive their
carrier facts and use the selected refinement directly:

```litex
by thm partition_is_set_of_real_subsets(I, P)
by thm partition_is_set_of_real_subsets(I, Q)
have Rf finite_set = common_refinement(I, P, Q)
$is_common_refinement_of_partitions(I, P, Q, Rf)
by thm common_refinement_is_partition_and_finer(I, P, Q, Rf)
```

For a fixed partition, the upper and lower sums are likewise callable values.
Their `*_has_value` theorems are the stable imported-module bridge from a
selector back to its relational specification:

```litex
have U R = upper_riemann_sum(I, P, f)
by thm upper_riemann_sum_has_value(I, P, f)
$has_upper_riemann_sum(I, P, f, U)
```

The selected step-integral and ordinary/Stieltjes integral values are
verified interfaces. Their remaining `trust` is limited to endpoint geometry,
approximation, and later gluing theorems recorded in
`scripts/Analysis/todo/03_integration_and_language_blockers.md`.

The Stieltjes piecewise-constant base now mirrors the ordinary one: canonical
piece and fixed-partition selectors are linked to the existing relation, and
the global selector is justified by alpha-length refinement transport through
a common refinement. Lemma 11.8.4 now reuses the checked generic
interval-weight induction; its remaining upstream debt is the foundational
bounded-connected characterization and
`alpha_interval_length_adds_across_bounded_difference`, not endpoint-piece
selection or a second trusted finite-additivity proof. The full Analysis
runner verifies this composition.
The corresponding checked order
layer compares weighted rectangles on one piece, sums them on one partition,
and sends the two witness partitions to a common refinement; it is exposed by
`piecewise_constant_stieltjes_minorant_integral_le_majorant_integral`.
That comparison now checks the first conclusion of Theorem 11.10.2: every
piecewise-constant function has equal upper and lower Stieltjes envelopes. The
theorem's remaining direct debt is only the finite identity with the ordinary
integral of `f*dalpha`.
