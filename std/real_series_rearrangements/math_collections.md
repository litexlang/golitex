# Real series rearrangements: mathematical collections

## Source correspondence and actual data

Tao Analysis I 7.4.1 and 7.4.3 use original real terms at every natural index,
starting at zero, and an arbitrary bijection of the native naturals. Native N
and the complete integer tail `{j Z:j>=0}` agree as carriers. Formation claims
prove both directions and the returned-index membership before composition.
The actual complete composition is `a(p(n))`; its name deliberately describes
an index composition, since only the theorem hypotheses require a permutation.

The three actual templates are `zero_start_real_index_composition`,
`natural_zero_prefix_restriction` and `natural_zero_prefix_image_map`.
The latter two have the exact complete finite domain `closed_range(0,M)`;
their graph agrees with the original map there. The image-valued function
has the actual finite image as codomain. No original infinite-domain function
is retyped as a finite-domain function.

`natural_map_prefix_bound(p,M,B)` means every image of an index in the closed
prefix through M is at most B. `natural_index_inverse_pair(p,q)` contains both
inverse equations on every natural index. The latter is constructed with
unique preimages from bijectivity, rather than assumed.

## General proof dependencies

| Named theorem | Exact mathematical role |
| --- | --- |
| natural_map_has_bounded_finite_prefix | For any natural map and M in N, its actual finite nonempty prefix image has a natural maximum B. |
| injective_natural_map_prefix_is_bijective_to_image | An injective map restricts to a bijection from its exact closed prefix to its actual image. |
| zero_start_rearranged_partial_sum_is_image_sum | Under injectivity, the actual rearranged partial sum equals the finite sum of original terms on that image. |
| nonnegative_real_finite_sum_increases_with_subset | For finite X subset Y and actual f:X->R, g:Y->R agreeing on X with g nonnegative, sum(f)<=sum(g). |
| bounded_natural_prefix_image_is_in_closed_prefix | A supplied actual prefix bound puts its image inside closed_range(0,B). |
| nonnegative_injective_zero_tail_partial_sum_domination | The actual rearranged partial sum through M is at most the original through B, given the actual prefix bound. |
| nonnegative_real_series_partials_are_below_candidate | At any integer start, every nonnegative partial sum is at most its real series candidate L. |
| zero_start_index_composition_preserves_nonnegative_terms | Any natural index composition preserves nonnegativity of all original terms. |
| nonnegative_injective_zero_tail_series_converges | Original nonnegative convergence and injectivity bound all actual rearranged partial sums and give convergence. |
| upper_bounded_real_series_partials_bound_candidate | At any integer start, an actual real upper bound H for all partial sums bounds every candidate L; no sign hypothesis is needed. |
| nonnegative_injective_zero_tail_series_candidate_bound | Under injectivity and nonnegative original terms, the rearranged candidate is at most the original candidate. |
| natural_bijection_has_inverse_index_map | Every natural bijection has an actual inverse natural bijection satisfying both equations. |
| nonnegative_zero_start_series_rearrangement_candidate | Source7.4.1, with an arbitrary original candidate L, from the two candidate inequalities using the actual inverse. |
| nonnegative_zero_start_series_rearrangement_has_same_sum | Source7.4.1 at the existing guarded original sum. |
| zero_start_index_composition_commutes_with_absolute_values | Exact equality of the complete absolute/composed functions for any natural map. |
| absolutely_convergent_zero_start_series_rearrangement_converges_absolutely | Source7.4.3 absolute and ordinary rearranged convergence. |
| zero_start_index_composition_commutes_with_sum | Exact equality of composition of actual termwise sums and the sum of the compositions. |
| signed_plus_absolute_zero_tail_is_nonnegative | Every actual term a(n)+abs(a(n)) is nonnegative. |
| absolutely_convergent_zero_start_series_rearrangement_candidate | Source7.4.3 preserves any signed original candidate L. |
| absolutely_convergent_zero_start_series_rearrangement_has_same_sum | Source7.4.3 at the existing guarded signed original sum. |

The actual finite subset comparison splits Y into X and Y minus X, uses
nonnegativity on the latter, and transports the finite sums through the exact
restrictions. This preserves the original summand's complete domain. The
finite-image sum identity uses the existing substitution theorem on supersets.
Existing cardinality, finite-sum, monotone-limit, real/extended-order and
sequence-limit comparison interfaces supply the remaining proof steps.

For source7.4.1, nonnegative monotone partial sums lie below the original
candidate L. Actual finite-prefix bounds dominate every rearranged partial sum
by an original one. The existing boundedness criterion gives convergence.
The same argument with the constructed inverse gives the opposite candidate
inequality. No positivity condition is imposed on an arbitrary partial-sum
upper bound H. The source proof's printed bound m<=N is read as m<=M for its
actual fixed finite prefix.

For source7.4.3, first apply the nonnegative theorem to the actual absolute
values, proving absolute and ordinary rearranged convergence. Write their
candidates as A and T, with original signed candidate L. The original
nonnegative series a+abs(a) has candidate L+A; its rearrangement has the same
candidate. Exact composition/addition equality and series algebra give T+A
for the same complete series. Candidate uniqueness yields T=L. This equivalent
proof retains every source quantifier and hypothesis; it avoids introducing a
second signed-series model or an unproved leftover-set estimate.

## Independent applications and boundaries

Applications construct the adjacent pair swap, including index0, and a finite
three-cycle that is not an involution. Both rearrange the positive geometric
series of sum2 and signed geometric series of sum2/3. Exact terms, ordinary
convergence guards and selected signed sums are checked. The actual absolute
sum of the three-cycle signed example is2.

The reciprocal-square example from source7.4.2 uses the actual translated
positive-index reciprocal-square function. Its rearranged first four terms
are1/4,1,1/16,1/9 and the selected sums agree. No value of zeta(2) is asserted.

The successor map is injective but not surjective; its actual geometric sum
is1 instead of2. The duplicate-zero map is surjective but not injective; its
actual third partial sum is5/2, ruling out the original sum2. Boundary controls
also check a false actual prefix bound, an actual divergent absolute series,
wrong signed/absolute sums, wrong inverse/term values, invalid finite-prefix
endpoints, a positive-only original domain and a map with negative outputs.
The signed-data call to the nonnegative theorem is a named-premise refusal;
its conclusion is independently true by the absolute theorem and is not
advertised as a mathematical counterexample.

The source has35 statements:20 named theorems,10 ordinary formation claims,
three actual templates and two predicates. Formation claims remain in fresh
consumers before dependent theorem or selector goals. No new mathematical
axiom, trust, native feature or operation overload is introduced.
