# Root and ratio tests: mathematical collections

Tao Analysis I 7.5.1-7.5.4, in source
order. The public mathematics uses the existing native reals and extended
real tail extrema; it introduces no native feature, axiom, trust or overload.

## Exact data and source correspondence

| Source | Complete mathematical contract |
| --- | --- |
| 7.5.1 | Actual original-degree roots abs(a(n))^(1/n), defined as0 at zero terms; extended limsup<1 gives absolute and ordinary convergence, and extended limsup>1 gives ordinary and absolute divergence. Original integer starts are restored through actual positive-cutoff restrictions. At1 both convergence behaviors occur. |
| 7.5.2 | Every strictly positive complete real tail satisfies ratio liminf <= root liminf <= root limsup <= ratio limsup. The first exercise inequality is included; values0 and positive infinity remain in the extended domains. |
| 7.5.3 | Every nonvanishing original real tail has actual absolute successive ratios abs(a(n+1))/abs(a(n)). Ratio limsup<1 gives absolute/ordinary convergence; ratio liminf>1 gives ordinary/absolute divergence of the original signed series. Equality1 does not decide convergence. |
| 7.5.4 | The actual variable-base function positive_index_nth_root_tail(n)=n^(1/n), complete domain integer n>=1, has limit1. |

`is_strictly_positive_real_tail(start,c)` quantifies over every integer n>=start
and requires c(n)>0. `is_nonvanishing_real_tail(start,a)` uses the same complete
original domain and requires a(n)!=0. Actual ratios retain that entire domain
and evaluate the original successor n+1. Codomain positivity never authorizes
changing a function's complete input domain.

`positive_start_real_tail_root_magnitudes<start,a>` has start inN+ and a's
complete domain integer n>=start. Its zero and nonzero cases include every
real original term. Its n-th power is abs(a(n)); reindexing at native k uses
original degree start+k-1. The integer-start wrappers take a natural length
with start+length>=1, construct the actual restriction, and restore the full
original series. Such lengths exist for every original integer start.

## Forward proof dependencies

Eventual root bounds inside(0,1) give a genuine geometric majorant. For
limsup>1, arbitrarily late roots above1 give original magnitudes above1,
contradicting the necessary zero-term limit. Extended selectors are the actual
ones, including positive infinity; no finite candidate is supplied as a premise.

Eventual upper and lower positive ratio bounds give geometric envelopes by
induction. Existing fixed-positive-base nth-root limits and nonnegative
comparisons across exact original domains yield the outer root bounds.
Positive real separation of distinct nonnegative extended values gives both
liminf/limsup inequalities without an extended reciprocal operation. Actual
finite-prefix invariance supplies the arbitrary-integer-start chain.

For signed ratios, absolute data is strictly positive on every original index.
Its actual ratio function equals the new absolute-ratio constructor. The
convergence branch applies the complete chain and root criterion to that
actual absolute data. The divergence branch proves equality of the actual
root functions after absolute values/restriction, then uses the original
signed root-divergence theorem. Absolute-data series divergence alone is not
used to infer ordinary signed divergence.

For n^(1/n), actual integer values have successive ratios(n+1)/n=1+1/n,
with limit1 by existing constant, reciprocal and sum laws. The complete chain
forces both actual root extrema to1; finite-extrema limit equivalence gives
the limit. Its base is n, distinct from the fixed-base nth-root theorem reused
inside the geometric-envelope proof.

## Named source theorems

- `positive_start_real_tail_root_power`
- `positive_start_real_tail_root_bound_gives_magnitude_bound`
- `positive_start_real_root_reindex_uses_original_degree`
- `native_absolute_series_is_real_tail_absolute_convergence`
- `real_tail_absolute_restriction_commutes`
- `real_tail_absolute_convergence_restores_finite_prefix`
- `positive_start_root_eventual_bound_gives_absolute_convergence`
- `nonnegative_real_tail_has_nonnegative_extremal_limits`
- `positive_start_real_series_root_limsup_below_one_converges`
- `positive_start_real_series_root_limsup_above_one_diverges`
- `real_tail_series_root_limsup_below_one_converges`
- `real_tail_series_root_limsup_above_one_diverges`
- `integer_tail_has_positive_cutoff_length`
- `real_tail_limit_restricts_after_finite_prefix`
- `real_tail_limit_restores_finite_prefix`
- `nonnegative_extended_strict_pair_has_positive_real_between`
- `extended_real_not_le_gives_reverse_strict_order`
- `nonnegative_real_tail_eventual_comparison_bounds_limsup`
- `nonnegative_real_tail_eventual_comparison_bounds_liminf`
- `nonnegative_real_tail_extremal_limits_ignore_finite_prefix`
- `positive_real_tail_successive_ratio_value`
- `nonnegative_real_positive_natural_power_reflects_order`
- `positive_real_tail_ratio_upper_bound_gives_offset_bound`
- `positive_real_tail_ratio_lower_bound_gives_offset_bound`
- `positive_real_tail_ratio_upper_bound_gives_geometric_envelope`
- `positive_real_tail_ratio_lower_bound_gives_geometric_envelope`
- `positive_start_geometric_magnitude_upper_bound_gives_root_bound`
- `positive_start_geometric_magnitude_lower_bound_gives_root_bound`
- `positive_start_ratio_upper_bound_bounds_root_limsup`
- `positive_start_ratio_lower_bound_bounds_root_liminf`
- `positive_start_ratio_limsup_bounds_root_limsup`
- `positive_start_ratio_liminf_bounds_root_liminf`
- `positive_start_real_tail_ratio_root_extrema_chain`
- `positive_real_tail_ratios_commute_with_restriction`
- `real_tail_ratio_root_extrema_chain_after_positive_cutoff`
- `nonzero_real_absolute_value_is_positive`
- `nonvanishing_real_tail_absolute_values_are_strictly_positive`
- `real_tail_absolute_successive_ratio_value`
- `absolute_successive_ratios_are_positive_absolute_data_ratios`
- `positive_start_roots_commute_with_absolute_values`
- `real_tail_restricted_roots_commute_with_absolute_values`
- `real_tail_series_absolute_ratio_limsup_below_one_converges`
- `real_tail_series_absolute_ratio_liminf_above_one_diverges`
- `positive_integer_successive_ratios_are_one_plus_reciprocal`
- `positive_integer_successive_ratios_tend_to_one`
- `positive_integer_root_magnitudes_tend_to_one`
- `positive_index_nth_roots_are_integer_root_magnitudes`
- `positive_index_nth_root_tail_tends_to_one`

## Acceptance scope

The module source contains82 statements:48 named theorems,26 formation
claims,3 actual templates,2 actual non-template functions,2 predicates and
one explicit release of the existing reciprocal definition. Formation claims
publish genuine carrier/domain facts before dependent expressions are formed.

Applications compute actual zero and signed geometric roots, original root
degrees, an actual positive-infinity root limsup, harmonic/reciprocal-square
root and ratio limits1 with opposite convergence behavior, and signed ratio
tests. A complete original tail starting at-2 has the three exceptional terms
-42 before its later half-geometric data; the actual ratio limit is restored
across that prefix. The actual ratio limsup of n^n is positive infinity, obtained from its
proved actual root limsup and the complete comparison chain. The README
example computes the genuine half-geometric root data and invokes the general
criterion; its minimal local-import standalone check has passed.

Semantic controls distinguish false conclusions from named-premise refusals.
They cover strict root and ratio thresholds, zero terms and global ratio
nonvanishing, wrong original degree/base/sign, lost original indices, invalid
cutoffs/lengths, incomplete complete domains, wrong finite/infinite extrema
and wrong limits. All six strict gates pass: source82, public source82, full181, fresh133,
local minimal README11 and the byte-exact public minimal README11. All48
full-domain theorem contracts and34 semantic controls were checked. The
fresh133 artifact removes all48 generic contract wrappers while retaining
actual example proofs and formation facts. This accepts source7.5.1-7.5.4;
it does not claim whole-book completion.
