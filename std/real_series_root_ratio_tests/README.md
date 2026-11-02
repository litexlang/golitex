# Real series root and ratio tests

Tao Analysis I 7.5.1-7.5.4: the root test, the complete ratio/root extrema
chain, the ratio test for nonzero real terms, and the actual limit n^(1/n)->1.
All series keep their complete original integer-tail domain. Actual tail
liminf/limsup values are extended reals, including zero and positive infinity.

| Source | General interface |
| --- | --- |
| 7.5.1 | `positive_start_real_series_root_limsup_below_one_converges` and `positive_start_real_series_root_limsup_above_one_diverges`; their `real_tail_series_...` counterparts restore any finite original prefix. |
| 7.5.2 | `positive_start_real_tail_ratio_root_extrema_chain` and `real_tail_ratio_root_extrema_chain_after_positive_cutoff`; all three inequalities, including the lower bound. |
| 7.5.3 | `real_tail_series_absolute_ratio_limsup_below_one_converges` and `real_tail_series_absolute_ratio_liminf_above_one_diverges`. |
| 7.5.4 | `positive_index_nth_root_tail(n)=n^(1/n)` on integer n>=1, and `positive_index_nth_root_tail_tends_to_one`. |

`positive_start_real_tail_root_magnitudes<start,a>` preserves the original
degree n, with value0 when a(n)=0. It does not use the shifted reindex as its
degree. For a nonpositive original start, choose any natural length with
start+length>=1 and use the actual restriction at start+length. Such a length
exists for every integer start. No original data is extended or retyped.

`is_strictly_positive_real_tail` requires every original term to be positive.
Its actual successive-ratio function is c(n+1)/c(n).
`is_nonvanishing_real_tail` requires every original real term to be nonzero.
Its `real_tail_absolute_successive_ratios` has value abs(a(n+1))/abs(a(n)).
The convergence criterion gives absolute and ordinary convergence; the
strict divergence criterion gives ordinary and absolute divergence of the
original signed series.

At threshold1, neither test determines convergence. The actual harmonic and
reciprocal-square data from `real_nonnegative_series` both have root limit1
and absolute-ratio limit1, while only the reciprocal-square series converges.
The constant unit series is another divergent threshold example.

The following complete example computes the actual root function for(1/2)^n,
its limit and limsup, and then invokes the general root criterion. It also
checks the distinct variable-base nth-root limit.

```ini
[import std]
RootRatio = real_series_root_ratio_tests
Real = real_sequences
Limits = real_sequence_limsup
Power = real_power_laws
[alias]
rt = RootRatio::main
rs = Real::main
limits = Limits::main
power = Power::main
[export]
main = "./main.lit"
```

```litex
have fn readme_half_terms(n {j Z:j>=1}) R=(1/2)^n

release thm fn_set_member(readme_half_terms,fn(n {j Z:j>=1}) R)

claim:
    ? \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms> = \rs::real_tail_constant<1,1/2>
    release thm fn_set_member(\rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>,fn(n {j Z:j>=1}) R)
    release thm fn_set_member(\rs::real_tail_constant<1,1/2>,fn(n {j Z:j>=1}) R)
    claim:
        ? forall n {j Z:j>=1}:
            \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>(n)=\rs::real_tail_constant<1,1/2>(n)
        n $in N+
        n $in R
        n!=0
        n $in R*
        1/n $in R
        release thm power::positive_real_power_is_positive(1/2,n)
        readme_half_terms(n)=(1/2)^n>0
        abs(readme_half_terms(n))=(1/2)^n
        release thm rt::positive_start_real_tail_root_power(1,readme_half_terms,n)
        release thm power::nonnegative_real_root_unique(abs(readme_half_terms(n)),\rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>(n),n)
        release thm power::nonnegative_real_root_unique(abs(readme_half_terms(n)),1/2,n)
        \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>(n)=abs(readme_half_terms(n))^(1/n)=1/2
        \rs::real_tail_constant<1,1/2>(n)=1/2
        \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>(n)=\rs::real_tail_constant<1,1/2>(n)
    by fn_extension \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms> = \rs::real_tail_constant<1,1/2>

release thm rs::real_tail_constant_limit(1,1/2)

claim:
    ? $rs::has_real_tail_limit(1,\rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>,1/2)
    \rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms> = \rs::real_tail_constant<1,1/2>
    $rs::has_real_tail_limit(1,\rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>,1/2)

release thm limits::real_tail_limit_equals_extremal_limits(1,\rt::positive_start_real_tail_root_magnitudes<1,readme_half_terms>,1/2)

release thm limits::real_strict_order_is_extended_order(1/2,1)

release thm rt::positive_start_real_series_root_limsup_below_one_converges(1,readme_half_terms)

release thm rt::positive_index_nth_root_tail_tends_to_one

release obj def rt::positive_index_nth_root_tail

rt::positive_index_nth_root_tail(1)=1
```

See `math_collections.md` for domains, proof dependencies and source scope.
