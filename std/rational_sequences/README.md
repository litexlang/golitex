# Rational sequence arithmetic and native real values

This module formalizes Tao, *Analysis I*, sections 5.1-5.4, with arbitrary integer
starting indices. It imports real_approximation. Sequences are actual functions
on `{n in Z:n>=start}` with rational values. Source Cauchy quantification uses
positive rational radii and closed error bounds. Every boundedness conclusion
supplies a nonnegative rational bound. Section 5.3 reuses native R and its fixed
arithmetic; actual rational representatives are connected to native real limits.
It does not construct a second quotient model, isomorphism or LIM selector.

```ini
[import std]
Sequences = rational_sequences
[alias]
rseq = Sequences::main
[export]
main = "./main.lit"
```

## Constructions and predicates

Template applications have a leading backslash.

| Interface | Contract |
| --- | --- |
| `\integer_index_tail<start>` | The actual subset `{n Z:n>=start}`, for any integer start. |
| `\rational_constant_sequence<start,value>` | The complete constant rational sequence on that tail. |
| `\rational_real_reindex<start,a>(k)` | The actual real-valued sequence `a(start+k-1)` on `k in N+`; its values are still the original rationals. |
| `\rational_tenth_perturbation<center,coefficient>(n)` | The actual rational sequence `center+coefficient*10^(-n)` on n>=1. Both parameters are rational. |
| `rational_reciprocal_sequence` | The actual rational function `n -> 1/n` on the integer tail starting at one. It has no value at zero. |
| `is_rational_steady(start,a,epsilon)` | Every pair of values is epsilon-close, for positive real epsilon. |
| `is_rational_steady_after(start,a,epsilon,cutoff)` | `cutoff>=start`, and all pairs of legal indices at least the integer cutoff are epsilon-close. |
| `is_eventually_rational_steady(start,a,epsilon)` | Such a cutoff exists. |
| `is_rational_cauchy(start,a)` | Eventual steadiness for every positive rational epsilon. |
| `is_rational_sequence_bounded_by(start,a,M)` | Rational `M>=0` bounds every absolute value. |
| `is_bounded_rational_sequence(start,a)` | Some rational M satisfies that bound. |
| `is_finite_rational_sequence_bounded_by(n,a,M)` | Rational `M>=0` bounds every coordinate of `a in finite_seq(Q,n)`, including the empty sequence. |
| `are_rational_sequences_close(start,a,b,epsilon)` | The two values at every common index are epsilon-close. |
| `are_rational_sequences_close_after(start,a,b,epsilon,cutoff)` | `cutoff>=start` and the pair is epsilon-close at every index at least the cutoff. |
| `are_eventually_rational_sequences_close(start,a,b,epsilon)` | Such a cutoff exists. |
| `are_equivalent_rational_sequences(start,a,b)` | Eventual closeness for every positive rational radius. No Cauchy premise is imposed. |

| `\rational_sequence_sum<start,a,b>` / `\rational_sequence_product<start,a,b>` | Actual pointwise rational sum/product on the unchanged integer tail. |
| `\rational_sequence_negation<start,a>` | Actual pointwise rational negation. |
| `\rational_sequence_replace_prefix<start,a,cutoff,value>` | Value before cutoff, original a(n) thereafter; the domain remains the full original tail. |
| `\rational_floor_sequence<x>` | Actual rational floor(n*x)/n on n>=1, for every native real x. |
| `\rational_sequence_reciprocal<start,a>` | Actual 1/a(n); the input must be a complete function into Q*. No value for 1/0 is assigned. |
| `is_rational_sequence_away_from_zero_by(start,a,c)` | Positive rational c is a uniform lower bound for abs(a(n)) on the full tail. |
| `is_rational_sequence_bounded_away_from_zero(start,a)` | Such a positive rational c exists. |
| `is_rational_real_limit_tail(start,a,L,epsilon,cutoff)` | Cutoff>=start and abs(a(n)-L)<epsilon thereafter, with positive real epsilon. |
| `is_rational_sequence_positive_by(start,a,c)` | Positive rational c satisfies a(n)>=c on every original index. |
| `is_rational_sequence_negative_by(start,a,c)` | Positive rational c satisfies a(n)<=-c on every original index. |
| `is_rational_sequence_positively_bounded_away_from_zero(start,a)` | Some positive rational c is a full-tail lower bound. |
| `is_rational_sequence_negatively_bounded_away_from_zero(start,a)` | Some negative rational -c is a full-tail upper bound. |

All names above follow `rseq::` in a caller.

## Theorems

The three `integer_index_tail_*` theorems introduce membership, expose integer
membership, and recover the lower-bound condition for an integer index.
`integer_reindex_ge_cutoff` translates cutoff inequalities on arbitrary
integers. `rational_original_index_positive` gives the inverse index
`n-start+1 in N+`; `rational_real_reindex_at` gives the exact value equation.
Before spelling `a(start+k-1)` in a goal, publish membership of that transformed
index using `integer_index_tail_member` and the nonnegative increment `k-1`.

The six Cauchy and boundedness theorems are:

| Theorem | Contract |
| --- | --- |
| `rational_constant_sequence_is_cauchy(start,value)` | Every constant rational sequence is Cauchy, including negative starts. |
| `rational_constant_sequence_is_bounded(start,value)` | Its actual rational absolute value is a valid bound. |
| `rational_reciprocal_sequence_is_cauchy` | The sequence `1,1/2,1/3,...` is Cauchy. Omit argument parentheses. |
| `finite_rational_sequence_is_bounded(n,a)` | A nonnegative rational bound exists for every finite rational sequence, including length zero. |
| `rational_cauchy_is_native_cauchy(start,a)` | The actual real reindexing of a source Cauchy sequence satisfies native Cauchy control. |
| `rational_cauchy_sequence_is_bounded(start,a)` | Every source Cauchy sequence has a nonnegative rational bound. |

The additional `rational_sequence_equivalence_reflexive`,
`rational_sequence_equivalence_symmetric` and
`rational_sequence_equivalence_transitive` prove an equivalence relation on
all rational sequences with a common specified starting domain.
`integer_common_tail_cutoff(start,first,second)` supplies the joint cutoff
`first+second-start`; it remains valid for negative starts.

`positive_geometric_dominates_index(q,n)` proves `n<=q^n` for real `q>=2`
and positive natural `n`. `rational_tenth_perturbations_equivalent(center,left,right)`
proves equivalence of the two perturbations about the same rational center,
for arbitrary rational amplitudes, including zero. Center one and amplitudes
one and minus one give the source's `1+10^(-n)` and `1-10^(-n)`.

## Examples: negative starts and equivalent sequences

With the configuration above, this complete caller applies the general
Cauchy-to-bounded theorem at start minus three and checks the source pair:

```litex
release thm rseq::rational_constant_sequence_is_cauchy(-3,7/2)
release thm rseq::rational_cauchy_sequence_is_bounded(-3,\rseq::rational_constant_sequence<-3,7/2>)
$rseq::is_bounded_rational_sequence(-3,\rseq::rational_constant_sequence<-3,7/2>)
release thm rseq::rational_tenth_perturbations_equivalent(1,1,-1)
$rseq::are_equivalent_rational_sequences(1,\rseq::rational_tenth_perturbation<1,1>,\rseq::rational_tenth_perturbation<1,-1>)
```

For concrete evaluation of the imported named reciprocal function, use
`release obj def rseq::rational_reciprocal_sequence` and legal indices.
Boundedness alone does not imply Cauchy: the imported acceptance example
`(-1)^n` is bounded by one and its Cauchy assertion is rejected. Likewise,
equivalence does not imply that either sequence is Cauchy. These perturbations
are arithmetic sequences; the digit-expansion theorems of Appendix B remain
separate. Cauchy arithmetic and native-real correspondence are supplied below. No kernel changes, new assumptions, source trust or alternate real
number construction are introduced. Drafts and exact acceptance records remain
in the source-ordered experiment workspace.


## Representative arithmetic (section 5.3)

There are 68 named theorems in the complete module. `rational_cauchy_sequences_sum`
and `rational_cauchy_sequences_product` prove closure from the two source Cauchy
premises. Product bounds are derived from Cauchy; zero sequences need no separate
nonzero bound assumption. `rational_sequence_sums_equivalent` allows arbitrary
rational sequences. `rational_sequence_products_equivalent` assumes Cauchy for
the original two factors and equivalence of both replacements.
`rational_equivalent_sequence_is_cauchy` derives Cauchy for a replacement.
The corresponding negation laws preserve Cauchy and equivalence.

`rational_cauchy_sequence_has_unique_real_limit` and
`native_cauchy_is_rational_cauchy` connect the two Cauchy interfaces using the
actual reindexing. `rational_sequence_equivalence_from_common_real_limit`,
`rational_sequence_equivalence_preserves_real_limit` and
`equivalent_rational_sequences_have_same_real_limit` establish the native-value
meaning of source equivalence. The `*_real_limit` laws for constants, sums,
products and negation identify their actual real values. Native field algebra
is reused, with no duplicate public arithmetic operations.

Finite-prefix replacement preserves equivalence, Cauchy and the native real
value when cutoff>=start. `rational_floor_sequence_error` proves error<1/n;
its real-limit and Cauchy theorems hold for every real x, including negative x.
`nonzero_real_has_separated_rational_representation` constructs a full rational
Cauchy representative for every nonzero real, with a uniform positive rational
lower bound and native limit x. Its finite prefix is replaced because the first
floor approximants can be zero.

`rational_sequence_away_from_zero_has_nonzero_values` proves complete function
membership into Q*. After that membership is available, the reciprocal template
is defined. `rational_cauchy_sequence_reciprocal` requires source Cauchy and
uniform separation. `rational_sequence_reciprocals_equivalent` requires both
separations and equivalence, with no additional Cauchy premise.
`rational_sequence_reciprocal_real_limit` gives native value 1/L when L is
nonzero. Pointwise nonzero terms alone do not imply reciprocal Cauchy: 1/n has
reciprocal n. A nonzero limit alone also does not eliminate early zero terms.

This complete additional caller uses a negative starting index and a negative
constant. The uniform lower bound supplies the nonzero function contract before
the reciprocal is used:

```litex
claim:
    ? forall n Z:
        n $in \rseq::integer_index_tail<-3>
        =>:
            abs(\rseq::rational_constant_sequence<-3,-2>(n)) >= 2
    \rseq::rational_constant_sequence<-3,-2>(n) = -2
    abs(\rseq::rational_constant_sequence<-3,-2>(n)) = abs(-2) = 2
by def $rseq::is_rational_sequence_away_from_zero_by(-3,\rseq::rational_constant_sequence<-3,-2>,2)
witness $rseq::is_rational_sequence_bounded_away_from_zero(-3,\rseq::rational_constant_sequence<-3,-2>) from 2
release thm rseq::rational_sequence_away_from_zero_has_nonzero_values(-3,\rseq::rational_constant_sequence<-3,-2>)
release thm rseq::rational_constant_sequence_is_cauchy(-3,-2)
release thm rseq::rational_cauchy_sequence_reciprocal(-3,\rseq::rational_constant_sequence<-3,-2>)
release thm rseq::rational_constant_sequence_real_limit(-3,-2)
release thm rseq::rational_sequence_reciprocal_real_limit(-3,\rseq::rational_constant_sequence<-3,-2>,-2)
```


## Signed representatives and order (section 5.4)

The signed bound predicates use a positive magnitude parameter c in both cases.
The positive/negative bound theorems imply absolute separation by the same c;
the existential versions imply uniform separation. A positive sequence cannot
also be negatively bounded away from zero. Negation of a positive separated
sequence is negatively separated.

`rational_sequence_real_limits_preserve_order(start,a,b,L,M)` transfers
pointwise a(n)<=b(n) to L<=M for their native real limits. No extra Cauchy
premise is needed once those limits are known.
`nonnegative_rational_sequence_has_nonnegative_real_limit` is the zero-bound
case. Strict pointwise order cannot replace the weak conclusion.

The `rational_sequence_positive_bound_passes_to_real_limit` and negative-bound
counterpart preserve the actual rational bound. Consequently
`positive_rational_sequence_has_positive_real_limit` and its negative
counterpart identify native signs. Conversely,
`positive_real_has_positive_rational_representation` constructs a full positive
separated rational Cauchy representative for every native x>0;
`negative_real_has_negative_rational_representation` does the same for x<0.
Both have actual native real limit x. They reuse floor approximants, finite-prefix
replacement and negation. No second definition of real order or absolute value
is added.

With the same configuration, this complete caller checks a positive bound at a
negative starting index and then applies both signed representative constructions:

```litex
claim:
    ? forall n Z:
        n $in \rseq::integer_index_tail<-4>
        =>:
            \rseq::rational_constant_sequence<-4,3>(n) >= 2
    \rseq::rational_constant_sequence<-4,3>(n) = 3 >= 2
by def $rseq::is_rational_sequence_positive_by(-4,\rseq::rational_constant_sequence<-4,3>,2)
witness $rseq::is_rational_sequence_positively_bounded_away_from_zero(-4,\rseq::rational_constant_sequence<-4,3>) from 2
release thm rseq::rational_constant_sequence_real_limit(-4,3)
release thm rseq::positive_rational_sequence_has_positive_real_limit(-4,\rseq::rational_constant_sequence<-4,3>,3)
release thm rseq::positive_rational_sequence_negation_is_negative(-4,\rseq::rational_constant_sequence<-4,3>)
sqrt(2) > 0
sqrt(2) $in R+
release thm rseq::positive_real_has_positive_rational_representation(sqrt(2))
-sqrt(2) < 0
release thm rseq::negative_real_has_negative_rational_representation(-sqrt(2))
```
