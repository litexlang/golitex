# Nonnegative real series, condensation and reciprocal powers

This module covers Tao Analysis I section7.3 on actual complete integer
tails. Nonnegative series converge exactly when their actual partial sums
have a finite real upper bound. Absolute comparison gives both convergence
and the complete bound abs(sum(a))<=sum(abs(a))<=sum(b).

| Interface after nn:: | Hypotheses and conclusion |
| --- | --- |
| nonnegative_real_tail_series_has_increasing_partial_sums | Every original term is nonnegative; the actual partial-sum tail is increasing. |
| upper_bounded_nonnegative_real_tail_series_converges | Nonnegative original data and any real upper bound M for all actual partial sums give series convergence. M=0 is included. |
| convergent_real_tail_series_has_upper_bounded_partial_sums | Every convergent real series has a real upper bound for its actual partial sums; this direction needs no sign condition. |
| real_tail_series_absolute_comparison | abs(a(n))<=b(n) on the complete original tail and convergence of b give absolute and ordinary convergence of a. |
| real_tail_series_absolute_comparison_sum_bounds | Candidate sums L for a, A for its absolute values and B for b, under the same pointwise comparison, give abs(L)<=A<=B. |
| nonabsolute_real_tail_series_has_divergent_majorants | The pointwise comparison and failure of absolute convergence of a imply that b is not convergent. |

The start is any integer. All data are actual complete functions
{j Z:j>=start}->R. Partial sums, convergence, guarded sums and actual absolute
values retain their established real_tail_series and real_sequence_limsup
interfaces. The upper-bound relation is the existing
sext::is_real_tail_upper_bound(start,actual_partial_sums,M).
No new scalar sum or bound selector is introduced.

The example checks a zero upper bound at negative start -3, a genuinely signed
series dominated by a nonnegative convergent majorant at start -2, the scalar
bound1<=3<=4, and the comparison contrapositive with a harmonic lower series:

```ini
[import std]
Nonnegative = real_nonnegative_series
TailSeries = real_tail_series
Real = real_sequences
Extrema = real_sequence_extrema
Limits = real_sequence_limsup
Series = real_series
Approximation = real_approximation
[alias]
nn = Nonnegative::main
ts = TailSeries::main
rs = Real::main
sext = Extrema::main
limits = Limits::main
series = Series::main
approx = Approximation::main
[export]
main = "./main.lit"
```

```litex
have fn signed_geometric(n {j Z:j>=-2}) R=(-1/2)^(n+3)

claim:
    ? forall k N+:
        \rs::real_tail_reindex<-2,signed_geometric>(k)=(-1/2)^k
    release thm rs::real_tail_positive_index(-2,k)
    release thm rs::real_tail_reindex_at(-2,signed_geometric,k)
    (-2+k-1)+3=k
    \rs::real_tail_reindex<-2,signed_geometric>(k)=signed_geometric(-2+k-1)=(-1/2)^((-2+k-1)+3)=(-1/2)^k

release thm series::series_sum_geometric(\rs::real_tail_reindex<-2,signed_geometric>,-1/2)

claim:
    ? $series::has_series_sum(\rs::real_tail_reindex<-2,signed_geometric>,-1/3)
    (-1/2)/(1-(-1/2))=-1/3
    $series::has_series_sum(\rs::real_tail_reindex<-2,signed_geometric>,(-1/2)/(1-(-1/2)))

release thm ts::native_series_sum_is_real_tail_series_sum(-2,signed_geometric,-1/3)

have fn positive_geometric(n {j Z:j>=-2}) R=(1/2)^(n+3)

claim:
    ? forall k N+:
        \rs::real_tail_reindex<-2,positive_geometric>(k)=(1/2)^k
    release thm rs::real_tail_positive_index(-2,k)
    release thm rs::real_tail_reindex_at(-2,positive_geometric,k)
    (-2+k-1)+3=k
    \rs::real_tail_reindex<-2,positive_geometric>(k)=positive_geometric(-2+k-1)=(1/2)^((-2+k-1)+3)=(1/2)^k

release thm series::series_sum_geometric(\rs::real_tail_reindex<-2,positive_geometric>,1/2)

claim:
    ? $series::has_series_sum(\rs::real_tail_reindex<-2,positive_geometric>,1)
    (1/2)/(1-1/2)=1
    $series::has_series_sum(\rs::real_tail_reindex<-2,positive_geometric>,(1/2)/(1-1/2))

have fn zero_terms(n {j Z:j>=-3}) R=0

claim:
    ? forall last Z:
        closed_range(-3,last) $subset {j Z:j>=-3}
    claim:
        ? forall n closed_range(-3,last):
            n $in {j Z:j>=-3}
        n $in Z
        n>=-3
        n $in {j Z:j>=-3}
    by def closed_range(-3,last) $subset {j Z:j>=-3}

claim:
    ? forall n {j Z:j>=-3}:
        zero_terms(n)>=0
    zero_terms(n)=0

claim:
    ? $sext::is_real_tail_upper_bound(-3,\ts::real_tail_partial_sums<-3,zero_terms>,0)
    claim:
        ? forall n {j Z:j>=-3}:
            \ts::real_tail_partial_sums<-3,zero_terms>(n)<=0
        n $in Z
        n $in R
        n>=-3
        n-(-3)+1 $in R
        (n-(-3)+1)*0=0
        sum(-3,n,zero_terms)=(n-(-3)+1)*0=0
        \ts::real_tail_partial_sums<-3,zero_terms>(n)=sum(-3,n,zero_terms)=0
        \ts::real_tail_partial_sums<-3,zero_terms>(n)<=0
    by def $sext::is_real_tail_upper_bound(-3,\ts::real_tail_partial_sums<-3,zero_terms>,0)

release thm nn::upper_bounded_nonnegative_real_tail_series_converges(-3,zero_terms,0)

release thm nn::convergent_real_tail_series_has_upper_bounded_partial_sums(-3,zero_terms)

release thm nn::nonnegative_real_tail_series_has_increasing_partial_sums(-3,zero_terms)

release thm ts::native_series_sum_is_real_tail_series_sum(-2,positive_geometric,1)

release thm ts::real_tail_series_sum_scale(-2,positive_geometric,1,4)

release thm ts::real_tail_series_sum_implies_convergent(-2,\rs::real_tail_scaled<-2,positive_geometric,4>,4)

claim:
    ? forall n {j Z:j>=-2}:
        abs(signed_geometric(n))=positive_geometric(n)
        positive_geometric(n)>=0
    n $in Z
    n>=-2
    n+3 $in Z
    n+3>=(-2)+3=1
    n+3 $in N+
    n+3 $in R
    signed_geometric(n)=(-1/2)^(n+3)
    positive_geometric(n)=(1/2)^(n+3)
    release thm approx::absolute_value_integer_power(-1/2,n+3)
    abs(-1/2)=1/2
    abs(signed_geometric(n))=abs((-1/2)^(n+3))=abs(-1/2)^(n+3)=(1/2)^(n+3)=positive_geometric(n)
    (1/2)^(n+3)>0
    positive_geometric(n)>=0

claim:
    ? forall n {j Z:j>=-2}:
        abs(\rs::real_tail_scaled<-2,signed_geometric,3>(n))<=\rs::real_tail_scaled<-2,positive_geometric,4>(n)
    signed_geometric(n) $in R
    positive_geometric(n) $in R
    positive_geometric(n)>=0
    abs(signed_geometric(n))=positive_geometric(n)
    \rs::real_tail_scaled<-2,signed_geometric,3>(n)=3*signed_geometric(n)
    abs(\rs::real_tail_scaled<-2,signed_geometric,3>(n))=abs(3*signed_geometric(n))=abs(3)*abs(signed_geometric(n))=3*positive_geometric(n)<=4*positive_geometric(n)=\rs::real_tail_scaled<-2,positive_geometric,4>(n)

release thm nn::real_tail_series_absolute_comparison(-2,\rs::real_tail_scaled<-2,signed_geometric,3>,\rs::real_tail_scaled<-2,positive_geometric,4>)

release thm ts::real_tail_series_sum_scale(-2,signed_geometric,-1/3,3)

release thm ts::real_tail_series_sum_scale(-2,positive_geometric,1,3)

claim:
    ? \limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>> = \rs::real_tail_scaled<-2,positive_geometric,3>
    claim:
        ? forall n {j Z:j>=-2}:
            \limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>>(n)=\rs::real_tail_scaled<-2,positive_geometric,3>(n)
        abs(signed_geometric(n))=positive_geometric(n)
        \rs::real_tail_scaled<-2,signed_geometric,3>(n)=3*signed_geometric(n)
        abs(\rs::real_tail_scaled<-2,signed_geometric,3>(n))=abs(3*signed_geometric(n))=abs(3)*abs(signed_geometric(n))=3*positive_geometric(n)
        \limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>>(n)=abs(\rs::real_tail_scaled<-2,signed_geometric,3>(n))=3*positive_geometric(n)=\rs::real_tail_scaled<-2,positive_geometric,3>(n)
    by fn_extension \limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>> = \rs::real_tail_scaled<-2,positive_geometric,3>

claim:
    ? $ts::has_real_tail_series_sum(-2,\rs::real_tail_scaled<-2,signed_geometric,3>,-1) and $ts::has_real_tail_series_sum(-2,\limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>>,3)
    3*(-1/3)=-1
    3*1=3
    $ts::has_real_tail_series_sum(-2,\rs::real_tail_scaled<-2,signed_geometric,3>,-1)
    $ts::has_real_tail_series_sum(-2,\rs::real_tail_scaled<-2,positive_geometric,3>,3)
    $ts::has_real_tail_series_sum(-2,\limits::real_tail_absolute_values<-2,\rs::real_tail_scaled<-2,signed_geometric,3>>,3)

release thm nn::real_tail_series_absolute_comparison_sum_bounds(-2,\rs::real_tail_scaled<-2,signed_geometric,3>,\rs::real_tail_scaled<-2,positive_geometric,4>,-1,3,4)

release thm nn::convergent_real_tail_series_has_upper_bounded_partial_sums(-2,\rs::real_tail_scaled<-2,signed_geometric,3>)

release obj def rs::positive_real_reciprocal_tail

claim:
    ? forall k N+:
        \rs::real_tail_reindex<1,rs::positive_real_reciprocal_tail>(k)=1/k
    release thm rs::real_tail_positive_index(1,k)
    k $in Z
    k>=1
    k $in {j Z:j>=1}
    1+k-1=k
    rs::positive_real_reciprocal_tail(k)=1/k
    release thm rs::real_tail_reindex_at(1,rs::positive_real_reciprocal_tail,k)
    \rs::real_tail_reindex<1,rs::positive_real_reciprocal_tail>(k)=rs::positive_real_reciprocal_tail(1+k-1)=rs::positive_real_reciprocal_tail(k)=1/k

release thm series::harmonic_series_diverges(\rs::real_tail_reindex<1,rs::positive_real_reciprocal_tail>)

claim:
    ? not $ts::is_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
    by contra:
        ? not $ts::is_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
        release thm ts::convergent_real_tail_series_is_native_convergent(1,rs::positive_real_reciprocal_tail)
        impossible $series::is_convergent_series(\rs::real_tail_reindex<1,rs::positive_real_reciprocal_tail>)

claim:
    ? not $ts::is_absolutely_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
    by contra:
        ? not $ts::is_absolutely_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
        release thm ts::absolutely_convergent_real_tail_series_converges(1,rs::positive_real_reciprocal_tail)
        impossible $ts::is_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)

claim:
    ? forall n {j Z:j>=1}:
        abs(rs::positive_real_reciprocal_tail(n))<=\rs::real_tail_constant<1,1>(n)
    n $in Z
    n>=1>0
    rs::positive_real_reciprocal_tail(n)=1/n>0
    abs(rs::positive_real_reciprocal_tail(n))=1/n<=n/n=1=\rs::real_tail_constant<1,1>(n)

release thm nn::nonabsolute_real_tail_series_has_divergent_majorants(1,rs::positive_real_reciprocal_tail,\rs::real_tail_constant<1,1>)
```

A separate complete-domain consumer verifies the existential form of the
boundedness criterion and the selected-sum comparison chain directly from
the original hypotheses. Convergence guards are proved before selected sums
are used. Explicit original interval/index memberships and real scalar
carriers supply formation evidence.

Proof basis: the existing actual finite-block identity gives adjacent
partial-sum increase; established increasing upper-bounded real-tail
convergence gives the criterion. The reverse uses ordinary convergence
boundedness. Exact native reindexing and existing absolute-series comparison
give absolute convergence. Finite partial-sum comparison and native limit
order give the scalar chain; ordinary contradiction gives the contrapositive.


The actual construction `\nn::real_geometric_tail_from_zero<base>` has the
complete domain `{j Z:j>=0}` and value `base^n` for every real base. It includes
base0 and uses the established `0^0=1` convention at index0. Its name has one
fixed start0 contract; existing native start1 geometric data are unchanged.

| Further interface after nn:: | Hypotheses and conclusion |
| --- | --- |
| zero_start_real_geometric_first_term | Every real base has first term1, including base0. |
| zero_start_real_geometric_tail_native_values | The actual restriction to start1 reindexes to base^k on N+. |
| zero_start_real_geometric_series_sum | abs(base)<1 gives the original start0 series candidate1/(1-base). |
| zero_start_real_geometric_absolute_data | Actual absolute values equal the start0 geometric data at abs(base), including index0. |
| zero_start_real_geometric_series_absolutely_converges | abs(base)<1 gives absolute and ordinary convergence. |
| zero_start_real_geometric_series_diverges | abs(base)>=1 gives divergence, including bases1 and-1. |

The same import configuration above checks the zero and signed cases, actual
selected sums and both boundary signs:

```litex
release thm nn::zero_start_real_geometric_series_sum(0)

release thm nn::zero_start_real_geometric_series_absolutely_converges(0)

claim:
    ? $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<0>,1)
    1/(1-(0))=1
    $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<0>,1/(1-(0)))

release thm ts::real_tail_series_sum_value(0,\nn::real_geometric_tail_from_zero<0>,1)

\ts::real_tail_series_sum<0>(\nn::real_geometric_tail_from_zero<0>)=1

release thm nn::zero_start_real_geometric_series_sum(-1/2)

release thm nn::zero_start_real_geometric_series_absolutely_converges(-1/2)

claim:
    ? $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<-1/2>,2/3)
    1/(1-(-1/2))=2/3
    $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<-1/2>,1/(1-(-1/2)))

release thm ts::real_tail_series_sum_value(0,\nn::real_geometric_tail_from_zero<-1/2>,2/3)

\ts::real_tail_series_sum<0>(\nn::real_geometric_tail_from_zero<-1/2>)=2/3

claim:
    ? \nn::real_geometric_tail_from_zero<0>(0)=1 and \nn::real_geometric_tail_from_zero<0>(1)=0
    \nn::real_geometric_tail_from_zero<0>(0)=0^0=1
    \nn::real_geometric_tail_from_zero<0>(1)=0^1=0

release thm nn::zero_start_real_geometric_absolute_data(-1/2)

release thm nn::zero_start_real_geometric_series_diverges(1)

not $ts::is_convergent_real_tail_series(0,\nn::real_geometric_tail_from_zero<1>)

release thm nn::zero_start_real_geometric_series_diverges(-1)

not $ts::is_convergent_real_tail_series(0,\nn::real_geometric_tail_from_zero<-1>)
```

Generic quotient goals first require the explicit nonzero denominator fact.
The independent complete-domain caller supplies this existing-source proof:

```litex
claim:
    ? forall base R:
        abs(base)<1
        =>:
            1-base!=0
    release thm series::unit_abs_upper_bound(base)
```


## Actual dyadic condensation

For actual data a:{j Z:j>=1}->R, `\nn::dyadic_real_tail_condensation<a>`
is exactly k->2^k*a(2^k) on the complete domain k>=0. When all original
terms are nonnegative and a(n+1)<=a(n), original and condensed convergence
are equivalent. This is Tao7.3.4, distinct from the finite-tail Cauchy criterion.
These interfaces relate convergence; scalar sums are determined separately
for the original and condensed data. The proof auxiliary7.3.6 is retained explicitly for every K in N, including0:
S(2^(K+1)-1)<=T(K)<=2*S(2^K), using actual original partial sums.

| Further interface after nn:: | Contract |
| --- | --- |
| dyadic_condensation_preserves_nonnegative_terms | Each actual condensed term is nonnegative when all original terms are nonnegative. |
| dyadic_indices_dominate_natural_indices | 2^K>=K+1 and2^(K+1)-1>=K+1, including K0. |
| real_tail_series_initial_partial_sum | The actual partial sum at an arbitrary integer start is its first original term. |
| real_tail_series_partial_sum_successor | The actual next partial sum adds the actual next term on any integer tail. |
| real_difference_upper_bound_gives_additive_bound | For real x,y,z, x-y<=z gives x<=y+z. |
| real_difference_lower_bound_gives_additive_bound | For real x,y,z, z<=x-y gives y+z<=x. |
| dyadic_condensation_partial_sum_lower_bound | Decreasing original data gives S(2^(K+1)-1)<=T(K); this direction does not require nonnegative terms. |
| dyadic_condensation_partial_sum_upper_bound | Nonnegative decreasing original data gives T(K)<=2*S(2^K). |
| dyadic_condensation_partial_sum_bounds | The complete two-sided source estimate. |
| convergent_nonnegative_decreasing_series_has_convergent_condensation | Convergence of the original nonnegative decreasing data gives condensed convergence. |
| convergent_condensation_gives_nonnegative_decreasing_series_convergence | Condensed convergence gives convergence of the same original nonnegative decreasing data. |

The next example condenses an actual reciprocal-square function to the
half-geometric function and the actual harmonic function to the unit-geometric
function. It proves reciprocal-square convergence and harmonic divergence
through the new directions, and checks the original K0 bounds.

```litex
claim:
    ? forall start Z,n {j Z:j>=start}:
        n+1 $in {j Z:j>=start}
    n $in Z
    n>=start
    n+1 $in Z
    n+1>=n>=start
    n+1 $in {j Z:j>=start}

claim:
    ? forall start,first,last Z:
        first>=start
        =>:
            closed_range(first,last) $subset {j Z:j>=start}
    claim:
        ? forall n closed_range(first,last):
            n $in {j Z:j>=start}
        n $in Z
        n>=first>=start
        n $in {j Z:j>=start}
    by def closed_range(first,last) $subset {j Z:j>=start}

claim:
    ? forall n {j Z:j>=0}:
        n $in N
    n $in Z
    n>=0
    n $in N

claim:
    ? forall k N:
        2^k $in N+
        2^k $in {j Z:j>=1}
        2^k>=1
    2^k $in Z
    2^k>0
    2^k $in N+
    2^k>=1
    2^k $in {j Z:j>=1}

claim:
    ? forall k {j Z:j>=0}:
        2^k $in {j Z:j>=1}
        2^k $in N+
        2^k>=1
    k $in N
    2^k $in N+
    2^k>=1
    2^k $in Z
    2^k $in {j Z:j>=1}

claim:
    ? forall k N:
        k $in {j Z:j>=0}
        k+1 $in {j Z:j>=0}
        2^(k+1)-1 $in {j Z:j>=1}
        2^(k+2)-1 $in {j Z:j>=1}
        2^k+1 $in {j Z:j>=1}
    k $in Z
    k>=0
    k $in {j Z:j>=0}
    k+1>=0
    k+1 $in {j Z:j>=0}
    release thm nn::dyadic_indices_dominate_natural_indices(k)
    2^(k+1)-1>=k+1>=1
    release thm nn::dyadic_indices_dominate_natural_indices(k+1)
    k+2=(k+1)+1
    2^(k+2)-1=2^((k+1)+1)-1>=(k+1)+1>=1
    2^k>=1
    2^k+1>=1
    2^(k+1)-1 $in Z
    2^(k+2)-1 $in Z
    2^k+1 $in Z
    2^(k+1)-1 $in {j Z:j>=1}
    2^(k+2)-1 $in {j Z:j>=1}
    2^k+1 $in {j Z:j>=1}

claim:
    ? forall n {j Z:j>=1}:
        n^2!=0
    n $in Z
    n>=1>0
    n $in R
    n^2>0
    n^2!=0

have fn reciprocal_square_terms(n {j Z:j>=1}) R=1/n^2

claim:
    ? forall n {j Z:j>=1}:
        reciprocal_square_terms(n)>=0
    n $in Z
    n>=1>0
    n $in R
    n^2>0
    reciprocal_square_terms(n)=1/n^2>0

claim:
    ? $sext::is_decreasing_real_tail(1,reciprocal_square_terms)
    claim:
        ? forall n {j Z:j>=1}:
            reciprocal_square_terms(n+1)<=reciprocal_square_terms(n)
        n $in Z
        n>=1>0
        n+1 $in {j Z:j>=1}
        n $in R
        n+1 $in R
        n^2>0
        (n+1)^2>0
        n^2<=(n+1)^2
        1/(n+1)^2<=1/n^2
        reciprocal_square_terms(n+1)=1/(n+1)^2<=1/n^2=reciprocal_square_terms(n)
    by def $sext::is_decreasing_real_tail(1,reciprocal_square_terms)

claim:
    ? \nn::dyadic_real_tail_condensation<reciprocal_square_terms> = \nn::real_geometric_tail_from_zero<1/2>
    release thm fn_set_member(\nn::dyadic_real_tail_condensation<reciprocal_square_terms>,fn(k {j Z:j>=0}) R)
    release thm fn_set_member(\nn::real_geometric_tail_from_zero<1/2>,fn(k {j Z:j>=0}) R)
    claim:
        ? forall k {j Z:j>=0}:
            \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(k)=\nn::real_geometric_tail_from_zero<1/2>(k)
        k $in N
        2^k $in {j Z:j>=1}
        2^k $in R
        2^k>0
        (2^k)^2>0
        reciprocal_square_terms(2^k)=1/(2^k)^2
        \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(k)=2^k*reciprocal_square_terms(2^k)=2^k*(1/(2^k)^2)=1/(2^k)
        2^(-1)=1/2
        (1/2)^k=(2^(-1))^k=2^((-1)*k)
        (-1)*k=-k
        2^((-1)*k)=2^(-k)=1/(2^k)
        (1/2)^k=1/(2^k)
        \nn::real_geometric_tail_from_zero<1/2>(k)=(1/2)^k=1/(2^k)
        \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(k)=\nn::real_geometric_tail_from_zero<1/2>(k)
    by fn_extension \nn::dyadic_real_tail_condensation<reciprocal_square_terms> = \nn::real_geometric_tail_from_zero<1/2>

release thm nn::zero_start_real_geometric_series_absolutely_converges(1/2)

$ts::is_convergent_real_tail_series(0,\nn::dyadic_real_tail_condensation<reciprocal_square_terms>)

release thm nn::convergent_condensation_gives_nonnegative_decreasing_series_convergence(reciprocal_square_terms)

$ts::is_convergent_real_tail_series(1,reciprocal_square_terms)

release thm nn::convergent_nonnegative_decreasing_series_has_convergent_condensation(reciprocal_square_terms)

release thm nn::dyadic_condensation_partial_sum_bounds(reciprocal_square_terms,0)

release thm nn::dyadic_condensation_partial_sum_bounds(reciprocal_square_terms,3)

claim:
    ? \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(0)=1 and \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(1)=1/2 and \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(2)=1/4
    reciprocal_square_terms(1)=1/1^2=1
    reciprocal_square_terms(2)=1/2^2=1/4
    reciprocal_square_terms(4)=1/4^2=1/16
    \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(0)=2^0*reciprocal_square_terms(2^0)=1
    \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(1)=2^1*reciprocal_square_terms(2^1)=2*(1/4)=1/2
    \nn::dyadic_real_tail_condensation<reciprocal_square_terms>(2)=2^2*reciprocal_square_terms(2^2)=4*(1/16)=1/4

release obj def rs::positive_real_reciprocal_tail

claim:
    ? forall n {j Z:j>=1}:
        rs::positive_real_reciprocal_tail(n)>=0
    n $in Z
    n>=1>0
    rs::positive_real_reciprocal_tail(n)=1/n>0

claim:
    ? $sext::is_decreasing_real_tail(1,rs::positive_real_reciprocal_tail)
    claim:
        ? forall n {j Z:j>=1}:
            rs::positive_real_reciprocal_tail(n+1)<=rs::positive_real_reciprocal_tail(n)
        n $in Z
        n>=1>0
        n+1 $in {j Z:j>=1}
        1/(n+1)<=1/n
        rs::positive_real_reciprocal_tail(n+1)=1/(n+1)<=1/n=rs::positive_real_reciprocal_tail(n)
    by def $sext::is_decreasing_real_tail(1,rs::positive_real_reciprocal_tail)

claim:
    ? \nn::dyadic_real_tail_condensation<rs::positive_real_reciprocal_tail> = \nn::real_geometric_tail_from_zero<1>
    release thm fn_set_member(\nn::dyadic_real_tail_condensation<rs::positive_real_reciprocal_tail>,fn(k {j Z:j>=0}) R)
    release thm fn_set_member(\nn::real_geometric_tail_from_zero<1>,fn(k {j Z:j>=0}) R)
    claim:
        ? forall k {j Z:j>=0}:
            \nn::dyadic_real_tail_condensation<rs::positive_real_reciprocal_tail>(k)=\nn::real_geometric_tail_from_zero<1>(k)
        k $in N
        2^k $in {j Z:j>=1}
        2^k>0
        rs::positive_real_reciprocal_tail(2^k)=1/(2^k)
        \nn::dyadic_real_tail_condensation<rs::positive_real_reciprocal_tail>(k)=2^k*(1/(2^k))=1=1^k=\nn::real_geometric_tail_from_zero<1>(k)
    by fn_extension \nn::dyadic_real_tail_condensation<rs::positive_real_reciprocal_tail> = \nn::real_geometric_tail_from_zero<1>

release thm nn::zero_start_real_geometric_series_diverges(1)

claim:
    ? not $ts::is_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
    by contra:
        ? not $ts::is_convergent_real_tail_series(1,rs::positive_real_reciprocal_tail)
        release thm nn::convergent_nonnegative_decreasing_series_has_convergent_condensation(rs::positive_real_reciprocal_tail)
        $ts::is_convergent_real_tail_series(0,\nn::real_geometric_tail_from_zero<1>)
        impossible $ts::is_convergent_real_tail_series(0,\nn::real_geometric_tail_from_zero<1>)

release thm nn::dyadic_condensation_partial_sum_bounds(rs::positive_real_reciprocal_tail,0)

release thm nn::dyadic_condensation_partial_sum_bounds(rs::positive_real_reciprocal_tail,1)
```

## Positive real-exponent reciprocal powers

The actual construction `\nn::positive_real_reciprocal_power_tail<q>` has
exact complete domain n>=1 and accepts every real q. It uses the existing
negative real power n^(-q). The value theorem proves its exact equality to
1/n^q at every original index, so no undefined value at0 or extension of an
input function is introduced. All terms are positive. The source decreasing
condition and series classification use q>0.

The author correction to Tao7.3.7 permits positive real exponents, using the
real-power laws of6.7.3; the result here has that complete real scope. See the
[author corrections](https://teorth.github.io/tao-web/analysis-i.html).
The exact actual condensed function is geometric at base2^(1-q). Thus q>1
gives convergence;0<q<=1 gives divergence. No classification theorem for
q<=0 is claimed here, although the constructor and value theorem remain valid.

| Further interface after nn:: | Contract |
| --- | --- |
| positive_real_reciprocal_power_value | Actual term equals1/n^q for every q in R and n>=1. |
| positive_real_reciprocal_power_terms_are_positive | Every actual term is positive for every real q. |
| positive_exponent_reciprocal_power_tail_is_decreasing | q>0 gives adjacent decrease on the complete original domain. |
| reciprocal_power_condensation_is_geometric | Equality of complete actual functions: condensation is geometric at2^(1-q), for every real q. |
| reciprocal_power_condensation_base_is_positive | The condensed base is positive and equals its absolute value. |
| reciprocal_power_condensation_base_is_inside_unit_interval | q>1 makes the absolute base less than1. |
| reciprocal_power_condensation_base_is_at_least_one | q<=1 makes the absolute base at least1. |
| real_reciprocal_power_series_converges_above_one | Every real q>1 gives series convergence. |
| positive_real_reciprocal_power_series_diverges_at_most_one | Every positive real q<=1 gives series divergence. |

The same import configuration checks the complete positive-exponent
biconditional, rational examples, the irrational exponents1+sqrt(2) and its
reciprocal on opposite sides of1, actual values and exact condensed data.
Values at q0 and q-1 exercise only the broader constructor/value contract.

```litex
claim:
    ? forall exponent R+:
        $ts::is_convergent_real_tail_series(1,\nn::positive_real_reciprocal_power_tail<exponent>)
        =>:
            exponent>1
    by contra:
        ? exponent>1
        exponent<=1
        release thm nn::positive_real_reciprocal_power_series_diverges_at_most_one(exponent)
        impossible $ts::is_convergent_real_tail_series(1,\nn::positive_real_reciprocal_power_tail<exponent>)

claim:
    ? forall exponent R+:
        exponent>1
        =>:
            $ts::is_convergent_real_tail_series(1,\nn::positive_real_reciprocal_power_tail<exponent>)
    release thm nn::real_reciprocal_power_series_converges_above_one(exponent)

forall exponent R+:
    =>:
        $ts::is_convergent_real_tail_series(1,\nn::positive_real_reciprocal_power_tail<exponent>)
    <=>:
        exponent>1

release thm nn::real_reciprocal_power_series_converges_above_one(2)

release thm nn::positive_exponent_reciprocal_power_tail_is_decreasing(2)

release thm nn::real_reciprocal_power_series_converges_above_one(3/2)

release thm nn::positive_exponent_reciprocal_power_tail_is_decreasing(3/2)

release thm nn::positive_real_reciprocal_power_series_diverges_at_most_one(1)

release thm nn::positive_real_reciprocal_power_series_diverges_at_most_one(1/2)

claim:
    ? 1+sqrt(2)>1 and 1/(1+sqrt(2))>0 and 1/(1+sqrt(2))<1
    sqrt(2) $in R
    sqrt(2)>0
    1+sqrt(2)>1>0
    1/(1+sqrt(2))>0
    1/(1+sqrt(2))<1

release thm nn::real_reciprocal_power_series_converges_above_one(1+sqrt(2))

release thm nn::positive_real_reciprocal_power_series_diverges_at_most_one(1/(1+sqrt(2)))

release thm nn::positive_real_reciprocal_power_value(2,3)

\nn::positive_real_reciprocal_power_tail<2>(3)=1/9

release thm nn::reciprocal_power_condensation_is_geometric(3/2)

release thm nn::positive_real_reciprocal_power_value(-1,2)

\nn::positive_real_reciprocal_power_tail<-1>(2)=2

release thm nn::positive_real_reciprocal_power_value(0,4)

\nn::positive_real_reciprocal_power_tail<0>(4)=1
```

The source has52 statements:32 named theorems,14 formation claims,3 actual
function templates and3 existing-definition releases. All domains and scalar
memberships are proved before their uses. The condensation estimates use
actual finite blocks, existing decreasing/increasing pairwise order and
partial-sum differences. Arbitrary real upper bounds are used in both
convergence directions, without requiring a positive bound.

Strict saved-file gates passed for source52, full imported196, README98 and
fresh no-wrapper applications146. The new condensation and p-series
boundaries have11 controls each; the geometric13 and earlier comparison15
retain their earlier checked receipts. All journals, planning, failed attempts,
source/executable epochs and exact acceptance records remain in experiments/.
No new axiom, trust, native change, build or complete-domain extension is used.
General expression verification and evidence composition/reuse remain shared
verify responsibilities. Later series sections are outside this module.
