# Real series on integer tails

This module covers Tao Analysis I section 7.2, including 7.2.1, 7.2.2, 7.2.5,
7.2.6, 7.2.8, 7.2.9, 7.2.12, 7.2.14 and 7.2.15. Series have any integer
start and actual complete real data on that original tail. It supplies the
full Cauchy criterion, zero and absolute convergence tests, the absolute sum
bound, both alternating directions, series laws and general telescoping.

| Data and relation after ts:: | Mathematical contract |
| --- | --- |
| \real_tail_partial_sums<start,a> | Actual function n -> sum(start,n,a), on n>=start. |
| $has_real_tail_series_sum(start,a,L) | The actual partial sums have source real-tail limit L. |
| $is_convergent_real_tail_series(start,a) | A finite real series-sum candidate exists. |
| \real_tail_series_sum<start>(a) | Selected finite sum, guarded by convergence. |
| $real_tail_series_tails_small_after(start,a,epsilon,cutoff) | Every p,q>=cutoff in the original tail has absolute finite block sum <=epsilon, with epsilon>0 and cutoff>=start. |
| $has_cauchy_real_tail_series_tails(start,a) | Such a cutoff exists for every positive real epsilon. |
| $is_absolutely_convergent_real_tail_series(start,a) | Series convergence of the existing original-domain absolute-value data. |
| \real_tail_alternating_terms<start,a> | Actual (-1)^n*a(n), on the same complete original tail. |
| \real_tail_series_translate<start,a,shift> | Actual a(n-shift), on n>=start+shift, for any integer shift. |
| \real_tail_forward_difference<start,a> | Actual a(n)-a(n+1), on n>=start. |

| Result after ts:: | Role |
| --- | --- |
| real_tail_series_sum_unique, real_tail_series_sum_implies_convergent, real_tail_series_sum_value, real_tail_series_sum_selected | Candidate uniqueness, existence and selected-value laws. |
| convergent_real_tail_series_has_convergent_partial_sums | Series existence gives partial-sum convergence. |
| real_tail_partial_sums_reindex | Exact original/native partial-sum identity. |
| real_tail_series_sum_is_native_series_sum, native_series_sum_is_real_tail_series_sum | Both candidate directions under actual native reindexing. |
| convergent_real_tail_series_is_native_convergent, native_convergent_series_is_real_tail_convergent | Both convergence directions. |
| real_tail_series_block_from_partial_sums | For p>start and p<=q, the actual block p..q equals S(q)-S(p-1). |
| convergent_real_tail_series_has_cauchy_tails, real_tail_series_cauchy_tails_imply_convergent | Complete Cauchy criterion, including reversed empty blocks. |
| real_tail_series_partial_sums_close_from_small_tails | Finite-tail control handles both endpoint orders and equality. |
| convergent_real_tail_series_terms_tend_to_zero | The zero test on original data. |
| real_tail_series_absolute_reindex, absolutely_convergent_real_tail_series_converges, real_tail_series_absolute_sum_bound | Absolute-value compatibility, convergence and abs(L)<=M for candidate sums. |
| adjacent_decreasing_real_tail_has_nonincreasing_reindex | Adjacent original decrease gives full native nonincrease. |
| real_tail_alternating_series_converges_from_zero_terms | Nonnegative decreasing magnitudes tending to zero give alternating convergence at any integer start. |
| convergent_real_tail_alternating_series_forces_zero_terms | Nonnegative magnitudes of a convergent actual alternating series tend to zero. |
| real_tail_series_sum_add, real_tail_series_sum_scale | Actual existing sum/scaled data has candidate L+M or c*L, for every real c. |
| real_tail_series_restriction_reindex_is_native_tail, real_tail_series_nonempty_prefix_is_native_partial_sum | Actual restriction and finite-prefix compatibility. |
| real_tail_series_sum_remove_finite_prefix, real_tail_series_sum_restore_finite_prefix | Both candidate directions, with the exact finite prefix and k in N including zero. |
| convergent_real_tail_series_remains_convergent_after_finite_prefix, convergent_real_tail_restriction_gives_convergent_series | Both finite-prefix convergence directions. |
| real_tail_series_sum_translate | Every integer translation preserves the candidate value. |
| real_tail_telescoping_series_sum | If a tends to L, its actual forward differences sum to a(start)-L. |

Every a parameter is a complete {j Z:j>=start}->R function. Cauchy endpoints
and cutoffs belong to that same tail. Since cutoff>=start, their quantification
is exactly the source quantification over every integer p,q above the cutoff.
Finite blocks use finite_set_sum(closed_range(p,q),a), including p>q. Actual
partial sums use native sum only on the legal nonempty range start..n.

The example checks signed geometric data from start -2, its absolute sum,
negative-start alternating convergence, zero and nonzero prefix lengths,
translation by -5, real scaling, telescoping and a convergent alternating
harmonic series that is not absolutely convergent:

```ini
[import std]
TailSeries = real_tail_series
Real = real_sequences
Series = real_series
Limits = real_sequence_limsup
Approximation = real_approximation
FiniteSums = finite_sums
[alias]
ts = TailSeries::main
rs = Real::main
series = Series::main
limits = Limits::main
approx = Approximation::main
fs = FiniteSums::main
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

release thm ts::real_tail_series_sum_implies_convergent(-2,signed_geometric,-1/3)

release thm ts::real_tail_series_sum_value(-2,signed_geometric,-1/3)

\ts::real_tail_series_sum<-2>(signed_geometric)=-1/3

release thm ts::convergent_real_tail_series_has_cauchy_tails(-2,signed_geometric)

release thm ts::convergent_real_tail_series_terms_tend_to_zero(-2,signed_geometric)

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

claim:
    ? forall k N+:
        \rs::real_tail_reindex<-2,positive_geometric>(k)=\rs::real_tail_reindex<-2,\limits::real_tail_absolute_values<-2,signed_geometric>>(k)
    release thm rs::real_tail_positive_index(-2,k)
    (-2+k-1)+3=k
    signed_geometric(-2+k-1)=(-1/2)^k
    positive_geometric(-2+k-1)=(1/2)^k
    release thm approx::absolute_value_integer_power(-1/2,k)
    abs(-1/2)=1/2
    abs(signed_geometric(-2+k-1))=abs((-1/2)^k)=abs(-1/2)^k=(1/2)^k
    \limits::real_tail_absolute_values<-2,signed_geometric>(-2+k-1)=abs(signed_geometric(-2+k-1))=(1/2)^k
    release thm rs::real_tail_reindex_at(-2,\limits::real_tail_absolute_values<-2,signed_geometric>,k)
    release thm rs::real_tail_reindex_at(-2,positive_geometric,k)
    \rs::real_tail_reindex<-2,positive_geometric>(k)=(1/2)^k=\limits::real_tail_absolute_values<-2,signed_geometric>(-2+k-1)=\rs::real_tail_reindex<-2,\limits::real_tail_absolute_values<-2,signed_geometric>>(k)

release thm series::series_sum_extensional(\rs::real_tail_reindex<-2,positive_geometric>,\rs::real_tail_reindex<-2,\limits::real_tail_absolute_values<-2,signed_geometric>>,1)

release thm ts::native_series_sum_is_real_tail_series_sum(-2,\limits::real_tail_absolute_values<-2,signed_geometric>,1)

release thm ts::real_tail_series_sum_implies_convergent(-2,\limits::real_tail_absolute_values<-2,signed_geometric>,1)

by def $ts::is_absolutely_convergent_real_tail_series(-2,signed_geometric)

release thm ts::absolutely_convergent_real_tail_series_converges(-2,signed_geometric)

release thm ts::real_tail_series_absolute_sum_bound(-2,signed_geometric,-1/3,1)

abs(-1/3)<=1

claim:
    ? closed_range(0,-1) $subset {j Z:j>=-2}
    claim:
        ? forall n closed_range(0,-1):
            n $in {j Z:j>=-2}
        n $in Z
        n>=0>=-2
        n $in {j Z:j>=-2}
    by def closed_range(0,-1) $subset {j Z:j>=-2}

finite_set_sum(closed_range(0,-1),signed_geometric)=0

release thm ts::native_series_sum_is_real_tail_series_sum(-2,positive_geometric,1)

release thm ts::real_tail_series_sum_implies_convergent(-2,positive_geometric,1)

release thm ts::convergent_real_tail_series_terms_tend_to_zero(-2,positive_geometric)

claim:
    ? forall n {j Z:j>=-2}:
        n+1 $in {j Z:j>=-2}
    n $in Z
    n>=-2
    n+1 $in Z
    n+1>=n>=-2
    n+1 $in {j Z:j>=-2}

claim:
    ? forall n {j Z:j>=-2}:
        positive_geometric(n)>=0
        positive_geometric(n+1)<=positive_geometric(n)
    n $in Z
    n+3 $in Z
    n+3 $in R
    (1/2)^(n+3)>0
    positive_geometric(n)=(1/2)^(n+3)>0
    (n+1)+3=(n+3)+1
    positive_geometric(n+1)=(1/2)^((n+1)+3)=(1/2)^((n+3)+1)=(1/2)^(n+3)*(1/2)^1=(1/2)^(n+3)*(1/2)=positive_geometric(n)*(1/2)<=positive_geometric(n)*1=positive_geometric(n)

release thm ts::real_tail_alternating_series_converges_from_zero_terms(-2,positive_geometric)

claim:
    ? forall last Z:
        closed_range(-2,last) $subset {j Z:j>=-2}
    claim:
        ? forall n closed_range(-2,last):
            n $in {j Z:j>=-2}
        n $in Z
        n>=-2
        n $in {j Z:j>=-2}
    by def closed_range(-2,last) $subset {j Z:j>=-2}

release thm ts::real_tail_series_sum_remove_finite_prefix(-2,signed_geometric,-1/3,0)

claim:
    ? finite_set_sum(closed_range(-2,-2+0-1),signed_geometric)=0
    release thm fs::integer_closed_interval_empty(-2,-2+0-1)
    finite_set_sum({},signed_geometric)=0
    finite_set_sum(closed_range(-2,-2+0-1),signed_geometric)=finite_set_sum({},signed_geometric)=0

claim:
    ? $ts::has_real_tail_series_sum(-2+0,\limits::real_tail_restriction<-2,signed_geometric,-2+0>,-1/3)
    -1/3-finite_set_sum(closed_range(-2,-2+0-1),signed_geometric)=-1/3-0=-1/3
    $ts::has_real_tail_series_sum(-2+0,\limits::real_tail_restriction<-2,signed_geometric,-2+0>,-1/3)

claim:
    ? finite_set_sum(closed_range(-2,-2+3-1),signed_geometric)=-3/8
    -2+3-1=0
    closed_range(-2,-2+3-1)=closed_range(-2,0)
    signed_geometric(-2)=-1/2
    signed_geometric(-1)=1/4
    signed_geometric(0)=-1/8
    finite_set_sum(closed_range(-2,0),signed_geometric)=-3/8
    finite_set_sum(closed_range(-2,-2+3-1),signed_geometric)=finite_set_sum(closed_range(-2,0),signed_geometric)=-3/8

release thm ts::real_tail_series_sum_remove_finite_prefix(-2,signed_geometric,-1/3,3)

claim:
    ? $ts::has_real_tail_series_sum(-2+3,\limits::real_tail_restriction<-2,signed_geometric,-2+3>,1/24)
    -1/3-finite_set_sum(closed_range(-2,-2+3-1),signed_geometric)=-1/3-(-3/8)=1/24
    $ts::has_real_tail_series_sum(-2+3,\limits::real_tail_restriction<-2,signed_geometric,-2+3>,1/24)

release thm ts::real_tail_series_sum_restore_finite_prefix(-2,signed_geometric,1/24,3)

claim:
    ? 1/24+finite_set_sum(closed_range(-2,-2+3-1),signed_geometric)=-1/3
    1/24+finite_set_sum(closed_range(-2,-2+3-1),signed_geometric)=1/24+(-3/8)=-1/3

release thm ts::convergent_real_tail_series_remains_convergent_after_finite_prefix(-2,signed_geometric,3)

release thm ts::convergent_real_tail_restriction_gives_convergent_series(-2,signed_geometric,3)

release thm ts::real_tail_series_sum_translate(-2,signed_geometric,-1/3,-5)

release thm ts::real_tail_series_sum_implies_convergent(-2+(-5),\ts::real_tail_series_translate<-2,signed_geometric,-5>,-1/3)

release thm ts::real_tail_series_sum_value(-2+(-5),\ts::real_tail_series_translate<-2,signed_geometric,-5>,-1/3)

claim:
    ? \ts::real_tail_series_translate<-2,signed_geometric,-5>(-2+(-5))=-1/2
    (-2+(-5))-(-5)=-2
    signed_geometric(-2)=-1/2
    \ts::real_tail_series_translate<-2,signed_geometric,-5>(-2+(-5))=signed_geometric((-2+(-5))-(-5))=signed_geometric(-2)=-1/2

release thm ts::real_tail_series_sum_add(-2,signed_geometric,positive_geometric,-1/3,1)

release thm ts::real_tail_series_sum_scale(-2,signed_geometric,-1/3,sqrt(2))

release thm ts::real_tail_telescoping_series_sum(-2,positive_geometric,0)

claim:
    ? $ts::has_real_tail_series_sum(-2,\ts::real_tail_forward_difference<-2,positive_geometric>,1/2)
    positive_geometric(-2)=1/2
    positive_geometric(-2)-0=1/2-0=1/2
    $ts::has_real_tail_series_sum(-2,\ts::real_tail_forward_difference<-2,positive_geometric>,1/2)

release thm ts::real_tail_series_sum_implies_convergent(-2,\ts::real_tail_forward_difference<-2,positive_geometric>,1/2)

release thm ts::real_tail_series_sum_value(-2,\ts::real_tail_forward_difference<-2,positive_geometric>,1/2)

release obj def rs::positive_real_reciprocal_tail

release thm rs::positive_real_reciprocal_tail_limit

claim:
    ? forall n {j Z:j>=1}:
        n+1 $in {j Z:j>=1}
    n $in Z
    n>=1
    n+1 $in Z
    n+1>=n>=1
    n+1 $in {j Z:j>=1}

claim:
    ? forall n {j Z:j>=1}:
        rs::positive_real_reciprocal_tail(n)>=0
        rs::positive_real_reciprocal_tail(n+1)<=rs::positive_real_reciprocal_tail(n)
    n $in Z
    n>=1>0
    n+1>n>0
    0<n*(n+1)
    rs::positive_real_reciprocal_tail(n)=1/n>0
    rs::positive_real_reciprocal_tail(n+1)=1/(n+1)
    1/(n+1)=n/(n*(n+1))<=(n+1)/(n*(n+1))=1/n
    rs::positive_real_reciprocal_tail(n+1)<=rs::positive_real_reciprocal_tail(n)

release thm ts::real_tail_alternating_series_converges_from_zero_terms(1,rs::positive_real_reciprocal_tail)

release thm ts::real_tail_series_sum_selected(1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>)

claim:
    ? \ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>(1)=-1
    rs::positive_real_reciprocal_tail(1)=1
    (-1)^1=-1
    \ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>(1)=(-1)^1*rs::positive_real_reciprocal_tail(1)=(-1)*1=-1

claim:
    ? forall k N+:
        \rs::real_tail_reindex<1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>>(k)=1/k
    release thm rs::real_tail_positive_index(1,k)
    1+k-1=k
    k $in Z
    k>=1
    k $in {j Z:j>=1}
    rs::positive_real_reciprocal_tail(k)=1/k>0
    release thm approx::absolute_value_integer_power(-1,k)
    abs(-1)=1
    abs((-1)^k)=abs(-1)^k=1^k=1
    \ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>(k)=(-1)^k*rs::positive_real_reciprocal_tail(k)=(-1)^k*(1/k)
    abs(1/k)=1/k
    abs(\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>(k))=abs((-1)^k*(1/k))=abs((-1)^k)*abs(1/k)=1*(1/k)=1/k
    \limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>(k)=abs(\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>(k))=1/k
    release thm rs::real_tail_reindex_at(1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>,k)
    \rs::real_tail_reindex<1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>>(k)=\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>(1+k-1)=\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>(k)=1/k

release thm series::harmonic_series_diverges(\rs::real_tail_reindex<1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>>)

claim:
    ? not $ts::is_absolutely_convergent_real_tail_series(1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>)
    by contra:
        ? not $ts::is_absolutely_convergent_real_tail_series(1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>)
        $ts::is_convergent_real_tail_series(1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>)
        release thm ts::convergent_real_tail_series_is_native_convergent(1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>)
        impossible $series::is_convergent_series(\rs::real_tail_reindex<1,\limits::real_tail_absolute_values<1,\ts::real_tail_alternating_terms<1,rs::positive_real_reciprocal_tail>>>)

claim:
    ? forall n {j Z:j>=1}:
        rs::positive_real_reciprocal_tail(n)>=0
    rs::positive_real_reciprocal_tail(n)>=0

release thm ts::convergent_real_tail_alternating_series_forces_zero_terms(1,rs::positive_real_reciprocal_tail)
```

Publish convergence before consuming a selected sum. Keep the original data
and exact dependent endpoint expressions, and establish interval inclusions
before aggregate use. Absolute values and restrictions reuse the existing
real_sequence_limsup functions. Addition/scaling reuse real_sequences data;
translation and forward differences construct the actual stated functions.
The source's broad use of “conditionally convergent” means ordinary convergence;
“only conditionally convergent” additionally excludes absolute convergence.

Proof basis: finite induction proves the exact partial-sum bridge; source
steadiness and native real completeness prove the Cauchy criterion. Existing
ordered-series mathematics supplies the zero, absolute and alternating tests.
Finite-domain triangle, source extensionality and native limit order give the
sum bound. Actual parity and integer-power identities retain the literal sign
(-1)^n for all integer starts. Prefix length zero is proved through complete
function extensionality and the actual empty prefix. Exact restrictions,
translation and native telescoping preserve the original domains and values.

The module has 54 statements: 31 named theorems, five propositions, five actual
function templates, nine carrier claims and four existing-definition releases.
Strict public-source, complete imported contracts, complete README and fresh
application gates pass; all 51 negative controls reject. Experiments retain the
exact receipts and earlier attempts. No new axiom, trust, native source change
or build is included. General membership verification and evidence composition
and reuse remain owned by shared verify. Native lim retains its one-argument
real N+ sequence contract.
