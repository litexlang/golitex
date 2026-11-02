# Limit points, limsup/liminf and completeness

Every sequence keeps its complete original domain `{j Z:j>=start}` for an
arbitrary integer start. Adherence needs one epsilon-close term; continual
adherence needs one after every cutoff; a finite real limit point requires this
for every positive real epsilon. Source closeness uses the closed <=epsilon
bound. A convergent real sequence has its limit as its unique finite limit point.

The actual same-value restriction to each later integer tail defines the upper
and lower extremum sequences. These are ExtendedReal-valued functions, including
infinite values. The total `\real_tail_limsup<start>(a)` is the extended infimum
of all tail suprema; `\real_tail_liminf<start>(a)` is the extended supremum of all
tail infima. Neither construction requires boundedness. Native lim and the
existing public sequence interfaces retain their fixed contracts.

The module proves all six parts of Analysis I 6.4.12: eventual strict bounds;
arbitrarily late strict crossings; inf <= liminf <= limsup <= sup; bounds for
every finite limit point; finite extremal limits as actual limit points; and
convergence exactly when both extremal limits equal the same finite real.
Comparison preserves all four extended extrema. The squeeze theorem, an actual
absolute-value zero test and Cauchy/convergence equivalence retain the same
original domains. Cauchy existence reuses native completeness through the
already proved source/native reindexing bridge.

This complete example computes the two extremal limits of (-1)^n, proves its
two finite limit points and nonconvergence, and excludes zero as a limit point:

```ini
[import std]
Limits = real_sequence_limsup
RealExtrema = real_sequence_extrema
ExtendedSequences = extended_sequence_extrema
Real = real_sequences
Extended = extended_reals
Approximation = real_approximation
[alias]
rsl = Limits::main
sext = RealExtrema::main
xseq = ExtendedSequences::main
rs = Real::main
xreal = Extended::main
approx = Approximation::main
[export]
main = "./main.lit"
```

```litex
release obj def xreal::extended_real_sup

release obj def xreal::extended_real_negate

release obj def xreal::extended_set_supremum

release obj def xreal::extended_set_infimum

have fn alternating_tail(n {j Z:j>=0}) R=(-1)^n

claim:
    ? forall n {j Z:j>=0}:
        abs(alternating_tail(n))=1
        -1<=alternating_tail(n)<=1
    n $in Z
    n>=0
    alternating_tail(n)=(-1)^n
    release thm approx::absolute_value_integer_power(-1,n)
    abs((-1)^n)=abs(-1)^n=1^n=1
    abs(alternating_tail(n))=1
    release thm approx::absolute_value_two_sided_bounds(alternating_tail(n),1)

claim:
    ? $rsl::is_real_tail_limit_point(0,alternating_tail,1)
    claim:
        ? forall epsilon R+,cutoff {j Z:j>=0}:
            exist n {j Z:j>=0} st {n>=cutoff and $approx::is_epsilon_close(alternating_tail(n),1,epsilon)}
        cutoff>=0
        cutoff $in N
        have n Z=2*cutoff
        n>=cutoff>=0
        n $in {j Z:j>=0}
        (-1)^(2*cutoff)=((-1)^2)^cutoff=1^cutoff=1
        alternating_tail(n)=(-1)^n=1
        abs(alternating_tail(n)-(1))=0<=epsilon
        by def $approx::is_epsilon_close(alternating_tail(n),1,epsilon)
        witness exist index {j Z:j>=0} st {index>=cutoff and $approx::is_epsilon_close(alternating_tail(index),1,epsilon)} from n
    release thm rsl::real_tail_arbitrarily_late_close_is_limit_point(0,alternating_tail,1)

claim:
    ? $rsl::is_real_tail_limit_point(0,alternating_tail,-1)
    claim:
        ? forall epsilon R+,cutoff {j Z:j>=0}:
            exist n {j Z:j>=0} st {n>=cutoff and $approx::is_epsilon_close(alternating_tail(n),-1,epsilon)}
        cutoff>=0
        cutoff $in N
        have n Z=2*cutoff+1
        cutoff+1>=0
        n=2*cutoff+1=cutoff+(cutoff+1)>=cutoff+0=cutoff
        n>=cutoff>=0
        n $in {j Z:j>=0}
        (-1)^(2*cutoff)=((-1)^2)^cutoff=1^cutoff=1
        (-1)^(2*cutoff+1)=(-1)^(2*cutoff)*(-1)^1=1*(-1)=-1
        alternating_tail(n)=(-1)^n=-1
        abs(alternating_tail(n)-(-1))=0<=epsilon
        by def $approx::is_epsilon_close(alternating_tail(n),-1,epsilon)
        witness exist index {j Z:j>=0} st {index>=cutoff and $approx::is_epsilon_close(alternating_tail(index),-1,epsilon)} from n
    release thm rsl::real_tail_arbitrarily_late_close_is_limit_point(0,alternating_tail,-1)

release thm xreal::real_number_is_extended_real(1)

release thm xreal::real_number_is_extended_real(-1)

claim:
    ? $sext::is_real_tail_upper_bound(0,alternating_tail,1) and $sext::is_real_tail_lower_bound(0,alternating_tail,-1)
    claim:
        ? forall n {j Z:j>=0}:
            alternating_tail(n)<=1
        -1<=alternating_tail(n)<=1
        alternating_tail(n)<=1
    claim:
        ? forall n {j Z:j>=0}:
            -1<=alternating_tail(n)
        -1<=alternating_tail(n)<=1
        -1<=alternating_tail(n)
    by def $sext::is_real_tail_upper_bound(0,alternating_tail,1)
    by def $sext::is_real_tail_lower_bound(0,alternating_tail,-1)

claim:
    ? \rsl::real_tail_limsup<0>(alternating_tail)=1 and \rsl::real_tail_liminf<0>(alternating_tail)=-1
    release thm sext::real_tail_upper_bound_is_extended(0,alternating_tail,1)
    release thm sext::real_tail_lower_bound_is_extended(0,alternating_tail,-1)
    release thm sext::real_tail_supremum_le_upper_bound(0,alternating_tail,1)
    release thm sext::real_tail_infimum_ge_lower_bound(0,alternating_tail,-1)
    release thm rsl::real_tail_limit_points_between_liminf_limsup(0,alternating_tail,1)
    release thm rsl::real_tail_limit_points_between_liminf_limsup(0,alternating_tail,-1)
    release thm rsl::real_tail_four_extrema_order(0,alternating_tail)
    release thm xreal::extended_real_order_transitive(\rsl::real_tail_limsup<0>(alternating_tail),\sext::real_tail_supremum<0>(alternating_tail),1)
    release thm xreal::extended_real_order_antisymmetric(\rsl::real_tail_limsup<0>(alternating_tail),1)
    release thm xreal::extended_real_order_transitive(-1,\sext::real_tail_infimum<0>(alternating_tail),\rsl::real_tail_liminf<0>(alternating_tail))
    release thm xreal::extended_real_order_antisymmetric(\rsl::real_tail_liminf<0>(alternating_tail),-1)

claim:
    ? not $rs::is_convergent_real_tail(0,alternating_tail)
    by contra:
        ? not $rs::is_convergent_real_tail(0,alternating_tail)
        obtain L from $rs::is_convergent_real_tail(0,alternating_tail)
        release thm rsl::real_tail_limit_equals_extremal_limits(0,alternating_tail,L)
        1=\rsl::real_tail_limsup<0>(alternating_tail)=L
        -1=\rsl::real_tail_liminf<0>(alternating_tail)=L
        1=-1
        impossible 1=-1

claim:
    ? not $rsl::is_real_tail_limit_point(0,alternating_tail,0)
    by contra:
        ? not $rsl::is_real_tail_limit_point(0,alternating_tail,0)
        release thm rsl::real_tail_limit_point_witness(0,alternating_tail,0,1/2,0)
        obtain n from exist n {j Z:j>=0} st {n>=0 and $approx::is_epsilon_close(alternating_tail(n),0,1/2)}
        abs(alternating_tail(n))=1
        abs(alternating_tail(n)-0)=abs(alternating_tail(n))=1
        abs(alternating_tail(n)-0)<=1/2
        impossible 1<=1/2
```

`\real_tail_restriction<start,a,cutoff>` accepts cutoffs in the original tail
and has precisely the later domain. Its start restriction equals a as an actual
function. `\real_tail_upper_extrema<start,a>` decreases and its lower dual
increases with the cutoff; comparison and extremal-limit theorems allow all
extended bounds, including both infinity markers. Finite limit-point parameters
remain in native R and epsilon parameters in R+.

`\real_tail_absolute_values<start,a>` is the actual pointwise absolute-value
function. The two zero-limit implications are separate callable theorems.
The completeness theorems construct an actual real source limit from source
Cauchyness and derive source Cauchyness from convergence.

The module has 59 source statements: 46 named theorems, six propositions,
six actual function templates and one supporting original-domain inclusion
proof. Source arithmetic, sets, existing extended extrema and native completeness
supply the proof basis. No new axiom, trust, native rule or kernel/WD change is
introduced. Full imported contracts, negative-start infinite tracers, a damped
oscillation squeeze/absolute-value/Cauchy application, quantifier controls and
complete strict receipts remain under experiments/.
