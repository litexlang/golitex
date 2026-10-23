# Ordered real series

This source library defines finite partial sums, real series convergence and a
guarded sum value, absolute convergence and convergence tests. It proves 78
source theorems using native finite sums, induction and real sequence limits.
It adds no kernel objects, reserved theorems or
automatic convergence search.

## Import and use

Add this to your project's `litex.config`, together with its `[export]` table:

```ini
[import std]
series = real_series
```

Imported source definitions are explicitly released in the caller. This
checked example proves a candidate before using the selected value:

```litex
release obj def series:::partial_sum
release obj def series:::partial_sums
release obj def series:::series_sum
release obj def series:::series_tail

have fn zero_terms(k N+) R=0
release thm series:::series_sum_zero(zero_terms)
release thm series:::series_sum_convergent(zero_terms,0)
release thm series:::series_sum_value(zero_terms,0)
series:::series_sum(zero_terms)=0
```

Publish the convergence guard before calling a theorem whose conclusion
contains `series_sum(a)`. Importing a module does not merge its ambient facts
into the caller. Its named theorems remain available through explicit calls.
See the [complete example](../../examples/real_analysis/series/main.lit).

## Functions and propositions

All inputs are complete real sequences indexed by `N+`; the equivalent
complete `fn(k N+) R` is accepted. Parameters `n,m` are positive integers and
`L,A,B,t,T` are real. The summation order is the given natural order.

| Interface | Meaning and domain |
| --- | --- |
| `partial_sum(a,n) R` | Inclusive `sum(1,n,a)`; requires `n in N+` |
| `partial_sums(a) seq(R)` | The complete sequence `n -> partial_sum(a,n)` |
| `$has_series_sum(a,L)` | `$has_seq_limit(partial_sums(a),L)` |
| `$is_convergent_series(a)` | A finite real candidate exists |
| `series_sum(a) R` | `lim(partial_sums(a))`, guarded by convergence |
| `series_tail(a,m) fn(k N+) R` | The complete sequence `k -> a(k+m)`, also in `seq(R)` |
| `absolute_terms(a) fn(k N+) R` | The complete sequence `k -> abs(a(k))` |
| `root_terms(a) fn(k N+) R` | The complete sequence `k -> abs(a(k))^(1/k)`; includes zero terms |
| `$is_absolutely_convergent_series(a)` | Convergence of `absolute_terms(a)` |
| `$is_cauchy_series(a)` | The native Cauchy property of `partial_sums(a)` |

The four propositions are ordinary source `prop` declarations. Negation uses
ordinary predicate negation; there are no dedicated series Fact variants.
`series_sum` consumes convergence evidence. Even the zero sequence has no
selected sum until that evidence is published.

Release `series:::absolute_terms` and `series:::root_terms` with
`release obj def` when using those constructions. The absolute and root maps
are functions; their convergence properties are propositions. No infinite-sum
AST or separate root-sequence AST is introduced.

## Theorems

Names below are qualified as `series:::name` in a caller. Pointwise premises
range over every `k in N+`, unless a tail restriction is stated. Write
`S(a,n)` for `partial_sum(a,n)` in this table only.

| Call | Required premises and result |
| --- | --- |
| `partial_sum_first(a)` | `S(a,1)=a(1)` |
| `partial_sum_successor(a,n)` | `S(a,n+1)=S(a,n)+a(n+1)` |
| `partial_sums_at(a,n)` | `partial_sums(a)(n)=S(a,n)` |
| `partial_sum_add(a,b,c,n)` | `c(k)=a(k)+b(k)` gives the corresponding partial-sum equality |
| `partial_sum_subtract(a,b,c,n)` | `c(k)=a(k)-b(k)` gives the difference equality |
| `partial_sum_scale(a,c,t,n)` | `c(k)=t*a(k)` gives `S(c,n)=t*S(a,n)` |
| `partial_sum_extensional(a,b,n)` | Equal terms give equal partial sums |
| `partial_sum_constant(a,t,n)` | Constant terms `t` give `S(a,n)=n*t` |
| `series_sum_unique(a,A,B)` | Candidates `A,B` imply `A=B` |
| `series_sum_convergent(a,L)` | Candidate `L` gives convergence |
| `convergent_series_limit_exists(a)` | Convergence gives a native partial-sum limit candidate's existence |
| `series_sum_selected(a)` | Convergence gives candidate `series_sum(a)` |
| `series_sum_value(a,L)` | Candidate `L` gives convergence and `series_sum(a)=L`; publish the guard first |
| `series_sum_from_partial_sums(a,s,L)` | `s -> L` and `s(n)=S(a,n)` give candidate `L` |
| `convergent_series_partial_sums(a)` | Series convergence gives sequence convergence of the partial sums |
| `partial_sums_convergent_series(a)` | The reverse implication |
| `series_sum_add(a,b,c,A,B)` | Candidates `A,B` and `c=a+b` give candidate `A+B` |
| `series_sum_subtract(a,b,c,A,B)` | Candidates `A,B` and `c=a-b` give candidate `A-B` |
| `series_sum_scale(a,c,A,t)` | Candidate `A` and `c=t*a` give candidate `t*A` |
| `series_sum_neg(a,c,A)` | Candidate `A` and `c=-a` give candidate `-A` |
| `series_sum_zero(a)` | Zero terms give candidate `0` |
| `series_sum_extensional(a,b,L)` | Candidate for `a` and equal terms transfer the candidate to `b` |
| `series_tail_at(a,m,k)` | `series_tail(a,m)(k)=a(k+m)` |
| `partial_sum_tail(a,m,n)` | `S(series_tail(a,m),n)=S(a,n+m)-S(a,m)` |
| `sequence_limit_from_shift(a,s,L,m)` | `s -> L` and `s(k)=a(k+m)` give `a -> L` |
| `series_sum_tail(a,L,m)` | Candidate `L` gives tail candidate `L-S(a,m)` |
| `series_sum_from_tail(a,T,m)` | Tail candidate `T` gives original candidate `T+S(a,m)` |
| `series_sum_finite_support(a,m)` | `a(k)=0` for `k>m` gives candidate `S(a,m)` |
| `series_sum_eventually_equal(a,b,L,m)` | Candidate `L` and equal terms for `k>m` give candidate `(L-S(a,m))+S(b,m)` for `b` |
| `series_terms_zero(a,L)` | A series candidate implies `$has_seq_limit(a,0)` |
| `convergent_series_tail(a,m)` | Convergence gives tail convergence |
| `tail_convergent_series(a,m)` | Tail convergence gives convergence |
| `convergent_series_terms_zero(a)` | Convergence implies `$has_seq_limit(a,0)` |

## Convergence and divergence theorems

The following 45 source theorems extend the 33 basic theorems above. All
sequence parameters are complete real sequences. Candidate limits and extrema
are finite reals. A conclusion of convergence does not compute a sum value.

| Call | Required premises and result |
| --- | --- |
| `series_cauchy_from_convergent(a)` | Convergence implies `is_cauchy_series(a)` |
| `series_convergent_from_cauchy(a)` | The converse, using real sequence completeness |
| `sequence_reciprocal_limit(a)` | `a(k)=1/k` implies `a -> 0` |
| `bernoulli_nonnegative(t,n)` | `t>=0,n in N` imply `(1+t)^n>=1+n*t` |
| `sequence_geometric_nonnegative_limit(a,q)` | `0<=q<1,a(k)=q^k` imply `a -> 0` |
| `absolute_natural_power(x,n)` | `abs(x^n)=abs(x)^n` for real x and positive integer n |
| `sequence_geometric_limit(a,r)` | `abs(r)<1,a(k)=r^k` imply `a -> 0` |
| `one_minus_nonzero(r)` | `r!=1` implies `1-r!=0` |
| `partial_sum_geometric(a,r,n)` | `r!=1,a(k)=r^k` give `S(a,n)=r*(1-r^n)/(1-r)` |
| `unit_abs_upper_bound(r)` | `abs(r)<1` gives `r<1,r!=1,1-r>0,1-r!=0` |
| `series_sum_geometric(a,r)` | `abs(r)<1,a(k)=r^k` give candidate `r/(1-r)`, including negative r and r=0 |
| `partial_sum_telescoping(a,u,n)` | `a(k)=u(k)-u(k+1)` gives `S(a,n)=u(1)-u(n+1)` |
| `series_sum_telescoping(a,u,L)` | Additionally `u -> L` gives candidate `u(1)-L` |
| `partial_sum_le(a,b,n)` | Pointwise `a<=b` implies `S(a,n)<=S(b,n)` |
| `partial_sum_nondecreasing(a,n,m)` | Nonnegative terms and `n<=m` imply `S(a,n)<=S(a,m)` |
| `nonnegative_partial_sums_nondecreasing(a)` | Nonnegative terms imply native `is_seq_nondecreasing(partial_sums(a))` |
| `nonzero_constant_series_diverges(a,c)` | `c!=0,a(k)=c` imply `not is_convergent_series(a)` |
| `harmonic_block_lower(a,n)` | `a(k)=1/k` implies `abs(S(a,2*n)-S(a,n))>=1/2` |
| `series_comparison(a,b)` | `b` converges and `0<=a(k)<=b(k)` imply convergence of `a` |
| `harmonic_series_diverges(a)` | `a(k)=1/k` implies actual nonconvergence |
| `absolute_terms_at(a,k)` | The absolute-term map's defining equality |
| `absolute_series_converges(a)` | Absolute convergence implies convergence |
| `absolute_series_comparison(a,b)` | `b` converges and `abs(a(k))<=b(k)` imply absolute convergence of `a` |
| `series_eventual_comparison(a,b,m)` | Positive comparison with inequalities only for `k>m` |
| `absolute_series_eventual_comparison(a,b,m)` | Absolute comparison with inequalities only for `k>m` |
| `absolute_terms_tail_at(a,m,k)` | Absolute terms commute pointwise with the tail construction |
| `absolute_series_from_tail(a,m)` | Absolute convergence of `series_tail(a,m)` implies absolute convergence of `a` |
| `series_geometric_domination(a,q,t,m)` | `0<=q<1,abs(a(k))<=t*q^k` for `k>m` imply absolute and ordinary convergence; t is real |
| `series_ratio_test(a,q,m)` | `0<=q<1,abs(a(k+1))<=q*abs(a(k))` for `k>=m` imply absolute and ordinary convergence; zeros are allowed |
| `nonnegative_natural_power_le(x,y,n)` | `0<=x<=y` implies `x^n<=y^n` for positive integer n |
| `nonnegative_root_power(x,n)` | `x>=0,n in N+` give a nonnegative real nth root and `(x^(1/n))^n=x` |
| `root_terms_at(a,k)` | Root-map equality, nonnegativity and `root_terms(a)(k)^k=abs(a(k))` |
| `series_root_test(a,q,m)` | `0<=q<1,root_terms(a)(k)<=q` for `k>=m` imply absolute and ordinary convergence |
| `nonnegative_sequence_limsup(a,L,m)` | Eventual `a(k)>=0` for `k>=m` and finite limsup L imply `L>=0` |
| `series_root_limsup_test(a,L)` | `has_seq_limsup(root_terms(a),L),L<1` imply absolute and ordinary convergence |
| `series_root_limit_test(a,L)` | The corresponding ordinary root-limit version |
| `absolute_terms_limit(a,L)` | `a -> L` implies `absolute_terms(a) -> abs(L)` |
| `series_ratio_limsup_test(a,ratio,L,m)` | A tail quotient represented by ratio, with finite limsup `L<1`, implies absolute and ordinary convergence |
| `series_ratio_limit_test(a,ratio,L,m)` | The corresponding ordinary ratio-limit version |
| `base_le_natural_power(x,n)` | `x>=1,n in N+` imply `x<=x^n` |
| `series_root_limsup_diverges(a,L)` | A finite root limsup `L>1` implies nonconvergence |
| `series_root_limit_diverges(a,L)` | The corresponding ordinary root-limit version |
| `series_ratio_diverges(a,q,m)` | `q>1,abs(a(m))>0` and `q*abs(a(k))<=abs(a(k+1))` for `k>=m` imply nonconvergence |
| `series_ratio_liminf_diverges(a,ratio,L,m)` | A tail quotient represented by ratio, with finite liminf `L>1`, implies nonconvergence |
| `series_ratio_limit_diverges(a,ratio,L,m)` | The corresponding ordinary ratio-limit version |

The four quotient theorems take a supplied complete real sequence `ratio`.
They require both `abs(a(k))>0` for `k>=m` and the guarded equality below.
Its early values are arbitrary, so early zero terms never create undefined
division:

```litex
forall k N+:
    k>=m
    0<abs(a(k))
    =>:
        ratio(k)=abs(a(k+1))/abs(a(k))
```

The strict thresholds matter: a ratio or root limit of 1 gives no conclusion.
A ratio limsup greater than 1 alone is not a divergence criterion. The root
limsup criterion does have a divergence direction above 1. See the
[imported convergence examples](../../examples/real_analysis/series/convergence/main.lit)
for actual checked calls in both directions.

## Boundaries and verification

There is no zero-length prefix in this version: `partial_sum(a,0)` is invalid.
Finite tuples and incomplete functions are not silently extended by zero.
Values are finite reals. Rearrangements, infinite extrema, conditional
convergence classification and products are outside this module. A zero term
limit alone does not establish series convergence; the harmonic example
proves both its zero term limit and its nonconvergence.

Normal verification JSON uses existing source-definition/theorem evidence.
This module adds no special infinite-sum LaTeX rendering or Lean support;
native analysis compilation retains its existing unsupported boundaries.

Run the focused positive and rejection checks from the repository:

```bash
python3 examples/real_analysis/series/check.py
```

The [mathematical design](math_collections.md) records the definitions and
dependency direction. The checks use strict mode and do not permit `trust`,
`axiom` or an assumed convergence result to stand in for a proof.
