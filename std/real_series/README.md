# Ordered real series

This source library defines finite partial sums, real series convergence and a
guarded sum value. It proves 33 theorems using native finite sums, induction
and real sequence limits. It adds no kernel objects, reserved theorems or
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

The two propositions are ordinary source `prop` declarations. Negation uses
ordinary predicate negation; there are no dedicated series Fact variants.
`series_sum` consumes convergence evidence. Even the zero sequence has no
selected sum until that evidence is published.

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

## Boundaries and verification

There is no zero-length prefix in this version: `partial_sum(a,0)` is invalid.
Finite tuples and incomplete functions are not silently extended by zero.
Values are finite reals; absolute convergence, rearrangement, general geometric
series and convergence tests are subsequent work. A zero term limit alone
does not establish series convergence.

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
