# Complex finite-sum inventory

## Delivered Obj interface

`complex_finite_sequence_moduli<n N,c finite_seq(C,n)>` is the actual function
j in closed_range(1,n) maps to C_abs(c(j)), returning R. Thus it lies in
finite_seq(R,n), including n=0. This public name has one fixed two-template-
parameter contract; n is the vector length, not a polynomial degree bound.
No nonzero coefficient or positive-length assumption is imposed.

## Delivered source theorem contracts

- complex_natural_sum_triangle(f fn(k N) C,n N)/2:
  C_abs(sum(0,n,f)) <= sum(0,n,fn(k N) R {C_abs(f(k))}).
- complex_natural_sum_zero_tail(f fn(k N) C,m,n N)/3:
  m<=n and f(k)=0 for every natural k>m imply sum(0,n,f)=sum(0,m,f).
- real_natural_constant_sum(n N,M R)/2:
  sum(0,n,fn(k N) R {M})=(n+1)*M.
- complex_natural_sum_uniform_bound(f fn(k N) C,n N,M R)/3:
  C_abs(f(k))<=M on closed_range(0,n) implies C_abs(sum(0,n,f))<=(n+1)*M.
- complex_finite_sequence_moduli_carrier(n N,c finite_seq(C,n))/2:
  the moduli vector lies in finite_seq(R,n) and fn(k closed_range(1,n)) R.
- complex_finite_sequence_norm_sum_carrier(n N,c finite_seq(C,n))/2:
  finite_set_sum(closed_range(1,n),the moduli vector) lies in R.
- complex_finite_sequence_strict_bound(n N,c finite_seq(C,n),j closed_range(1,n))/3:
  C_abs(c(j)) < abs(finite_set_sum(closed_range(1,n),the moduli vector))+1.

## Proofs, WD and reuse

The natural-index sum includes n+1 terms. Source induction uses the existing
complex triangle inequality; zero-tail preservation and constant real sums are
also proved by induction. Uniform bounds reuse the triangle result and the
existing pointwise sum comparison. The coefficient bound uses termwise modulus
nonnegativity and finite_set_summand_le_sum, after explicit release of both
function and real-sum carrier theorems. Anonymous checked publications supply
those carrier facts before source theorem goal WD; callers do the same.

Reused Obj interfaces: C, N (including 0), R, C_abs, abs, sum,
finite_set_sum, finite_seq and ordinary functions. Reused BTs:
sum_le_sum_from_pointwise, finite_set_summand_le_sum and
finite_set_sum_substitution. No new predicate, reserved BT name/arity, builtin
rule, strategy, AST, parser, verifier or Lean interface was added or changed.
No trust or axiom is used.

## Verification

validation/.ladr/acceptance.json records 10 strict source declarations,
45 independent imported statements and four retained-context refusals.
The pinned binary SHA-256 is
acbc6e6d9bdb9188bf2fb57bdbac22b8981486df925a53cf1154ab2c80d6de2e.
Examples cover nonreal coefficients (i,2i), norm sum 3 and bound 4, the empty
coefficient vector, zero-index sums and a finite zero tail. Invalid bound and
tail premises, a false sum and invalid index 0 are refused. A named pointwise
callback plus finite_set_sum_substitution computes the actual norm sum.

## Planned, not delivered

Highest-term growth, coefficient uniqueness, exact polynomial degree,
polynomial root count and complete FTA. This dependency checkpoint alone
accepts no additional LADR catalogue ID.
