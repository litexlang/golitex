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

validation/.ladr/check.py checks 10 strict source declarations,
45 independent imported statements and four retained-context refusals.
Earlier verification used binary SHA-256
acbc6e6d9bdb9188bf2fb57bdbac22b8981486df925a53cf1154ab2c80d6de2e.
Examples cover nonreal coefficients (i,2i), norm sum 3 and bound 4, the empty
coefficient vector, zero-index sums and a finite zero tail. Invalid bound and
tail premises, a false sum and invalid index 0 are refused. A named pointwise
callback plus finite_set_sum_substitution computes the actual norm sum.

## Delivered growth interfaces

- growth::complex_modulus_of_real(x R)/1: C_abs(x)=abs(x).
- growth::complex_modulus_natural_power(z C,n N)/2:
  C_abs(z^n)=C_abs(z)^n, including n=0 and the monoid convention 0^0=1.
- growth::real_natural_power_exponent_monotone(x R+,m,n N)/3:
  x>=1 and m<=n imply x^m<=x^n.
- growth::complex_modulus_nonzero_positive(z C)/1:
  z!=0 implies C_abs(z)>0.
- growth::complex_power_sum_nonzero_from_leading_bound(n N+,c finite_seq(C,n+1),
  M,x R+,terms fn(k N) C)/5: x>=1, lower moduli at most M, the supplied
  representation through n and x*C_abs(c(n+1))>n*M imply sum(0,n,terms)!=0.
- growth::complex_power_representation_has_nonzero_value(n N+,c finite_seq(C,n+1),
  p fn(x R+) C)/3: a power representation and nonzero last coefficient
  imply existence of a positive-real input where p is nonzero.
- growth::complex_power_representation_truncation(n,m N,c finite_seq(C,n+1),
  prefix finite_seq(C,m+1),p fn(x R+) C,x R+)/6: m<=n, matching prefix entries
  and a zero tail preserve the value at x after truncation.
- growth::complex_zero_power_representation_coefficients(n N,c finite_seq(C,n+1),
  p fn(x R+) C,j closed_range(1,n+1))/4: representation and p=0 pointwise
  on R+ imply c(j)=0. No nonzero-leading-term premise is needed.
- growth::complex_power_representation_coefficients_unique(n N,left,right
  finite_seq(C,n+1),p fn(x R+) C,j closed_range(1,n+1))/5: representations
  of the same p imply left(j)=right(j).

The growth proof selects an explicit sufficiently large positive real input,
using the strict coefficient bound from main. The zero-coefficient theorem
selects the largest nonzero index from a finite subset of R and contradicts
growth after truncation; its constant case uses an indexed singleton sum.
Same-bound uniqueness applies that theorem to the coefficient difference.
There is no order on C, FTA premise, or coefficient-uniqueness premise in this
forward proof route.

## Delivered padding interfaces

coefficients::complex_finite_sequence_zero_padding<n N,m {size N:n<=size},
c finite_seq(C,n)> returns the actual complex function on closed_range(1,m)
which equals c(j) for j<=n and zero otherwise. The refined target length
enforces n<=m in the constructor. These parameters are vector lengths.

- complex_finite_sequence_zero_padding_carrier(n,m N,c finite_seq(C,n))/3:
  n<=m implies membership in finite_seq(C,m).
- complex_finite_sequence_zero_padding_head(n,m N,c finite_seq(C,n),j N+)/4:
  n<=m, j<=n and j<=m imply the jth entry equals c(j).
- complex_finite_sequence_zero_padding_tail(n,m N,c finite_seq(C,n),j N+)/4:
  n<=m, j>n and j<=m imply the jth entry is zero.
- complex_power_representation_padding(n,m N,c finite_seq(C,n+1),
  p fn(x R+) C,x R+)/5: n<=m and a representation through exponent n
  imply the padded representation through m at x.
- complex_power_representations_common_coefficients(n,m N,left finite_seq(C,n+1),
  right finite_seq(C,m+1),p fn(x R+) C,j N+)/6: two representations of p,
  j<=n+1 and j<=m+1 imply left(j)=right(j).
- complex_power_representation_excess_coefficients_zero(n,m N,left
  finite_seq(C,n+1),right finite_seq(C,m+1),p fn(x R+) C,j N+)/6:
  n<m, n+1<j<=m+1 and the two representations imply right(j)=0.

Prefix premises use dual guards j<=m+1 and j<=n+1, keeping each function
application well-defined before the enclosing size inequality is available.
No raw equality of finite functions with unequal domains is required.
The same-bound theorem is reused after padding both representations to n+m.

## Growth and comparison verification

validation/.ladr/power_use/check.py checks the strict 9-statement source
target, with registered main10/growth15 predecessors, 64 independent imported
statements and seven retained-context refusals. All consumed source/configuration
and executable hashes are recorded and checked by power_use/check.py.
Source growth15 also has its own strict receipt in growth_gate.json.
Concrete uses cover i+x at exponent bounds 1 and 3, zero at bounds 0 and 3,
empty vectors/padding, and powers with exponent zero. Refusals cover shrinking,
index zero, a zero leading term, an unproved zero-function premise, unequal
representations, an invalid head index and a false scalar entry.

These additions reuse finite_set_max, C_abs, natural powers, finite-set sum
addition/scaling/substitution and main's sum estimates. No new reserved BT
name/arity, native rule, strategy, AST, Env/Runtime, parser, verifier, compiler,
Lean bridge, trust or axiom was introduced. Public operation names retain one
fixed mathematical contract.

## Planned, not delivered

The native polynomial-function bridge, exact polynomial degree, polynomial
root count and complete FTA. This dependency checkpoint alone accepts no
additional LADR catalogue ID.
