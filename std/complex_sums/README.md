# Complex finite sums and coefficient bounds

This module provides source proofs over native complex scalars, modulus and
finite sums. Import it as `ComplexSums = complex_sums` under `[import std]`.

| Source interface | Contract |
| --- | --- |
| `complex_natural_sum_triangle(f,n)` | Modulus of sum(0,n,f) is at most the sum of the termwise moduli |
| `complex_natural_sum_zero_tail(f,m,n)` | For m<=n and f(k)=0 whenever k>m, sum(0,n,f)=sum(0,m,f) |
| `real_natural_constant_sum(n,M)` | Sum of the constant real M from 0 to n is (n+1)M |
| `complex_natural_sum_uniform_bound(f,n,M)` | Termwise modulus at most M on 0,...,n gives modulus of the sum at most (n+1)M |

Here f:N->C is total and n,m are natural, including zero. The interval 0,...,n
contains n+1 terms. The uniform-bound theorem takes M in R and requires every
termwise bound; it does not assume that a supplied bound is valid.

## Finite vectors of moduli

`\ComplexSums::main::complex_finite_sequence_moduli<n,c>` is the real finite
list whose jth entry is C_abs(c(j)), for c in finite_seq(C,n). It includes the
empty list. `complex_finite_sequence_moduli_carrier(n,c)` exposes both its
finite-sequence and exact function carriers.
`complex_finite_sequence_norm_sum_carrier(n,c)` proves its finite sum is real.
Release those two theorems before a comparison involving this sum.

`complex_finite_sequence_strict_bound(n,c,j)`, for j in closed_range(1,n), proves

```litex
C_abs(c(j))<abs(finite_set_sum(closed_range(1,n),\ComplexSums::main::complex_finite_sequence_moduli<n,c>))+1
```

The expression on the right is a positive explicit bound. It is not an exact
polynomial degree. The proof uses the existing nonnegative-summand inequality
and explicitly releases the real sum carrier before that comparison.

The [check](validation/.ladr/check.py) passes 10 strict source declarations,
45 independent imported statements and four refusal controls, retaining the
valid context. Actual nonreal coefficients, a computed norm sum 3 and bound 4,
zero-length vectors, n=0 sums and nonzero zero-tail examples pass. Invalid
termwise bounds, a false zero-tail premise, a wrong sum and index 0 are refused.
See [acceptance](validation/.ladr/acceptance.json).

No axiom, trust, native rule, strategy, kernel, parser or compiler change is
introduced. These are dependencies for LADR polynomial growth. Coefficient
uniqueness, exact polynomial degree and complete FTA remain unfinished.
