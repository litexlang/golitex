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

## Growth and coefficient uniqueness

The `growth` export proves modulus of real scalars and natural complex powers,
monotonicity of natural powers for real bases at least one, and positivity of
the modulus of a nonzero complex scalar. These feed the highest-term estimate:
if x>=1, lower coefficient moduli are at most M>0, and
x*C_abs(c(n+1))>n*M, the represented sum is nonzero.

`complex_power_representation_has_nonzero_value(n,c,p)` constructs a positive
real input with nonzero value when n>0 and the last coefficient is nonzero.
`complex_zero_power_representation_coefficients(n,c,p,j)` proves every
coefficient zero when the represented function is zero on the positive real
axis, including n=0. `complex_power_representation_coefficients_unique` compares
two coefficient vectors with the same exponent bound.

All these representation functions have domain R+ and codomain C. Apply them
to an explicit restriction of a polynomial on R or C. They do not identify
function objects with different complete input domains.

The `coefficients` export provides
`complex_finite_sequence_zero_padding<n,m,c>`, for vector lengths n<=m. Its
head and tail theorems preserve entries through n and give zero after n;
both lengths may be zero. `complex_power_representation_padding` preserves a
power representation when its exponent bound increases. The comparison
theorems `complex_power_representations_common_coefficients` and
`complex_power_representation_excess_coefficients_zero` prove agreement at
common positions and zero coefficients beyond a shorter bound. Original
vectors of different lengths are never asserted equal.

The [power check](validation/.ladr/power_use/check.py) passes the 9-declaration
coefficient source target, strictly replaying its 10 sum and 15 growth
predecessors, plus 64 independent imported statements and seven refusals.
Examples cover i+x with bounds 1 and 3, the zero function at bounds 0 and 3,
nonreal coefficients and empty padding. Shrinking a padding, index zero, a
missing nonzero leading term, a missing zero-function premise, incompatible
representations, an invalid head index and a false entry are rejected while
retaining valid context. See [acceptance](validation/.ladr/power_use/acceptance.json).

No axiom, trust, native rule, strategy, kernel, parser or compiler change is
introduced. These are polynomial dependencies. Exact polynomial degree, a
general root count and complete FTA remain unfinished.
