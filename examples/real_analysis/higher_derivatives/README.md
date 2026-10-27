# Unary finite-order real derivatives

The example proves the first three derivative steps of `x^3` with existing unary
BTs, supplies the finite family, and then selects its third derivative 6 at 2.
It also checks order zero (8), order one (12), an actual `R+` input domain and
order zero of `abs(x)` at zero. A generic-point candidate is proved as well.

The independent unary candidate is `has_nth_derivative_at(D,k,f,p,L)`.
After proving it, release `nth_derivative_candidate_exists` and
`nth_derivative_value`. The selector is
`\Calc::unary_higher_order::nth_derivative<D,k>(f,p)`: two template parameters,
two ordinary arguments, real result. `R` inputs remain separate from
`cart_n(R,1)` inputs. Every intermediate derivative has its actual domain.

`boundaries.json` records the rejected controls: no higher-order proof, only a
pointwise first candidate, the unproved first derivative of `abs` at zero,
wrong values, invalid order, actual-domain violations, vector or multiple input
parameters, and incorrect arities. The installed integration test checks these
in one continued Session, with an accepted `0=0` after every rejection.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/higher_derivatives/main.lit
```

No high-order automatic differentiation, smoothness hierarchy or new native BT
is added. The explicit first-derivative calculations are proof steps outside WD.

[mixed.lit](mixed.lit) reuses the cubic results and the existing sine, cosine,
addition and subtraction BTs to prove `(x^3+sin(x))′′′(0)=5`. It supplies each
intermediate function explicitly and proves each step before selecting the
third-order value. The registered export order loads main first.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/higher_derivatives/mixed.lit
```

The refusal controls also check that an outer multiplication by zero cannot hide an undefined higher derivative.


[coherence.lit](coherence.lit) obtains a third-order certificate for the cubic,
then constructs its first and second derivative functions on the certificate's
actual preceding domains. Both values at2 are12; their next derivative
candidates are12 and6. Candidate-valued restriction and uniqueness justify the
first profile, and common-neighborhood uniqueness identifies the next value.
The current-order successor theorem takes m and returns the m+1 candidate.
`coherence_boundaries.json` adds11 refusal/liveness controls for all-point guards,
actual-domain membership, values, arity, scalar/vector separation and restriction
neighborhoods. The installed test verifies these in the same continued Session.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/higher_derivatives/coherence.lit
```
