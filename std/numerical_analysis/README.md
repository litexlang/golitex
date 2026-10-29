# Numerical analysis: positive square-root Newton iteration

This module proves a parameterized square-root Newton method in exact real
arithmetic. It contains 12 source theorems, two functions and a sequence
template. The radicand and starting value are arbitrary positive reals.
It does not supply a complete numerical-analysis course.

## Operations and results

| Interface | Contract and checked result |
| --- | --- |
| `newton_sqrt_step(a,x)` | a>0, x>0; returns (x+a/x)/2 as a positive real. |
| `newton_sqrt_iterate(a,start,n)` | Positive a/start, n in N including zero; u(0)=start and u(n+1)=step(a,u(n)). |
| `newton_sqrt_sequence<a,start>` | Native real sequence on N+, with value u(k). Its first value is the first update, not the initial seed. |
| `newton_sqrt_scaled_step` | 2*x*step=x^2+a. |
| `newton_sqrt_residual_identity` | 4*x^2*(step^2-a)=(x^2-a)^2. |
| `newton_sqrt_root_error_identity` | 2*x*(step-sqrt(a))=(x-sqrt(a))^2. |
| `newton_sqrt_step_is_above_root` | Every positive input maps to a value at least sqrt(a). |
| `newton_sqrt_step_decreases_above_root` | If x>=sqrt(a), the next value is at most x. |
| `newton_sqrt_error_halves` | Above the root, the nonnegative error after one step is at most half the previous error. |
| `newton_sqrt_error_is_quadratic` | Above the root, the next error is at most (x-sqrt(a))^2/(2*sqrt(a)). |
| `newton_sqrt_iterates_are_above_root`, `newton_sqrt_iterates_decrease` | Iterates are above the root and decrease from index 1 onward, even if the seed is below the root. |
| `newton_sqrt_iterate_error_bound` | For n>=1, u(n)-sqrt(a)<=(u(1)-sqrt(a))/2^(n-1). |
| `newton_sqrt_sequence_converges` | The native sequence has limit sqrt(a) for every positive radicand and seed. |
| `newton_sqrt_fixes_root` | The root itself is a fixed point of the update. |

Import `numerical_analysis` and alias its `main` export, for example
`num = Numerical::main`. Replay the two function definitions before using
their arithmetic values. The sequence is written
`\num::newton_sqrt_sequence<a,start>`. Call the convergence theorem before
using its native one-argument `lim` selector. The imported validation project
shows both arbitrary-parameter callers and exact iterate calculations.

## Verification and boundaries

`python3 std/numerical_analysis/validation/check.py` checks the independent
positive file, then keeps one strict Session for all refusal cases. It requires
each preceding frame to pass and only the intended final frame to reject.
`--negative-only` repeats just the refusal stage.

The strict source has 17 accepted declarations/statements. The actual full
std-imported consumer has 34 accepted statements: exact iterates, several
radicands/seeds, a seed already equal to the root, generic convergence/error
callers, and native limit values sqrt(2) and 3. Seven refusal cases cover zero
radicand/seed, negative index, the geometric estimate before index 1, local
decrease/quadratic estimates below the root, and the first update incorrectly
claimed always decreasing. The fresh refusal Session passes all seven checks.

The first update can increase: a=4 and start=1 give u(1)=5/2>u(0)=1. No
global decrease from index zero is claimed. The module excludes a=0 and
nonpositive seeds, performs no floating-point rounding or stability analysis,
and supplies no arbitrary-function Newton, bisection, interpolation, numerical
quadrature or ODE discretization result. It adds no trust or native rule.
See [math_collections.md](math_collections.md) for the mathematical dependencies.
