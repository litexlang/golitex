# From derivatives to definite integrals

A derivative can identify a useful primitive; a primitive can turn an integral
into an endpoint calculation. This short lecture follows that thread from
`x^2` to `sin(x^2)`, then uses substitution and integration by parts. It shows
Litex's native calculus interfaces independently of the selected
[Analysis I chapters](../README.md).

The distinction to watch is between proving a value and using it. This complete
example first proves a derivative candidate, then selects the derivative:

```litex
have fn square(x R) R = x^2
$has_derivative_at(square, 3, 6)
derivative(square, 3) = 6
```

The derivative selector consumes the preceding proof. Using it before that
proof is rejected, even though the formula is familiar. The checked source
also exposes the corresponding difference-quotient limit and differentiates
`1/x` at `2`, with the nonzero domain retained in the function declaration.
The square example parallels Example 10.1.3 of Terence Tao's *Analysis I*;
the lecture is an independent selection, not a translation of Chapters 9–11.

## A chain rule becomes an integral

The derivative of `sin(x^2)` is `2*x*cos(x^2)`. The source proves the inner
square derivative and the sine derivative, then uses
`antiderivative_compose` to establish the composite primitive. An
antiderivative is a relation between two supplied functions, rather than a
command that searches for a primitive.

Here is the endpoint of that development, excerpted from its shared context:

<!-- litex:skip-test -->
```litex
release thm riemann_integrable_continuous(weighted_cosine, 0, 2)
release thm riemann_integral_newton_leibniz(weighted_cosine, wave, 0, 2)
wave(2) = sin(4)
wave(0) = 0
wave(2)-wave(0) = sin(4)
integral(weighted_cosine, 0, 2) = sin(4)
```

Continuity establishes integrability. Newton–Leibniz checks the derivative
law and continuity of the primitive, then supplies the candidate
`wave(2)-wave(0)`. Only then does the selected integral have the claimed value.
The underlying builtin analysis rules are part of Litex's trusted foundation;
this lecture does not reconstruct their foundational proofs.

## Change the interval, then change the method

On `[-1,1]`, the same substitution `u=x^2` has equal image endpoints.
The source supplies the zero-length cosine integral at `1`, then applies
`riemann_integral_substitution` to obtain
`integral(weighted_cosine,-1,1)=0`. The map is not monotone on this interval.
This example illustrates an oriented substitution identity with an explicit
factor `2*x`, rather than a one-to-one parametrization of the image.

Finally, integration by parts uses `u(x)=x`, `v(x)=exp(x)` and their
derivative functions. A previously established exponential integral gives
the right-hand term; the boundary calculation yields
`integral(weighted_exp,0,1)=1`. Both methods reuse proved candidates instead
of asking the integral selector to discover an integration technique.

## Reading map and boundaries

| In [the checked source](main.lit) | Mathematical move |
| --- | --- |
| Square and reciprocal | Point derivative candidate → selected value; difference-quotient limit |
| Sine of a square | Product rule for the square → chain rule → antiderivative relation |
| Weighted cosine on `[0,2]` | Continuity → integrability → Newton–Leibniz |
| Weighted cosine on `[-1,1]` | Nonmonotone substitution with equal image endpoints |
| Weighted exponential on `[0,1]` | Known exponential integral → integration by parts → endpoint cancellation |

This standalone module passes strict verification with no source `trust`,
user axioms, abstract predicates, or chapter imports. See the
[dated verification receipt](../../verification_runs/2026-10-24-native-calculus.json)
and [interface guide](math_collections.md).
Strict acceptance still relies on Litex's verifier and builtin mathematical
rules; no Lean replay is claimed.

Native point derivatives require an interior point of the actual domain.
They do not replace derivatives relative to arbitrary subsets or one-sided
endpoint derivatives in the textbook. The integrals here are finite proper
real Riemann integrals; general symbolic integration, improper integrals and
higher derivatives are outside this selection.
