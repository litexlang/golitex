# From slopes to definite integrals

The central distinction is between a function, a proved fact about that
function, and a selected value that consumes the fact. The functions below
have domain `R`; the reciprocal example uses `R*` to exclude division by zero.
No local predicates reproduce native analysis interfaces.

## Point derivatives

`$has_derivative_at(square,3,6)` states a derivative candidate.
`derivative(square,3)` is the selected real value, usable after candidate or
existence evidence. The nearest rejected form is using the selector before
that evidence. The native derivative requires an interior point of the actual
function domain; it does not express an endpoint derivative relative to a
closed interval. `fn_derivative_at_to_limit` exposes its difference-quotient
limit, connecting the interface to the usual mathematical definition.

## Antiderivatives and the chain rule

`$is_antiderivative_on(F,f,R)` is a relation between existing functions: at
every real point, the derivative of `F` is `f`. It is not an operation choosing
an arbitrary primitive. For `square(x)=x^2`, `twice(x)=2*x`, and the sine/cosine
pair, `antiderivative_compose` gives the primitive `wave(x)=sin(x^2)` of
`weighted_cosine(x)=2*x*cos(x^2)`. The rule consumes the inner derivative law
and the displayed composition/product equations. This showcase uses `R`;
the current relation also supports explicit nonempty bounded open intervals,
not arbitrary disconnected sets.

## Newton–Leibniz and substitution

`$is_riemann_integrable(f,a,b)` asserts existence;
`$has_riemann_integral(f,a,b,I)` identifies a candidate. Both allow selection
of `integral(f,a,b)`, but existence alone does not give a numerical value.
`riemann_integral_newton_leibniz` consumes integrability of `f`, continuity of
`F` on the closed interval, and the interior derivative law `F'=f`.
The resulting candidate is `F(b)-F(a)`.

Substitution consumes a known integral candidate on the image interval,
continuity and derivative/image/product conditions. The map `x^2` sends both
endpoints of `[-1,1]` to `1`; the zero-length cosine integral gives a zero
candidate for the weighted cosine integral. This version does not require
the substitution map to be injective or monotone. It is an oriented integral
identity, not a claim that `x^2` parametrizes its image once.

## Integration by parts

With `u(x)=x`, `u'(x)=1`, and `v(x)=v'(x)=exp(x)`, a known exponential
integral supplies the right-hand candidate in
`integral(u*v') = [u*v] - integral(u'*v)`. The implemented rule checks
continuity of the four factor/derivative functions, their derivative laws,
and both product equations. It is a C1 sufficient-condition interface,
not the weakest possible integration-by-parts theorem.

All selections require well-defined actual domains covering the relevant
closed intervals. The examples use finite proper real integrals, with no
improper integration, higher derivatives, or general symbolic integration.
Strict verification excludes source `trust` and user axioms; it still relies
on Litex's builtin analysis rules and verifier.
