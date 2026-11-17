# Textbook Calculus: Derivatives, Chain Rules, and Definite Integrals

This directory collects **30 textbook-style calculus examples** checked natively in strict mode without user axioms or `trust`:

- [textbook_derivatives_and_chain_rule.lit](textbook_derivatives_and_chain_rule.lit): **20 derivative & chain-rule examples** covering elementary and multi-layer chain rules, guarded quotients/logarithms/radicals, variable exponents via $\exp(v(x)\ln u(x))$, inverse-function and even-function derivative theorems, stationary/critical/tangent/ODE propositions, the antiderivative chain rule, and multivariable gradients and Jacobians (Part I also available standalone in [textbook_chain_rule_examples.lit](../real_analysis/textbook_chain_rule_examples.lit)).
- [textbook_riemann_integrals.lit](textbook_riemann_integrals.lit): **10 definite Riemann integral (`integral`) examples** covering polynomial integration with signed reversal and zero-width intervals, exactness of Simpson's $1/3$ rule on cubics, linearity and automatic integrability closure (products, `abs`, Gaussians, nowhere-zero continuous denominators), Newton–Leibniz with automatic `deriv`, piecewise `abs(x)` splitting, integration by parts (`integ_parts`), $u$-substitution (`riemann_integral_substitution`) with odd cancellation, custom integral-average and $L^2$-orthogonality `prop`s (Legendre polynomials $P_1, P_2$), and integral comparison bounds on $\int_0^1 \frac{dx}{1+x^2}$ (complementing the 10 foundational examples in [textbook_integral_examples.lit](../real_analysis/textbook_integral_examples.lit)).

## I. Derivatives and Chain Rules (`textbook_derivatives_and_chain_rule.lit`)

| # | Topic / Construction | Verified Mathematical Statement |
| ---: | --- | --- |
| 1 | Power of an affine function | $((3x+1)^5)'\big|_a = 15(3a+1)^4$ |
| 2 | Sine of a square | $(\sin(x^2))'\big|_a = 2a\cos(a^2)$ |
| 3 | Exponential of a sine | $(e^{\sin x})'\big|_a = e^{\sin a}\cos a$ |
| 4 | Three-layer elementary composition | $(\sin(e^{x^2}))'\big|_a = 2ae^{a^2}\cos(e^{a^2})$ |
| 5 | Logarithm of a positive polynomial | $(\ln(1+x^2))'\big|_a = \frac{2a}{1+a^2}$ |
| 6 | Square root of a positive polynomial | $(\sqrt{1+x^2})'\big|_a = \frac{a}{\sqrt{1+a^2}}$ |
| 7 | Product and chain rules | $(x^2 e^{3x})'\big|_a = e^{3a}(2a + 3a^2)$ |
| 8 | Quotient and chain rules | $\left(\frac{\sin x}{1+x^2}\right)'\Big|_a = \frac{(1+a^2)\cos a - 2a\sin a}{(1+a^2)^2}$ |
| 9 | Stationary-point `prop` | $((x^2-1)^2)'\big|_a = 4a(a^2-1)$ and `$stationary_at` at $\pm 1$ |
| 10 | Abstract three-layer chain rule | $(f \circ g \circ h)'(a) = f'(g(h(a)))g'(h(a))h'(a)$ |
| 11 | Damped oscillation & point evaluation | $w(x) = e^{2x}\cos(3x)$, general formula and $w'(0) = 2$ |
| 12 | Guarded abstract chain + quotient | $(f(g(x))/h(x))'\big|_{x_0}$ on $\{x \in \mathbb{R} : h(x) \neq 0\}$ |
| 13 | Guarded logarithmic & radical chain | $(\ln f(x))'$ on $\{0 < f(x)\}$ and $(\sqrt{f(x)})'$ on $\{0 \le f(x)\}$ with $0 < f(x_0)$ |
| 14 | Variable-exponent power via $\exp(v\ln u)$ | $(\exp(v(x)\ln u(x)))'\big|_{x_0}$ and $(\exp(x\ln x))'\big|_1 = 1$ |
| 15 | Inverse function derivative `thm` | $(\forall x \in \mathbb{R},\ g(f(x)) = x) \land f'(x_0) \neq 0 \implies g'(f(x_0)) = 1/f'(x_0)$ |
| 16 | Even function derivative parity `thm` | $(\forall x \in \mathbb{R},\ f(-x) = f(x)) \implies f'(x_0) = -f'(-x_0)$ |
| 17 | Critical-point composition `thm` | `$is_critical_point(g, x0)` $\implies$ `$is_critical_point(f \circ g, x0)` |
| 18 | Tangent-line `prop` on Gaussian curve | $y = e^{-1} - 2e^{-1}(x - 1)$ is tangent to $e^{-x^2}$ at $a = 1$ |
| 19 | 1D conservative ODE energy law `thm` | $q' = v,\ v' = -V'(q) \implies \frac{d}{dt}\left(\frac{1}{2}v(t)^2 + V(q(t))\right) = 0$ |
| 20 | Antiderivative & multivariable chain | `$is_antiderivative_on` for $\sin(x^2)$, gradient of $e^{x_1^2+x_2^2}$, and $D(G \circ F)(p) = DG(F(p))DF(p)$ |

## II. Definite Riemann Integrals (`textbook_riemann_integrals.lit`)

| # | Topic / Construction | Verified Mathematical Statement |
| ---: | --- | --- |
| 1 | Cubic polynomial, signed reversal & zero width | $\int_0^2 (4x^3 - 3x^2 + 2x - 1)\,dx = 10$, $\int_2^0 \dots = -10$, $\int_2^2 \dots = 0$ |
| 2 | Exactness of Simpson's $1/3$ quadrature rule | $\forall a,b,c,d \in \mathbb{R},\ \int_0^2 p(x)\,dx = \frac{1}{3}(p(0) + 4p(1) + p(2))$ for $p(x)=ax^3+bx^2+cx+d$ |
| 3 | Linearity & automatic integrability closure | $\int_a^b (2f - g/c + 5) = 2\int_a^b f - \frac{1}{c}\int_a^b g + 5(b-a)$; integrability of $fg + |f-g|$, $e^{-x^2}$, $\frac{\cos x}{1+x^2}$ |
| 4 | Newton–Leibniz + automatic `deriv` | $\int_0^1 \frac{2x}{1+x^2}\,dx = [\ln(1+x^2)]_0^1 = \ln(2)$ |
| 5 | Piecewise / corner splitting (`abs`) | $\int_{-1}^2 |x|\,dx = \int_{-1}^0 (-x)\,dx + \int_0^2 x\,dx = \frac{5}{2}$ |
| 6 | Integration by parts (`integ_parts`) | $\int_0^{\pi/2} x\cos(x)\,dx = [x\sin(x)]_0^{\pi/2} - \int_0^{\pi/2} \sin(x)\,dx = \frac{\pi}{2} - 1$ |
| 7 | $u$-substitution & odd cancellation | $\int_0^1 2x e^{x^2}\,dx = e - 1$ and $\int_{-1}^1 2x e^{x^2}\,dx = 0$ |
| 8 | Integral average `prop` & Archimedes' `thm` | `$integral_average` with $\forall L \in \mathbb{R}^+,\ \frac{1}{L}\int_0^L x^2\,dx = \frac{L^2}{3}$ |
| 9 | $L^2$ orthogonality `prop` (Legendre $P_1, P_2$) | `$are_l2_orthogonal_on(leg_p1, leg_p2, -1, 1)` for $P_1(x)=x,\ P_2(x)=\frac{3}{2}x^2 - \frac{1}{2}$ |
| 10 | Integral comparison / squeeze bounds | $1 - x^2 \le \frac{1}{1+x^2} \le 1$ on $[0, 1] \implies \frac{2}{3} \le \int_0^1 \frac{dx}{1+x^2} \le 1$ |

## Verification

```bash
target/release/litex -strict -lang en -f examples/calculus/textbook_derivatives_and_chain_rule.lit
target/release/litex -strict -lang en -f examples/calculus/textbook_riemann_integrals.lit
```

## Authoring Pattern and Current Boundaries

- **Write values as equations**. Prefer `deriv(f, a) = v` and `integral(f, a, b) = I`. Shared verification checks their mathematical domains and establishes differentiability or integrability from supported function expressions and existing premises. For arbitrary functions, state the required `$diff_at(f, a)` or `$integrable(f, a, b)` assumptions.
- **Automatic integrability vs. automatic integral value**: `RiemannIntegrability` automatically discharges `$integrable` across arithmetic, products, `abs`, natural powers, continuous elementary compositions (`exp`, `ln`, `sin`, `cos`, `sqrt`), and nowhere-zero continuous denominators. `RiemannIntegralValue` automatically evaluates constants, natural powers $x^n$, linear combinations, scalar divisions, and known leaf integrals; nonlinear antiderivatives, piecewise corner splits, integration by parts, and change of variables invoke the explicit calculus theorems (`riemann_integral_newton_leibniz`, `riemann_integral_split`, `integ_parts`, `riemann_integral_substitution`).
- **Scope boundaries**: direct `abs(x)` differentiation away from zero, unexpanded variable-exponent `x^x` syntax (expressed via $\exp(x\ln x)$ in Example I.14), general transcendental antiderivative search and measure integrals, and independent Lean replay of the new native derivative/integral value strategies remain outside this native example gate.

## Improper integrals

[integral_audit_repairs.lit](integral_audit_repairs.lit) covers zero-function
infinite integrals, stored equality paths across fresh bound names, and
LaTeX grouping for powered open endpoints.

[improper_integrals.lit](improper_integrals.lit) checks finite open endpoints,
endpoint reversal, independent two-sided convergence, and both infinite
intervals. `integ(x,a,b,E)` binds the variable only in the expression.
`integ_oc`, `integ_co` and `integ_oo` preserve which endpoint is omitted.
Function arguments use `integral` and the canonical `integral_open_closed`,
`integral_closed_open`, `integral_open`, `integral_pos_inf` and
`integral_neg_inf` interfaces.

The finite open-endpoint operations require distinct endpoints. All operations
require the complete integration region to lie in the function domain.
Improper values additionally require local Riemann integrability and finite
convergence of each relevant truncation limit. The native examples run with
`-strict`. Their improper certificates currently have explicit unsupported
Lean compiler branches.

```bash
target/release/litex -strict -lang en -f examples/calculus/improper_integrals.lit
```
