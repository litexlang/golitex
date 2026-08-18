# Ordinary Differential Equations in a Nutshell

This standalone showcase builds both relational and selected-value derivative
interfaces and proves that `y(x)=x^2+1` solves the initial-value problem
`y'=2x, y(0)=1`. It also introduces the candidate family `y=x^2+c` and proves
that the initial value selects `c` uniquely.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell
```

`has_derivative_at(f, x, slope)` remains the epsilon-delta relation used to
prove candidate slopes. `is_differentiable_at(f, x)` records existence, and
`derivative_at(f, x)` selects the unique slope on that domain. Consequently the
ODE may also be read directly as
`derivative_at(f, x) = rhs(x, f(x))`, together with differentiability.

The fixed solution's epsilon-delta proof, general derivative-value uniqueness,
the unique selection, and both ODE interfaces are fully checked. A single
uniform derivative theorem for the function-valued quadratic family is not
asserted: the current verifier does not yet fold that lambda representation
back into the derivative predicate reliably. The published Litex file adds no
trust or axiom to hide that boundary.

`same_math_in_lean.lean` now works over `ℝ`, defines the same punctured
epsilon-delta derivative predicate, proves the quadratic difference-quotient
calculation directly, and also exposes the result through Mathlib's standard
`HasDerivAt` interface. Run it from the `lean/` project so Mathlib is available:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/same_math_in_lean.lean
```
