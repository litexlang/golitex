# Real multivariable calculus

The input is one real vector in `cart_n(R,n)`, equivalently the exact function
space `fn(k closed_range(1,n)) R`. Dimensions are positive; coordinates start at 1.

`main.lit` proves candidates before selecting all eleven native values: scalar
and vector limits, partial derivatives, scalar and vector differentials,
gradient, Jacobian, Hessian, divergence, three-dimensional curl and Laplacian.
For example:

```litex
have fn bowl(x cart_n(R,2)) R=x(1)^2+x(2)^2
$has_gradient_at(bowl,(1,2),2,(2,4))
gradient_at(bowl,(1,2),2)(2)=4
```

`rules.lit` checks explicit algebra, scalar and vector composition, full chain
rules, component and trace laws for opaque functions. Mixed-partial exchange
requires derivatives on a neighbourhood and continuity; the two vector
identities consume the stated symmetric Hessians and identities of fields.
`continuous_composition.lit` proves continuity and a limit of `abs(x(1))` at
the origin by composing a continuous unary function with a coordinate map.
`coordinates/main.lit` imports the ordinary `std/real_multivariable` helpers.

Run each file with `target/release/litex -strict -lang en -f <file>`.
Negative controls are `examples/wd_negative/multivariable_without_proof.lit`
and `examples/wd_negative/multivariable_wrong_coordinate.lit`.

Selector WD consumes a previously proved candidate or existence. It does not
calculate one. Gradient/Jacobian existence alone does not assert total
differentiability. Hessian entries record the first and then second coordinate;
symmetry requires an additional theorem. Native multivariable Lean replay is
currently unsupported. Automatic expression proofs cover a bounded smooth
coordinate fragment; opaque functions use explicit BTs or definitions.
