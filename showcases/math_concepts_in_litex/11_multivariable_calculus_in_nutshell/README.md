# Multivariable Calculus in a Nutshell

This standalone showcase studies the quadratic scalar field
`f(x,y)=x^2+y^2`, proves its two exact coordinate difference quotients, turns
them into epsilon-delta partial derivatives, and verifies that `(2x,2y)` is
the coordinate gradient.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell
lean showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/same_math_in_lean.lean
```

The example uses native Cartesian products rather than a custom point object.
A general total-derivative/Jacobian interface is deliberately outside this
first version.
