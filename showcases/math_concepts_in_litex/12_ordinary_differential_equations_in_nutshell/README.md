# Ordinary Differential Equations in a Nutshell

This standalone showcase builds a relational derivative interface and proves
that `y(x)=x^2+1` solves the initial-value problem `y'=2x, y(0)=1`.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell
lean showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/same_math_in_lean.lean
```

The published Litex file contains no direct trust or local axiom.
