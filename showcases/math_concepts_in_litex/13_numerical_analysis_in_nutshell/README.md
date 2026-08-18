# Numerical Analysis in a Nutshell

This standalone showcase follows the named residual through three exact Newton
iterates for `x^2-2=0`, proves the scaled residual identity, and checks that the
residual magnitude drops from `1/4` to `1/144`.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell
lean showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/same_math_in_lean.lean
```

The theorem's public conclusion is stated with the reusable residual function;
the expanded polynomial expression appears only inside its proof. The
published Litex file contains no direct trust or local axiom.
