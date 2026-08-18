# Ordinary Differential Equations in a Nutshell

This standalone showcase builds a relational derivative interface and proves
that `y(x)=x^2+1` solves the initial-value problem `y'=2x, y(0)=1`. It also
introduces the candidate family `y=x^2+c` and proves that the initial value
selects `c` uniquely.

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell
lean showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/same_math_in_lean.lean
```

The fixed solution's epsilon-delta derivative proof is fully checked. A single
uniform derivative theorem for the function-valued family is not asserted:
the current verifier does not yet fold that lambda representation back into
the derivative predicate reliably. The published file adds no trust or axiom
to hide that boundary.
