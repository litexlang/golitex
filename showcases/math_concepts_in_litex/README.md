# Math Concepts in Litex

This collection contains sixteen independent, executable showcases ordered as
a reader path from school mathematics to foundational and early undergraduate
topics.
The numeric prefixes are editorial order only: the projects do not import one
another.

Every directory publishes the same five artifacts:

- `main.lit`: a checked mathematical spine;
- `litex.config`: the standalone module entry;
- `README.md`: scope, run command, and trust boundary;
- `math_collections.md`: the concept/interface inventory; and
- `same_math_in_lean.lean`: a handwritten Lean analogy of the same semantics.

| No. | Project | Main line / flagship |
| ---: | --- | --- |
| 1 | `1_middle_school_math_in_nutshell` | equations, AM-GM, geometry, probability, statistics |
| 2 | `2_sets_functions_and_relations_in_nutshell` | finite sets, a callable function, a relation, and injectivity |
| 3 | `3_number_theory` | gcd/Bezout and linear Diophantine solvability |
| 4 | `4_discrete_mathematics_in_nutshell` | finite counting and direct Pascal recurrence |
| 5 | `5_linear_algebra` | fields, vector spaces, and kernel-zero iff injective |
| 6 | `6_abstract_algebra` | kernels of group homomorphisms are normal |
| 7 | `7_calculus` | epsilon-delta derivatives and tangent error |
| 8 | `8_probability_and_statistics_in_nutshell` | expectation linearity and Bayes' rule |
| 9 | `9_topology` | continuity, closed preimages, compact images |
| 10 | `10_real_analysis_in_nutshell` | unique sequence limits and a canonical selector |
| 11 | `11_multivariable_calculus_in_nutshell` | epsilon-delta partials and coordinate gradient |
| 12 | `12_ordinary_differential_equations_in_nutshell` | quadratic family and the IVP `y' = 2x, y(0)=1` |
| 13 | `13_numerical_analysis_in_nutshell` | Newton iteration with a proved gap bound |
| 14 | `14_tarski_geometry_from_axioms` | GeoCoq-aligned SST Chapters 2–11, Euclid I.5, and exact angle-based SAS |
| 15 | `15_category_theory_in_set_theory` | a generic set-coded small-category signature plus checked terminal and two-object chaotic instances |
| 16 | `16_probability_theory` | Borel events, event limits/Borel--Cantelli, and concrete probability constructions |

Run any project from the repository root:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell
lean showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/same_math_in_lean.lean
```

## Modeling and publication rules

Use a Builtin object or theorem first, then `std`, and declare a local concept
only when neither layer expresses the intended mathematics. Settings are the
default theorem-facing form; structs are for values that must be constructed,
stored, passed, compared, or returned.

Published files contain no direct `trust`, local axiom, Lean `axiom`,
`sorry`, or `admit`. Lean analogies state missing mathematics as explicit
structure fields or theorem hypotheses; analytic comparisons may use the
repository's Mathlib environment for standard objects such as real series.
Proof journals and other iteration records belong under
each project's `.drafts/` directory and are Git-ignored.
