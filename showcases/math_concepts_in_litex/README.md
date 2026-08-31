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
| 6 | `6_abstract_algebra` | normal group kernels; prime ideals iff supplied quotients are domains |
| 7 | `7_calculus` | epsilon-delta derivatives and tangent error |
| 8 | `8_probability_and_statistics_in_nutshell` | expectation linearity and Bayes' rule |
| 9 | `9_topology` | continuity, closed preimages, compact images |
| 10 | `10_real_analysis_in_nutshell` | unique sequence limits and a canonical selector |
| 11 | `11_multivariable_calculus_in_nutshell` | epsilon-delta partials and coordinate gradient |
| 12 | `12_ordinary_differential_equations_in_nutshell` | quadratic family and the IVP `y' = 2x, y(0)=1` |
| 13 | `13_numerical_analysis_in_nutshell` | Newton iteration with a proved gap bound |
| 14 | `14_tarski_geometry_from_axioms` | GeoCoq-aligned SST Chapters 2–11, Euclid I.5, and exact angle-based SAS |
| 15 | `15_category_theory_in_set_theory` | categories, functors, natural transformations, and checked finite instances |
| 16 | `16_probability_theory` | Borel events, event limits/Borel--Cantelli, and concrete probability constructions |

Run any project from the repository root:

```bash
target/release/litex -graph -r showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell
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

## What “complete enough” means here

A subject is complete for this showcase collection when it has one checked
vertical slice:

```text
ambient setting / structure
  -> morphism or subobject
  -> one real construction
  -> one theorem that consumes the construction
  -> one concrete instance
  -> STOP
```

This is a publication boundary, not a claim to encyclopedic coverage. The
current stopping lines are:

- linear algebra: fields, vector spaces, linear maps, kernels, and the
  zero-kernel/injectivity criterion; no basis, dimension, rank-nullity, or
  quotient spaces in this version;
- abstract algebra: normal group kernels and the prime-ideal/supplied-quotient
  domain characterization; no Sylow/classification, general quotient
  construction, maximal-ideal correspondence, modules, or extension theory;
- topology: continuity, the closed-preimage criterion, compact subsets, and
  compact images; no filters, separation hierarchy, connectedness, or
  algebraic topology;
- single-variable calculus and real analysis may grow through the Mean Value
  Theorem and its elementary consequences, then stop; Riemann/Lebesgue
  integration and the Fundamental Theorem of Calculus are not first-version
  completion requirements;
- multivariable calculus and differential geometry stop at Euclidean
  derivatives, gradients, Jacobians, and elementary curves; no general
  manifolds, tangent bundles, metrics, connections, or curvature;
- ODE is complete at the checked explicit IVP family. Picard--Lindelof is one
  optional later flagship; systems, stability, and boundary-value theory are
  outside the first boundary;
- category theory stops at categories, functors, natural transformations,
  identity/composition, and a concrete terminal-category consumer; no limits,
  adjunctions, Yoneda, monads, or general functor categories;
- a future functional-analysis slice, if added, stops at normed/Banach spaces,
  bounded linear maps, and Banach's fixed-point theorem;
- a future PDE slice, if added, contains only explicit classical solutions of
  a few elementary equations; no weak solutions, Sobolev spaces, or general
  existence/regularity theory.

Algebraic geometry, homological algebra, representation theory, model theory,
and universal algebra are explicit collection non-goals. Empty placeholder
modules are not created for future subjects; their boundaries live here until
there is a checked vertical slice to publish.
