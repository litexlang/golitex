# Collection-Level Mathematical Design

This note records the cross-project dependency plan. Detailed concept cards
live in each child project's `math_collections.md`.

## First-version checkpoint

The first executable pass is complete in all six independent modules. The
current endpoints are radical-equation filtering, supplied inverse to
bijection, Bezout to linear Diophantine solvability, analytic Euclid I.1,
concrete `R^2` kernel-zero iff injective, and relational derivatives for
squares and affine functions. No cross-project import or direct `trust` was
needed for this checkpoint.

## Dependency legend

- **language**: a downstream project reuses the same ordinary mathematical
  vocabulary, without importing the current scratch implementation.
- **proof pattern**: a proof shape learned earlier reappears downstream.
- **future import**: a candidate dependency that may become an explicit import
  only after both sides stabilize.

## Typed dependency sketch

```text
Builtin arithmetic and order
  -> elementary algebra                         [language, proof pattern]
  -> analytic Euclidean geometry                [language]
  -> concrete linear algebra                    [language]
  -> real limits and derivative estimates       [language]

Builtin sets and functions
  -> sets/functions/relations                    [language]
  -> number-theory relations and constructions   [proof pattern]
  -> geometric loci and constructions            [future import]
  -> kernels, ranges, and subspaces               [future import]
  -> calculus domains and restrictions            [future import]

Elementary equality chains and case splits
  -> Euclidean coordinate arguments               [proof pattern]
  -> linear-map coordinate examples               [proof pattern]
  -> difference quotients and epsilon estimates   [proof pattern]

Existence witnesses and unique selection
  -> Bezout and Diophantine constructions          [proof pattern]
  -> inverse functions                            [proof pattern]
  -> basis coordinates                            [future import]
  -> limit, derivative, and integral selections   [future import]

Real completeness and compact intervals
  -> limit/continuity core                         [trust/source, future import]
  -> EVT and IVT                                   [proof]
  -> Rolle and MVT                                 [proof]
  -> continuous Riemann integrability and FTC      [proof]

Finite sequences and finite sums
  -> linear combinations and dimension            [future import]
  -> partitions and Riemann sums                   [future import]
```

There are no cross-project imports in the scratch tranche. That is deliberate:
an interface becomes shared library material only after independent projects
converge on the same semantic role, carrier, and downstream use.

## Build order

1. Stabilize the executable first version and boundary for each project.
   **Completed for the independent scratch checkpoint.**
2. Complete elementary algebra's equality/inequality proof vocabulary.
3. Complete set/function construction interfaces.
4. Develop number theory and Euclidean geometry independently as contrasting
   consumers of the proof language.
5. Keep the checked square-derivative tracer live while developing calculus
   Gate A: candidate limits, uniqueness, continuity, and compact-interval
   foundations.
6. Develop real-vector-space linear algebra Gate A, then audit which earlier
   set and function interfaces should become imports.
7. Admit calculus Gate B only after its uniqueness and compact-interval
   dependencies pass; finish MVT and its monotonicity/equation-uniqueness
   consumer.
8. Attempt finite-dimensional linear algebra and calculus Gate C only after
   their shared finite-sequence/finite-sum infrastructure is usable. Keep basis
   selection and Riemann-partition obligations separate.
9. Finish calculus Gate C with continuous integrability and FTC only when the
   full main chain has no direct trust.

## Shared non-goals

This collection is not an encyclopedic undergraduate library, a replacement
for the existing textbooks, a compatibility layer over unstable textbook
names, or a vehicle for moving broad mathematical theorems into the kernel.
