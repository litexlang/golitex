# Linear Algebra Done Right

This draft module is a source-ordered Litex formalization of Chapters 1
through 9 of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. It
keeps Sections 1A through 9D. Standalone exercises are omitted.

## Run entrypoint and namespaces

Run the draft project with:

```sh
target/release/litex -compact -r scripts/textbooks_drafts/Linear-Algebra-Done-Right
```

`litex.config` exports the chapter namespaces in source order:

```text
chap1a -> ... -> chap3f -> chap4 -> chap5a -> ... -> chap9d
```

Cross-section uses remain explicit, for example `chap2a::span`. An explicit
structure type on a binding selects that binding's default field view, so
`scalars &chap1a::ScalarSystem<s>` supports field notation such as
`scalars.add(a,b)`. Generic vector-space interfaces name the carrier
`VSet` and the corresponding `VectorSpace` structure `V`, keeping later
expressions concise as `V.add(u,v)` and `V.smul(a,u)`.

## Implemented mathematical surface

The implemented draft surface includes:

- the builtin complex carrier `C`, with callable conjugation, real and
  imaginary projections, and absolute value;
- the `ScalarSystem` and `VectorSpace` structures and their mathematical laws;
- finite coordinate lists, coordinate spaces, function spaces, subspaces,
  finite subspace sums, and direct sums;
- linear combinations, span, linear independence, bases, and dimension;
- linear maps and their pointwise operations, null spaces, ranges,
  rank-nullity statements, matrices, invertibility, products, quotients, and
  duality;
- complex conjugation and absolute value, polynomial evaluation, degree,
  division, zeros, and complex and real factorization statements;
- operators, eigenvalues and eigenvectors, minimal polynomials, invariant
  subspaces, triangularization, diagonalization, Gershgorin disks, and
  commuting-operator statements;
- inner products, norms, orthogonality, orthonormal bases, adjoints,
  Gram–Schmidt, spectral and singular-value decompositions, and operator
  geometry;
- generalized eigenvectors, nilpotent/Jordan structure, traces, bilinear and
  multilinear forms, alternating forms, determinants, characteristic
  polynomials, and the current tensor-product interfaces.

A representative application shape is:

<!-- litex:skip-test -->
```litex
have x, y finite_seq(R, 2) = [1, 2], [3, 4]
\chap1a::coordinate_add<R, chap1a::real_scalars, 2>(x, y)
    $in finite_seq(R, 2)
```

## Verification and trust boundary

This is a runnable proof-debt-bearing translation, not a fully proved
formalization. Remaining `axiom` and direct `trust` boundaries are visible in
the exported section files. The
largest open boundaries concern selected algebraic structures, finite-list
recursion, basis and dimension infrastructure, matrix-coordinate
constructions, polynomial factorization, and the operator decomposition
theorems.

Chapter 1 has four localized boundaries: two complex-scalar adapter field
values after explicit `ScalarSystem` construction, the zero-length `FiniteList`
entry map in Section 1A, and packaging inherited subspace operations in
Section 1C. Dependent-list extensionality, the selected inverse equation,
binary direct-sum uniqueness, all five elementary
vector-space consequences in Section 1B, and both directions of the finite
and binary direct-sum criteria in Section 1C are checked.

Chapters 2 and 3 are fully source-represented and runnable. Chapter 2 has no
`axiom` and retains 35 localized direct `trust` steps (19, 5, and 11 in
Sections 2A, 2B, and 2C); clean release file gates pass for all three sections.
This includes checked proofs of exchange, basis reduction and extension,
complements, and the two-subspace dimension formula (Result 2.43), alongside
explicit remaining finite-list, basis-selection, and packaging debt. Chapter 3
remains a proof-debt-bearing development with 60 direct `trust` steps and 42
named source theorem or construction axioms.
Its boundaries cover matrix/rank constructions, quotient well-definedness,
and duality.
The finite-dimensional rank-nullity theorem and both finite-dimensional
domain/codomain dimension obstructions are checked; linear-system consequences
remain explicit boundaries. The open
items are tracked as translated rather than zero-trust checkable interfaces.

Across all 36 exports, the current direct-`trust` count is 178, down from the
captured 339-marker migration baseline. The current release verifier checks
every export independently with `-f`; the public textbook snapshot is not
modified by draft proof-debt cleanup.

`math_collections.md` records the intended interfaces and their dependency
order. Working plans, item records, verifier notes, and blockers live in
`scripts/linear_algebra_done_right/`.
