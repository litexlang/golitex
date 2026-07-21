# Linear Algebra Done Right

This module is a source-ordered Litex formalization of Chapters 1–4 and
Sections 5A–5B of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. The repository-local
transcript dated 9 May 2026 is the source of truth. Standalone exercises are
omitted; definitions, notation, results, and mathematically useful explanatory
prose are retained in the order in which the book introduces them.

## Run entrypoint and namespaces

Run the current project with:

```sh
target/debug/litex -compact -runner -r textbooks/LinearAlgebraDoneRight
```

`litex.config` exports one namespace per source section, from `chap1a`
through `chap3f`, followed by `chap4`, `chap5a`, and `chap5b`. Cross-section uses are explicit,
for example `chap2a::span` and `chap3b::null_space`.

Chapter files use file-local macros such as `@ScalarSystem`, `@Scalars`,
`@Space`, and `@LinearMaps` for repeated fully qualified types, structure
views, and function families. `@ScalarSystem` denotes the bare scalar-system
type, while `@Scalars` denotes the view of the supplied `scalars` instance.
These macros are readability-only textual abbreviations: public declarations
keep their mathematical parameters explicit, and the canonical cross-file
namespaces remain `chap1a` through `chap5b`.

The ordinary project runner checks that the exported project loads and that
the public declarations are well formed. Because project exports are trusted
for speed, theorem-body checking uses the flattened isolated gate documented
in `scripts/linear_algebra_done_right/source_manifest.yaml`.

## Implemented mathematical surface

The current public surface includes:

- the concrete `Complex` carrier and callable complex operations;
- `ScalarSystem` and `VectorSpace` structures with callable operations and
  their mathematical laws, including a checked concrete real scalar instance;
- finite coordinate lists, coordinate spaces, function spaces, subspaces,
  finite subspace sums, and direct sums;
- linear combinations, span, linear independence, bases, and dimension;
- linear maps, null spaces, ranges, matrices of linear maps, rank,
  invertibility, products, quotient spaces, and dual spaces; and
- function-based polynomials, degree, zeros, complex factorization, conjugate
  roots, and the real quadratic splitting criterion; and
- operators, invariant subspaces, eigenvalues/eigenvectors, nonnegative
  operator powers, polynomial evaluation at an operator, and invariant null
  spaces and ranges of `p(T)`; and
- monic and annihilating polynomials, the uniquely selected minimal
  polynomial, restrictions to invariant subspaces, and the source-facing
  eigenvalue, divisibility, invertibility, and parity results of Section 5B.

Representative application shape:

<!-- litex:skip-test -->
```litex
have x, y finite_seq(R, 2) = [1, 2], [3, 4]
\chap1a::coordinate_add<R, chap1a::real_scalars, 2>(x, y)
    $in finite_seq(R, 2)
```

## Verification and trust boundary

This is a runnable proof-debt-bearing translation, not a completed foundation
for linear algebra. The checked declarations and the remaining named `axiom`
and direct `trust` boundaries are counted section by section in
`scripts/linear_algebra_done_right/source_manifest.yaml`. The largest open
boundaries are construction of selected complex/vector structures,
finite-list exchange and basis theorems, quotient well-definedness, rank,
duality, the analytic input to the fundamental theorem of algebra, and the
finite-sum algebra behind operator-polynomial multiplicativity.

`math_collections.md` records the intended mathematical interfaces and their
dependency order. Working plans, item records, verifier notes, and blockers
live only in `scripts/linear_algebra_done_right/`.
