# Linear Algebra Done Right

This module is a source-ordered Litex formalization of all nine chapters of
Sheldon Axler's *Linear Algebra Done Right*, fourth edition. The
repository-local transcript dated 9 May 2026 is the source of truth. Standalone
exercises are omitted; definitions, notation, results, and mathematically useful
explanatory prose are retained in the order in which the book introduces them.

## Run entrypoint and namespaces

Run the current project with:

```sh
target/debug/litex -compact -runner -r textbooks/LinearAlgebraDoneRight
```

`litex.config` exports one namespace per source section, from `chap1a`
through `chap9d` (with the unsectioned polynomial chapter exported as
`chap4`). Cross-section uses are explicit, for example `chap2a::span`,
`chap8b::characteristic_polynomial`, and `chap9c::operator_determinant`.

An explicit structure type on a binding also selects that binding's default
view. Thus `scalars &chap1a::ScalarSystem<s>` permits direct field notation
such as `scalars.add(a,b)`, and a finite-list binding permits
`vectors.entries(k)`. All source declarations now use complete expressions;
there is no pre-parser abbreviation layer. Canonical cross-file namespaces
remain `chap1a` through `chap9d`.

The ordinary project runner checks that the exported project loads and that
the public declarations are well formed. Because project exports are trusted
for speed, the routine body gate also runs every exported section directly
with `-runner -f`; the optional flattened isolated gate is documented in
`scripts/linear_algebra_done_right/source_manifest.yaml`.

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
  eigenvalue, divisibility, invertibility, and parity results of Section 5B;
  and
- one-basis operator matrices, matrix diagonals, upper-triangular predicates,
  invariant prefix flags, diagonal products, and triangularization criteria;
  and
- diagonal matrices, diagonalizability, callable eigenspaces, square-free
  minimal-polynomial criteria, invariant restrictions, and Gershgorin disks;
  and
- operator and matrix commutation, invariant eigenspaces, common eigenvectors,
  simultaneous diagonal and upper-triangular forms, and the sum/product
  eigenvalue results for commuting complex operators; and
- real/complex inner-product scalar geometry, inner-product spaces, callable
  norms and one-vector orthogonal decompositions, orthogonality,
  Cauchy-Schwarz, triangle, Pythagorean, and parallelogram interfaces; and
- orthonormal lists and bases, coordinate/Parseval formulas, a finite
  Gram-Schmidt trace, orthonormal triangularization and Schur interfaces, and
  the uniquely selected Riesz representative; and
- orthogonal complements, pointwise-defined orthogonal projections,
  minimization, null-complement restrictions, pseudoinverses, and their exact
  algebraic and best-solution properties; and
- adjoints, conjugate transpose, self-adjoint and normal operators, and the
  source's null/range, norm, eigenvector, and commuting-part characterizations;
  and
- real and complex spectral-theorem interfaces through orthonormal
  diagonalizing and eigenvector bases, plus the checked calculations in
  Examples 7.30 and 7.33; and
- positive operators, square-root candidates, all six source
  characterizations, the unique positive-square-root interface and callable
  selected root, plus checked calculations from Examples 7.35, 7.37, and 7.41;
  and
- isometries, unitary operators and matrices, coordinate inner products and
  matrix-vector products, the source characterizations, exact QR and Cholesky
  factorization relations, and a checked source-length proof that every
  eigenvalue of a unitary operator has absolute value 1; and
- ordered singular values, operator and matrix SVD, operator norm, low-rank
  approximation, polar decomposition, and the book's geometric image and
  volume constructions; and
- complexification, generalized eigenspaces and multiplicities, nilpotent and
  Jordan-basis interfaces, and basis-independent operator trace; and
- bilinear, symmetric, alternating, and quadratic forms, finite multilinear
  forms, permutations and signs, the basis-free operator determinant, matrix
  determinant, and the determinant characteristic polynomial; and
- two-space and finite-family tensor products defined as multilinear
  functionals on duals, with pure tensors, dimension and basis formulas,
  tensor inner products, and both universal linearization directions.

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
finite-sum algebra behind operator-polynomial multiplicativity. Sections 7A
and 7C each keep one direct typed selector trust, for the adjoint and positive
square root respectively, because the verifier cannot yet instantiate these
subtype-valued parameterized selections in a real importing caller. Later
chapters also keep visible selection or structure-packaging trust for ordered
singular-value lists, generalized-eigenvalue data, operator trace,
bilinear/multilinear function spaces, determinant values, and dependent
tensor-product component and dual structures. The substantial spectral,
permutation, determinant, and universal-property arguments remain named
axioms rather than being disguised as checked proofs.

Result 7.54 has a checked source-length proof and is independently exercised
from an importing caller. Instantiating some coordinate matrix helpers from an
importing caller can still expose the existing cross-module template-binding
problem in `chap3b::scalar_finite_sum`; that verifier issue is recorded as
`kernel_problem` in the working todo.

`math_collections.md` records the intended mathematical interfaces and their
dependency order. Working plans, item records, verifier notes, and blockers
live only in `scripts/linear_algebra_done_right/`.
