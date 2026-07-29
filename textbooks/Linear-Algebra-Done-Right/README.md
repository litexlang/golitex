# Linear Algebra Done Right

This draft module is a source-ordered Litex formalization of Chapters 1
through 5 of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. It
keeps Sections 1A through 5E. Standalone exercises are omitted.

## Run entrypoint and namespaces

Run the draft project with:

```sh
target/release/litex -compact -r scripts/textbooks_drafts/Linear-Algebra-Done-Right
```

`litex.config` exports the chapter namespaces in source order:

```text
chap1a -> ... -> chap3f -> chap4 -> chap5a -> ... -> chap5e
```

Cross-section uses remain explicit, for example `chap2a::span`. An explicit
structure type on a binding selects that binding's default field view, so
`scalars &chap1a::ScalarSystem<s>` supports field notation such as
`scalars.add(a,b)`. Generic vector-space interfaces name the carrier
`VSet` and the corresponding `VectorSpace` structure `V`, keeping later
expressions concise as `V.add(u,v)` and `V.smul(a,u)`.

## Implemented mathematical surface

The implemented draft surface includes:

- the concrete `Complex` pair carrier, with `real_coord` and `im` fields, and
  callable complex operations;
- the `ScalarSystem` and `VectorSpace` structures and their mathematical laws;
- finite coordinate lists, coordinate spaces, function spaces, subspaces,
  finite subspace sums, and direct sums;
- linear combinations, span, linear independence, bases, and dimension.
- linear maps and their pointwise operations, null spaces, ranges,
  rank-nullity statements, matrices, invertibility, products, quotients, and
  duality;
- complex conjugation and absolute value, polynomial evaluation, degree,
  division, zeros, and complex and real factorization statements;
- operators, eigenvalues and eigenvectors, minimal polynomials, invariant
  subspaces, triangularization, diagonalization, Gershgorin disks, and
  commuting-operator statements.

A representative application shape is:

<!-- litex:skip-test -->
```litex
have x, y finite_seq(R, 2) = [1, 2], [3, 4]
\chap1a::coordinate_add<R, chap1a::real_scalars, 2>(x, y)
    $in finite_seq(R, 2)
```

## Verification and trust boundary

This is a runnable proof-debt-bearing translation, not a fully proved
formalization. Remaining `axiom`, direct `trust`, and localized
`abstract_prop` boundaries are visible in the exported section files. The
largest open boundaries concern selected algebraic structures, finite-list
recursion, basis and dimension infrastructure, matrix-coordinate
constructions, polynomial factorization, and the operator decomposition
theorems.

`math_collections.md` records the intended interfaces and their dependency
order. Working plans, item records, verifier notes, and blockers live in
`scripts/linear_algebra_done_right/`.
