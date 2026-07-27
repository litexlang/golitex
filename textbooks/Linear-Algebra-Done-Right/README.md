# Linear Algebra Done Right

This published module is a source-ordered Litex formalization of Chapters 1
and 2 of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. It keeps
Sections 1A through 2C and intentionally stops before Section 3A. Standalone
exercises are omitted.

## Run entrypoint and namespaces

Run the published project with:

```sh
target/release/litex -compact -r textbooks/Linear-Algebra-Done-Right
```

`litex.config` exports six namespaces in source order:

```text
chap1a -> chap1b -> chap1c -> chap2a -> chap2b -> chap2c
```

Cross-section uses remain explicit, for example `chap2a::span`. An explicit
structure type on a binding selects that binding's default field view, so
`scalars &chap1a::ScalarSystem<s>` supports field notation such as
`scalars.add(a,b)`.

## Implemented mathematical surface

The published surface includes:

- the concrete `Complex` carrier and callable complex operations;
- the `ScalarSystem` and `VectorSpace` structures and their mathematical laws;
- finite coordinate lists, coordinate spaces, function spaces, subspaces,
  finite subspace sums, and direct sums;
- linear combinations, span, linear independence, bases, and dimension.

A representative application shape is:

<!-- litex:skip-test -->
```litex
have x, y finite_seq(R, 2) = [1, 2], [3, 4]
\chap1a::coordinate_add<R, chap1a::real_scalars, 2>(x, y)
    $in finite_seq(R, 2)
```

## Verification and trust boundary

This is a runnable proof-debt-bearing translation, not a completed foundation
for linear algebra. The remaining `axiom` and direct `trust` boundaries are
visible in the six exported section files. The largest open boundaries in
this published slice concern selected complex/vector structures, finite-list
recursion, exchange and deletion arguments, and basis existence or
basis-length results.

`math_collections.md` records the intended interfaces and their dependency
order. Working plans, item records, verifier notes, and blockers live in
`scripts/linear_algebra_done_right/`.
