# Linear Algebra Core

This independent first version implements a concrete Gate A over `R^2`:

- vector addition, scalar multiplication, subtraction, and coordinate
  projection;
- a reusable linear-map predicate and proof that projection is linear;
- general kernels and the `R^2` subspace criterion;
- preservation of zero and the theorem that kernels are subspaces;
- both directions of “a linear map is injective iff its kernel is the zero
  subspace”; and
- the projection kernel as a nontrivial subspace, with a checked proof that
  projection is not injective.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r scratch/math_concepts_in_litex/linear_algebra_core
```

The module has no `trust` or local axiom. It intentionally stops before a
generic real-vector-space structure, bases, dimension, and rank-nullity; those
belong to the guarded next gate.
