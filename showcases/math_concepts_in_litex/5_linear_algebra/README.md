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
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/5_linear_algebra
```

The module has no `trust` or local axiom. It intentionally stops before a
generic real-vector-space structure, bases, dimension, and rank-nullity; those
belong to the guarded next gate.

`same_math_in_lean.lean` builds the small scalar, linear-map,
subspace, and kernel interfaces directly over Prelude products. It proves that
a kernel is a subspace, the injective-to-trivial-kernel direction, and the
noninjectivity of coordinate projection. It has no imports and is a handwritten
formulation of the same mathematics, not compiler-generated output. Run it with:

```sh
lean showcases/math_concepts_in_litex/5_linear_algebra/same_math_in_lean.lean
```
