# Linear Algebra over a Field

This standalone showcase now follows the conceptual order of *Linear Algebra
Done Right*:

- `Field<K>` packages scalar zero, one, addition, negation, multiplication,
  inversion, and the field laws;
- `VectorSpace<K,V>` owns one `Field<K>` value and packages vector zero,
  addition, scalar multiplication, and the vector-space laws;
- vector negation and subtraction are derived from unique additive inverses;
- linear maps, subspaces, kernels, and the zero subspace are carrier-generic;
- kernels of linear maps are subspaces; and
- a linear map is injective exactly when its kernel is the zero subspace.

Only after that abstract spine does the module construct `real_field`, the
real coordinate plane, and the x-axis projection. The projection is checked as
a linear endomorphism, its kernel contains `(0,7)`, and it is not injective.
Thus `cart(R,R)` is an example of the interfaces, not their definition.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/5_linear_algebra
```

The module contains no `trust` or local axiom. It intentionally stops before
bases, dimension, rank-nullity, matrices, and quotients. A direct `R`-as-a-
vector-space instance is also deferred: every required law verifies, but the
current verifier does not assemble the `K = V = R` nested structure value via
`struct_member`. The checked `R^2` instance avoids that representation boundary
without weakening the public generic interface; the failed probes remain in
the ignored proof journal.

`same_math_in_lean.lean` is a handwritten Prelude-only analogy with the same
generic field, vector-space, linear-map, subspace, kernel, and injectivity
semantics. It also constructs the coordinate plane and x-axis projection.
Run it with:

```sh
lean showcases/math_concepts_in_litex/5_linear_algebra/same_math_in_lean.lean
```
