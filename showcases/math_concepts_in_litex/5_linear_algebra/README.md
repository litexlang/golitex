# Linear Algebra over a Field

This standalone showcase follows the conceptual order of *Linear Algebra Done
Right*: a scalar field, vector spaces over that field, linear maps, subspaces,
kernels, and finally concrete coordinate examples.

The module exports two checked presentations:

- `main.lit` defines the first-class structures, propositions, constructions,
  proofs, and concrete values;
- `main2.lit` develops an independent predicate presentation, passing scalar
  and vector operations explicitly and naming their laws with `prop` definitions.

`Field<K>` packages scalar operations and their laws. A vector-space object has
the carrier

```text
&VectorSpace<K, field, V>
```

so the concrete `field &Field<K>` is fixed when the object is declared. The
vector-space record itself therefore needs only `zero`, `add`, and `smul`.
Two spaces used by one linear map carry the same `field` in their types; no
later `source.field = target.field` compatibility premise is required.

In `main2.lit`, `FieldSetting`, `VectorSpaceSetting`, and
`LinearMapSetting` are ordinary predicates over supplied operations and laws.
They use current `prop` syntax. The removed `setting` keyword and the explicitly quantified carriers, operations, and context-predicate premises
binder notation are not executable interfaces in this release.

The checked development derives vector negation and subtraction, proves that
linear maps preserve zero and negation, proves that kernels are subspaces, and
establishes the trivial-kernel criterion for injectivity. Only then does it
construct `real_field`, the coordinate plane `real_plane`, and projection onto
the x-axis. `main2.lit` constructs its own named real operations, coordinate-plane operations, and projection.

Run the registered module from the repository root with:

```bash
target/release/litex -strict -r showcases/math_concepts_in_litex/5_linear_algebra
```

The published Litex source contains no direct `trust` or local `axiom`. The
module intentionally stops before bases, dimension, rank-nullity, matrices,
and quotients. `LinearMap` and `Subspace` also remain propositions in this
gate; they have not been promoted to structures.

That stop is the collection's completion boundary for linear algebra: the
field/space setting, linear-map relation, kernel construction, consuming
kernel theorems, and concrete real-plane projection already form one complete
vertical slice. More chapters are optional extensions, not prerequisites for
calling this showcase finished.

`same_math_in_lean.lean` is a handwritten Prelude-only comparison covering the
same generic field, vector-space, linear-map, subspace, kernel, injectivity, and
coordinate-plane mathematics. Run it separately with:

```sh
lean showcases/math_concepts_in_litex/5_linear_algebra/same_math_in_lean.lean
```
