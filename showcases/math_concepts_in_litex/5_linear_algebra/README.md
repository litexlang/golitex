# Linear Algebra over a Field

This standalone showcase follows the conceptual order of *Linear Algebra Done
Right* in two parallel presentations:

- `main.lit` uses first-class `Field<K>` and `VectorSpace<K,V>` structures;
- `main2.lit` uses `FieldSetting`, `VectorSpaceSetting`, and
  `LinearMapSetting` as ambient theorem contexts and contains no `struct`.

Both presentations begin with:

- `Field<K>` packages scalar zero, one, addition, negation, multiplication,
  inversion, and the field laws;
- `VectorSpace<K,V>` owns one `Field<K>` value and packages vector zero,
  addition, scalar multiplication, and the vector-space laws;
- vector negation and subtraction are derived from unique additive inverses;
- linear maps, subspaces, kernels, and the zero subspace are carrier-generic;
- kernels of linear maps are subspaces; and
- a linear map is injective exactly when its kernel is the zero subspace.

Only after that abstract spine does either presentation introduce real scalar
operations, the coordinate plane, and the x-axis projection. In `main2.lit`,
the projection is checked against the setting-derived linear-map judgment, its
kernel is obtained from the carrier-generic theorem, and `(0,7)` is exhibited
as a kernel element. Thus `cart(R,R)` is an instance of the interfaces, not
their definition.

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

The two Litex files make a deliberate modeling tradeoff visible. A `struct` is
a mathematical value that can be stored, returned, and projected. A `setting`
is a reusable binder-and-assumption prefix for theorem contexts; its operations
are used directly as `add_V(u,v)` and `smul_V(a,v)`. The paired
`VectorSpacesSetting` binds one field and two spaces because setting references
currently introduce fresh binders rather than reusing an outer field binder.

`same_math_in_lean.lean` is a handwritten Prelude-only analogy with the same
generic field, vector-space, linear-map, subspace, kernel, and injectivity
semantics. It also constructs the coordinate plane and x-axis projection.
Run it with:

```sh
lean showcases/math_concepts_in_litex/5_linear_algebra/same_math_in_lean.lean
```
