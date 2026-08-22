# Linear Algebra over a Field

This standalone showcase follows the conceptual order of *Linear Algebra Done
Right*: a scalar field, vector spaces over that field, linear maps, subspaces,
kernels, and finally concrete coordinate examples.

The two Litex exports now share one mathematical ontology:

- `main.lit` defines the first-class structures, propositions, constructions,
  proofs, and concrete values;
- `main2.lit` adds a small Setting-facing layer over those same values. It does
  not flatten operations or rebuild the mathematics a second time.

`Field<K>` packages scalar operations and their laws. A vector-space object has
the carrier

```litex
&VectorSpace<K, field, V>
```

so the concrete `field &Field<K>` is fixed when the object is declared. The
vector-space record itself therefore needs only `zero`, `add`, and `smul`.
Two spaces used by one linear map carry the same `field` in their types; no
later `source.field = target.field` compatibility premise is required.

Settings name recurring theorem contexts without creating another kind of
field or vector space:

```litex
setting VectorSpaceSetting(
    [FieldSetting(K, field)],
    V nonempty_set,
    space &VectorSpace<K, field, V>
)
```

Inside such a context, `field.mul`, `space.zero`, `space.add`, and `space.smul`
come from the struct types attached to those binders. Mere later membership of
an unrelated symbol in a struct carrier does not install a second field view on
that symbol.

The checked development derives vector negation and subtraction, proves that
linear maps preserve zero and negation, proves that kernels are subspaces, and
establishes the trivial-kernel criterion for injectivity. Only then does it
construct `real_field`, the coordinate plane `real_plane`, and projection onto
the x-axis. `main2.lit` reuses those concrete values through its Settings.

Run the registered module from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/5_linear_algebra -summarize
```

The published Litex source contains no direct `trust` or local `axiom`. The
module intentionally stops before bases, dimension, rank-nullity, matrices,
and quotients. `LinearMap` and `Subspace` also remain propositions in this
gate; they have not been promoted to structures.

`same_math_in_lean.lean` is a handwritten Prelude-only comparison covering the
same generic field, vector-space, linear-map, subspace, kernel, injectivity, and
coordinate-plane mathematics. Run it separately with:

```sh
lean showcases/math_concepts_in_litex/5_linear_algebra/same_math_in_lean.lean
```
