# Historical design record

This record describes an earlier struct-backed `setting` design. The current
release has removed that syntax; see README.md and math_collections.md for the
actual two exported presentations. Its snippets are historical excerpts.

# Struct-backed Setting acceptance

## Reader-visible contract

This migration keeps `Field` and `VectorSpace` as first-class structures while
making the scalar field a header index of each vector-space object. `Setting`
is only a reusable binder-and-assumption layer over those objects.

The executable sources are [main.lit](main.lit) and [main2.lit](main2.lit).

## Before

The former showcase had two independent presentations. Its Setting branch
flattened every operation and repeated the algebraic laws, while its struct
branch stored the field again inside each vector-space record. The following
is historical design evidence, not current executable Litex:

```text
# struct VectorSpace<K nonempty_set, V nonempty_set>:
#     field &Field<K>
#     zero V
#     add fn(x, y V) V
#     smul fn(a K, x V) V
#
# setting VectorSpaceSetting(
#     [FieldSetting(K, scalar_zero, scalar_one, scalar_add, scalar_neg, scalar_mul, scalar_inv)],
#     V nonempty_set,
#     zero_V V,
#     add_V fn(x, y V) V,
#     smul_V fn(a K, x V) V
# ):
#     $has_vector_space_laws(K, V, scalar_one, scalar_add, scalar_mul, zero_V, add_V, smul_V)
```

Consequences of that shape were duplicated laws, long theorem signatures,
raw calls such as `add_V(u,v)`, and an extra source/target field-compatibility
obligation for linear maps.

## Now

The scalar field is fixed in the struct carrier itself, and Settings bind the
resulting declaration-typed values:

```text
struct VectorSpace<K nonempty_set, field &Field<K>, V nonempty_set>:
    zero V
    add fn(x, y V) V
    smul fn(a K, x V) V
    <=>:
        forall x, y, z V:
            add(add(x, y), z) = add(x, add(y, z))
        forall x, y V:
            add(x, y) = add(y, x)
        forall x V:
            add(zero, x) = x
            exist y V st {add(x, y) = zero}
        forall a, b K, x V:
            smul(field.mul(a, b), x) = smul(a, smul(b, x))
            smul(field.add(a, b), x) = add(smul(a, x), smul(b, x))
        forall a K, x, y V:
            smul(a, add(x, y)) = add(smul(a, x), smul(a, y))
        forall x V:
            smul(field.one, x) = x

setting FieldSetting(K nonempty_set, field &Field<K>)

setting VectorSpaceSetting(
    [FieldSetting(K, field)],
    V nonempty_set,
    space &VectorSpace<K, field, V>
)

setting VectorSpacesSetting(
    [FieldSetting(K, field)],
    V, W nonempty_set,
    source &VectorSpace<K, field, V>,
    target &VectorSpace<K, field, W>
)

setting LinearMapSetting([VectorSpacesSetting], T fn(v V) W):
    $is_linear_map(K, field, V, W, source, target, T)
```

The Setting-facing tracer in `main2.lit` exercises the complete route from a
Setting expansion to struct fields and an existing theorem:

```text
thm setting_linear_map_sends_zero_to_zero:
    ? forall [LinearMapSetting]:
        T(source.zero) = target.zero
    by thm main::linear_map_sends_zero_to_zero(K, field, V, W, source, target, T) => T(source.zero) = target.zero
```

The concrete `real_projection_uses_setting` theorem then instantiates the same
route with `main::real_field`, `main::real_plane`, and
`main::projection_x_axis`; no second concrete model is built.

## Semantic boundary

- `&VectorSpace<K, field, V>` is a set once `K`, `field`, and `V` are fixed.
- A symbol declared with that carrier owns the `VectorSpace` fields selected at
  declaration time.
- Proving later that some differently declared symbol belongs to another
  struct carrier does not install that other carrier's fields on the symbol.
- `field` is a struct header index, so there is intentionally no
  `space.field`, `source.field`, or `target.field` projection.
- `is_linear_map` and `is_subspace` remain propositions in this migration.
- The Setting layer does not duplicate struct laws or introduce raw operation
  binders.

## Verification gates

Run from the repository root:

```bash
target/release/litex -compact -summarize -f showcases/math_concepts_in_litex/5_linear_algebra/main.lit
target/release/litex -compact -summarize -f showcases/math_concepts_in_litex/5_linear_algebra/main2.lit
target/release/litex -compact -summarize -r showcases/math_concepts_in_litex/5_linear_algebra
```

Acceptance requires exit status zero and a final run-summary object for all
three commands, plus no newly introduced direct `trust` or local `axiom` in
the published Litex files.

Recorded on 2026-08-21: all three commands exited zero and reported top-level
`ok: true`. The directory gate verified `main` and `main2` together.

The existing `target/release/litex` binary was used for these gates. Rebuilding
that binary from the current dirty checkout was separately attempted but is
blocked by an unrelated non-exhaustive `BuiltinRuleEvidence` match in
`src/stmt_result_to_lean_compiler/stmt_result_to_lean_compiler.rs`; this
showcase migration does not modify that subsystem.
