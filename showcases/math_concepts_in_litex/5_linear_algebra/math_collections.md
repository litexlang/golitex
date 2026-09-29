# Mathematical Design: Linear Algebra over a Field

## Purpose and scope

This showcase follows the conceptual order of *Linear Algebra Done Right*:
first a scalar field, then vector spaces indexed by that field, and only then
linear maps, subspaces, kernels, and concrete coordinates. The public generic
interfaces do not depend on `R` or `cart(R,R)`.

The current gate covers unique additive inverses, derived vector negation and
subtraction, zero and negation preservation by linear maps, kernels as
subspaces, the trivial-kernel criterion for injectivity, and the real-plane
projection example. Bases, dimension, matrices, quotients, and rank-nullity
remain later work.

## Modeling decisions

- `Field<K>` is a first-class `struct` because scalar operations are coherent
  data that later objects must retain, pass, and project.
- `VectorSpace<K, field, V>` is a first-class `struct` family indexed by one
  concrete `field &Field<K>`. With `K`, `field`, and `V` fixed,
  `&VectorSpace<K, field, V>` is the carrier set of those vector-space objects.
- A `VectorSpace` value stores only `zero`, `add`, and `smul`; its scalar field
  is already fixed by the struct header and is not duplicated as a record
  field.
- `is_linear_map` and `is_subspace` are `prop`s: they are judgments on already
  supplied functions, subsets, and struct values. This gate does not introduce
  `LinearMap` or `Subspace` structs.
- `linear_kernel` and `zero_subspace` are set-valued `have` declarations in
  templates because callers use the resulting sets as mathematical objects.
- Vector negation is selected by `have fn ... by exist!` only after existence
  and uniqueness are proved. It is not stored as an unexplained vector-space
  field.
- `Setting` names recurring binders and assumptions. It does not define a
  second field/vector-space ontology and does not repeat laws already supplied
  by struct membership.
- `trust`, `axiom`, and verifier acceptance are epistemic statuses, not forms
  for mathematical concepts.

## Struct-backed Setting layer

The core context spine in `main.lit` is:

```litex
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
```

These binders retain the declaration-owned views of `field`, `space`,
`source`, and `target`, so theorem bodies use `field.mul`, `space.add`,
`source.smul`, and `target.zero`. The shared field index in both vector-space
carriers expresses scalar compatibility before a linear-map proposition is
stated; there is no `source.field = target.field` premise to transport later.

`LinearMapSetting` adds exactly one contextual assumption:

```litex
setting LinearMapSetting([VectorSpacesSetting], T fn(v V) W):
    $is_linear_map(K, field, V, W, source, target, T)
```

`main2.lit` is deliberately a small consumer-facing overlay over the exported
`main::Field`, `main::VectorSpace`, propositions, templates, and theorems. It
does not redeclare raw scalar/vector operations, field laws, the real field,
the real plane, or the projection proof. Its tracer theorem demonstrates that
the Setting expands to the correct declaration-typed objects:

```litex
thm setting_linear_map_sends_zero_to_zero:
    ? forall [LinearMapSetting]:
        T(source.zero) = target.zero
```

This separation is intentional:

- a struct value can be stored, returned, passed to another theorem, and used
  through its declaration-owned fields;
- a Setting is a reusable theorem-context prefix over such values;
- later membership of an untyped symbol in a struct carrier does not give that
  symbol another declaration-owned field view.

## Core interface cards

### Field

- **Ordinary meaning:** a nonempty scalar carrier with zero, one, commutative
  addition and multiplication, additive inverses, distributivity, and
  multiplicative inverses for nonzero scalars.
- **Litex form:** `struct Field<K>` with `zero`, `one`, `add`, `neg`, `mul`,
  `inv`, and their laws.
- **Representative use:** `field &Field<K>`, followed by `field.add(a,b)` and
  `field.mul(a,b)`.
- **Rejected nearby form:** only a predicate over anonymous operations. Such a
  predicate can judge supplied data but cannot supply a coherent value whose
  operations are later projected.
- **Checked instance:** `real_field &Field<R>`.

### Vector space over one concrete field

- **Ordinary meaning:** a nonempty carrier `V` with vector zero, addition, and
  scalar multiplication by one selected field.
- **Litex form:**
  `struct VectorSpace<K, field &Field<K>, V>` with `zero`, `add`, `smul`, and
  the vector-space laws.
- **Representative use:** `space &VectorSpace<K, field, V>`, followed by
  `space.add(u,v)` and `space.smul(a,v)`.
- **Rejected nearby forms:** a real-only `RealVectorSpace<V>`; a raw predicate
  that flattens every operation into every theorem; or a record field that
  duplicates the already-fixed `field` index.
- **Checked instance:**
  `real_plane &VectorSpace<R, real_field, cart(R,R)>`.

### Derived vector negation and subtraction

- **Ordinary meaning:** every vector has a unique additive inverse;
  subtraction adds that inverse.
- **Litex form:** an existence-and-uniqueness theorem, then template-scoped
  `have fn vector_neg by exist!` and formula-defined `have fn vector_sub`.
- **Dependencies:** the additive laws of the indexed vector-space object.
- **Downstream use:** cancellation, zero-scalar lemmas, preservation of
  negation, and the reverse kernel-zero/injectivity argument.

### Linear map

- **Ordinary meaning:** a function between two vector spaces over the same
  scalar field that preserves addition and scalar multiplication.
- **Litex form:**
  `prop is_linear_map([VectorSpacesSetting], T fn(v V) W)`.
- **Carrier invariant:** `source` and `target` are already indexed by the same
  `field`; equality between two stored field projections is neither present
  nor needed.
- **Checked instance:** `projection_x_axis` on `real_plane`.

### Subspace

- **Ordinary meaning:** a subset containing vector zero and closed under
  addition and scalar multiplication.
- **Litex form:** `prop is_subspace([VectorSpaceSetting], U power_set(V))`.
- **Reason it remains a prop:** kernel proofs establish a property of a set
  already supplied or constructed; they do not yet need a packaged subspace
  value with additional data.

### Kernel and zero subspace

- **Ordinary meaning:** the kernel contains vectors sent to target zero; the
  zero subspace contains exactly source zero.
- **Litex form:** template-scoped set constructions `linear_kernel` and
  `zero_subspace`.
- **Downstream use:** kernel-is-subspace and injective iff zero kernel.

## Typed dependency DAG

Edge labels describe why the dependency is present.

```text
K nonempty_set
  -> Field<K>                                      [signature, laws]
  -> VectorSpace<K, field, V/W>                    [field index, laws]
  -> FieldSetting / VectorSpaceSetting             [context]
  -> unique additive inverses                      [existence, uniqueness]
  -> vector_neg / vector_sub                       [selection, definition]
  -> cancellation and scalar-zero lemmas           [proof]

VectorSpace<K, field, V> + VectorSpace<K, field, W>
  -> VectorSpacesSetting                           [shared field index]
  -> is_linear_map                                 [judgment]
  -> LinearMapSetting                              [contextual assumption]
  -> maps preserve zero and negation               [proof]
  -> linear_kernel                                 [definition]
  -> kernel is a subspace                          [proof]
  -> injective iff kernel = zero_subspace          [proof]

builtin R
  -> real_field                                    [checked struct value]
  -> real_plane                                    [checked indexed struct value]
  -> projection_x_axis is linear                   [proof]
  -> concrete Setting tracer                       [reuse]
```

The graph is acyclic. In particular, vector negation follows uniqueness,
kernels follow the linear-map judgment, and concrete coordinates consume the
generic interfaces rather than defining them.

## Source-aware implementation order

1. Define `Field<K>`.
2. Define `VectorSpace<K, field, V>` with `field` in the struct header.
3. Add struct-backed Settings for one field, one space, two spaces, and a
   linear map assumption.
4. Derive vector negation, subtraction, cancellation, and scalar-zero facts.
5. Define linear-map and subspace judgments plus kernel constructions.
6. Prove zero preservation, kernel closure, and both injectivity directions.
7. Construct `real_field`, `real_plane`, and the x-axis projection.
8. Reuse the exported ontology through the small `main2.lit` Setting overlay.

## Verification and trust boundary

Acceptance requires the release Litex runner to report top-level `success: true`
for `main.lit`, `main2.lit`, and the registered module directory. The published
Litex files must add no direct `trust` or local `axiom`. Builtin arithmetic,
logic, and registered prior-module imports remain inside Litex's ordinary
verifier boundary; this showcase changes no kernel rule.
