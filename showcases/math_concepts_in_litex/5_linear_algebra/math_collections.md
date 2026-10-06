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
- `main2.lit` uses ordinary `prop` context predicates over explicitly supplied
  operations. It is an independent presentation of the same mathematical
  stopping line; it does not use the removed `setting` syntax or import the
  struct development as a context overlay.
- Both exported files are independently checked as well as checked through
  the configured module. Neither uses direct trust or axioms.

## Current context presentations

`main.lit` passes `field &Field<K>` and vector-space values indexed by that
field directly in theorem and proposition signatures. `main2.lit` instead
passes scalar and vector operations, with `FieldSetting`, `VectorSpaceSetting`,
and `LinearMapSetting` predicates stating their laws. Each file proves the
kernel/subspace and zero-kernel/injectivity results and has its own concrete
real-plane projection consumer.

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
  `is_linear_map` with explicit field, carriers, spaces and map parameters.
- **Carrier invariant:** `source` and `target` are already indexed by the same
  `field`; equality between two stored field projections is neither present
  nor needed.
- **Checked instance:** `projection_x_axis` on `real_plane`.

### Subspace

- **Ordinary meaning:** a subset containing vector zero and closed under
  addition and scalar multiplication.
- **Litex form:** `is_subspace` with explicit field, vector-space and subset parameters.
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
  -> explicit struct parameters                     [context]
  -> unique additive inverses                      [existence, uniqueness]
  -> vector_neg / vector_sub                       [selection, definition]
  -> cancellation and scalar-zero lemmas           [proof]

VectorSpace<K, field, V> + VectorSpace<K, field, W>
  -> explicit source/target parameters              [shared field index]
  -> is_linear_map                                 [judgment]
  -> is_linear_map premise                           [contextual assumption]
  -> maps preserve zero and negation               [proof]
  -> linear_kernel                                 [definition]
  -> kernel is a subspace                          [proof]
  -> injective iff kernel = zero_subspace          [proof]

builtin R
  -> real_field                                    [checked struct value]
  -> real_plane                                    [checked indexed struct value]
  -> projection_x_axis is linear                   [proof]
  -> independent predicate presentation             [comparison]
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
