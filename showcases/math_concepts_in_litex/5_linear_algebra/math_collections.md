# Mathematical Design: Linear Algebra over a Field

## Purpose and scope

This showcase follows the conceptual order of *Linear Algebra Done Right*:
first a scalar field, then a vector space over that field, and only then
subspaces, linear maps, kernels, and concrete coordinate examples. The module
remains standalone; it does not import the repository's full LADR translation
or another showcase.

The checked first gate must preserve the former kernel-zero/injectivity
endpoint while replacing its `cart(R,R)`-specific public interfaces with
carrier-generic ones. `R`, `R^2`, and x-axis projection are
instances at the end of the reader path, not the definitions of linear
algebra.

## Modeling conventions

- A field and a vector space are first-class structures because later
  mathematics projects and applies their operations.
- A condition on supplied data, such as being a subspace or a linear map, is a
  `prop`.
- A constructed set, such as a kernel, is a set-valued `have` declaration
  inside a `template` because callers use it as a set.
- Vector negation is selected only after additive-inverse existence and
  uniqueness are proved. It is not an extra primitive vector-space field.
- The inverse operation of a field is total as a Litex function; the field law
  constrains it only on nonzero scalars.
- `trust`, `axiom`, and verifier acceptance are epistemic statuses, never
  substitutes for a mathematical concept.

## Parallel setting-first presentation

`main2.lit` supplies a second checked interface without changing the
first-class design of `main.lit`. Its central forms are:

- `FieldSetting`: one scalar carrier, its operations, and the field laws as an
  ambient binder prefix;
- `VectorSpaceSetting`: the field prefix plus one vector carrier and its laws;
- `VectorSpacesSetting`: one shared field plus source and target vector-space
  operations;
- `LinearMapSetting`: the two-space prefix plus a map and its preservation
  laws;
- ordinary props `is_field_in_setting`, `is_vector_space_in_setting`,
  `is_linear_map_in_setting`, and `is_subspace_in_setting` for judgments that
  concrete examples can assert.

A setting is not a competing kind of field or vector-space value. It cannot be
stored, returned, or projected; theorem bodies consume its operations directly
as `add_V(u,v)` and `smul_V(a,v)`. This makes it a good LADR-style presentation
when the goal is to state theorems in a fixed ambient algebra. The struct form
remains preferable when spaces themselves must be passed around as data.

The paired setting is intentional. Explicit setting references introduce fresh
binders, so two nested `VectorSpaceSetting` references cannot currently identify
their scalar field binders. `VectorSpacesSetting` binds one field once and then
checks both vector-space law predicates over it.

The setting-first dependency spine is:

```text
FieldSetting
  -> VectorSpaceSetting
  -> VectorSpacesSetting
  -> LinearMapSetting
  -> T(0) = 0
  -> setting_linear_kernel
  -> kernel is a subspace
  -> real plane and x-axis projection instance
```

## Core interface cards

### Field

- **Ordinary meaning:** a nonempty scalar carrier with distinct zero and one,
  commutative addition and multiplication, additive inverses, distributivity,
  and multiplicative inverses for nonzero elements.
- **Semantic role and Litex form:** `struct Field<K>` containing `zero`, `one`,
  `add`, `neg`, `mul`, and `inv`, together with the field laws.
- **Representative interface:** `field &Field<K>` followed by
  `field.add(a,b)` and `field.mul(a,b)`.
- **Nearest rejected form:** a lone `prop is_field(...)`. It can test supplied
  operations but cannot give later code a coherent value whose operations can
  be projected and applied.
- **Dependencies:** only the carrier `K`, functions on `K`, equality, and
  ordinary logic.
- **Downstream use:** every vector-space scalar law and every linear-map scalar
  law.
- **Checked-use target:** construct `real_field &Field<R>` and evaluate its
  projected operations as ordinary real arithmetic.

### Vector space over a field

- **Ordinary meaning:** a nonempty carrier `V` with vector zero, addition, and
  scalar multiplication by one selected `Field<K>`, satisfying the LADR
  vector-space axioms.
- **Semantic role and Litex form:** `struct VectorSpace<K,V>` containing the
  field object, vector zero, vector addition, and scalar multiplication.
- **Representative interface:** `space &VectorSpace<K,V>` followed by
  `space.add(u,v)` and `space.smul(a,v)`.
- **Nearest rejected form:** a real-only `RealVectorSpace<V>` or a predicate
  over anonymous operations. The former hides the scalar abstraction; the
  latter makes ordinary operation use awkward and incoherent.
- **Dependencies:** `Field<K>` by signature and the field operations by law.
- **Downstream use:** additive inverse selection, subspaces, linear maps,
  kernels, and all later finite-dimensional concepts.
- **Checked-use target:** construct
  `real_plane &VectorSpace<R,cart(R,R)>` over `real_field`. The mathematically
  valid `VectorSpace<R,R>` assembly is recorded as a verifier-gap probe rather
  than published through trust.

### Derived vector negation and subtraction

- **Ordinary meaning:** every vector has a unique additive inverse; subtraction
  is addition of that inverse.
- **Semantic role and Litex form:** an existence-and-uniqueness theorem,
  followed by template-scoped `have fn vector_neg by exist!` and formula-defined
  `have fn vector_sub`.
- **Nearest rejected form:** storing negation as an unexplained primitive field
  or choosing an inverse before uniqueness is established.
- **Dependencies:** vector-space additive laws by existence and uniqueness.
- **Downstream use:** cancellation, preservation of negation, and the reverse
  kernel-zero/injectivity argument.

### Linear map

- **Ordinary meaning:** a function between vector spaces over the same field
  that preserves vector addition and scalar multiplication.
- **Semantic role and Litex form:**
  `prop is_linear_map(K,V,W,source,target,T)`.
- **Representative interface:** the predicate requires
  `source.field = target.field` and the two preservation laws.
- **Nearest rejected form:** `is_linear_map_R2_to_R`; that concrete predicate
  mistakes one example for the mathematical concept.
- **Dependencies:** both vector-space structures by signature and their common
  field by law.
- **Downstream use:** zero preservation, kernels, composition, range, and
  finite-dimensional results.
- **Checked-use target:** prove the x-axis projection endomorphism linear only
  after constructing the real plane as a vector space.

### Subspace

- **Ordinary meaning:** a subset containing vector zero and closed under vector
  addition and scalar multiplication.
- **Semantic role and Litex form:**
  `prop is_subspace(K,V,space,U)` on a supplied subset `U`.
- **Nearest rejected form:** only a packaged subspace structure. Kernel proofs
  naturally establish a property of an already supplied set.
- **Dependencies:** `VectorSpace<K,V>` by signature and law.
- **Downstream use:** kernels now; induced spaces, ranges, sums, and quotients
  later.

### Kernel and zero subspace

- **Ordinary meaning:** the kernel consists of vectors sent to target zero;
  the zero subspace contains exactly source zero.
- **Semantic role and Litex form:** template-scoped set-valued constructions
  `linear_kernel` and `zero_subspace`.
- **Nearest rejected form:** membership predicates only. The flagship theorem
  compares the two sets by equality.
- **Dependencies:** the function and target zero by definition; the source
  zero for the zero subspace.
- **Downstream use:** kernel-is-subspace and injective iff zero kernel.

### Basis, coordinates, and dimension (later gate)

- **Ordinary meaning:** a basis is independent and spanning; coordinates are
  uniquely determined relative to a basis; dimension is the common length of
  finite bases.
- **Ideal forms:** basis and candidate-coordinate relations as `prop`, the
  coordinate map as `have fn ... by exist!`, and dimension as a selected
  natural only after basis-length uniqueness.
- **Nearest rejected forms:** arbitrary basis choice, nonunique coordinate
  selection, or an axiom-valued dimension function.
- **Dependencies:** finite sequences, finite sums, basis existence/extension,
  and basis-length uniqueness.
- **Boundary:** none of these interfaces is part of the current checked gate.

## Typed dependency DAG

Edge legend: `signature` names a carrier or structure in an interface;
`law` consumes structure laws; `definition` unfolds a construction;
`existence`, `uniqueness`, and `selection` expose canonical vector negation;
`proof` cites a prior mathematical result.

```text
K nonempty_set
  -> Field<K>                                      [signature, law]
  -> VectorSpace<K,V> / VectorSpace<K,W>           [signature, law]
  -> additive inverse exists uniquely              [existence, uniqueness]
  -> vector_neg / vector_sub                       [selection, definition]
  -> cancellation and scalar-zero lemmas           [proof]

VectorSpace<K,V> + VectorSpace<K,W>
  -> is_linear_map                                 [signature, law]
  -> linear maps preserve zero and negation        [proof]
  -> linear_kernel                                 [definition]
  -> kernel is a subspace                          [proof]
  -> injective iff kernel = zero_subspace          [proof]

builtin R
  -> real_field                                    [law]
  -> real_plane                                    [law]
  -> projection_x_axis is linear                   [proof]
  -> projection kernel is nontrivial               [definition, proof]
  -> projection_x_axis is not injective            [proof]

finite sequences + finite sums
  -> span / independence / basis                   [definition]
  -> coordinate existence and uniqueness           [existence, uniqueness]
  -> coordinate map                                [selection]
  -> basis-length uniqueness -> dimension          [proof, selection]
  -> rank-nullity and matrices                      [proof, definition]
```

The graph is acyclic. In particular, vector negation follows unique additive
inverses, kernels follow linear maps, and dimension follows basis-length
uniqueness rather than defining it.

## Source-aware implementation order

1. Define `Field<K>` and its direct field-operation use surface.
2. Define `VectorSpace<K,V>` with one owned field value.
3. Prove unique additive inverses, select vector negation, and prove
   cancellation and zero-scalar lemmas.
4. Define abstract linear maps, subspaces, kernels, and the zero subspace.
5. Prove zero preservation, kernel closure, and both injectivity directions.
6. Construct `real_field` and `R^2` as checked instances.
7. Reintroduce x-axis projection only as a consumer of the abstract
   interfaces. Keep the direct `R` vector-space assembly probe in the journal
   until the nested `K = V` structure-membership gap is resolved.

This deliberately departs from the former coordinate-first file order. The
departure is required by the confirmed reader promise: concrete coordinates
must illustrate the abstract definitions rather than define them.

## Verification and trust boundary

The current gate is accepted only when the registered release file and module
runners report top-level `ok: true`, the published Litex source contains no
direct `trust` or local `axiom`, and the concrete projection consumes the
generic interfaces. Builtin arithmetic and logic remain part of Litex's
ordinary verifier boundary; no kernel behavior is changed by this showcase.
