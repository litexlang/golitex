# Plan: Linear Algebra Core

## Reader promise

This file should connect familiar coordinate calculations to a reusable
abstract interface. A reader first sees a concrete map on `R^n`, then sees why
the same facts follow from vector-space and linear-map laws. It is the
collection's abstraction showcase, but it deliberately avoids the full
generality and breadth of a mature linear-algebra library.

## Foundational decision

The first stable interface uses real vector spaces. Arbitrary scalar systems,
fields, and modules remain important research/library work, but forcing them
into the first public path would make every definition longer and obscure the
reader-facing theorem chain.

The eventual file has two gates:

- **Gate A -- structural core:** real vector spaces, subspaces, linear maps,
  kernels/ranges, and injectivity iff zero kernel. This gate must be independently
  coherent and zero-trust.
- **Gate B -- finite-dimensional core:** finite linear combinations, span,
  independence, basis coordinates, dimension, rank-nullity, and matrix
  representation. Gate B enters only when finite-list/sum and basis-selection
  interfaces are explicit and the whole chain can remain honest.

Failure of Gate B must not weaken or block publication of Gate A, and must not
be hidden by a broad rank-nullity axiom.

## Mathematical boundary

Included in Gate A:

- concrete coordinate spaces `R^n` as motivating examples;
- a packaged real vector-space structure with zero, addition, scalar
  multiplication, and laws;
- subspace predicate and induced subspace structure;
- linear-map predicate/space, identity, zero map, and composition;
- linear maps preserve zero and additive inverse;
- kernel and range as set-valued constructions;
- kernel/range are subspaces; and
- a linear map is injective iff its kernel is `{0}`.

Included in Gate B, conditionally:

- finite lists/sequences and finite sums as dependencies, not reinventions;
- linear combinations, span, linear independence, basis;
- existence and uniqueness of coordinates relative to a basis;
- finite-dimensionality and dimension as a selected basis length only after
  basis-length uniqueness;
- rank-nullity;
- matrices of linear maps relative to chosen bases; and
- composition corresponds to matrix multiplication.

Explicitly excluded:

- inner products, norms, orthogonality, Gram-Schmidt, least squares, adjoints,
  spectral theory, eigenvalues, determinants as a general theory, quotient
  spaces, duality, tensor products, and SVD;
- arbitrary rings/modules or simultaneous `R`/`C`/generic-field abstraction in
  the first public spine;
- infinite-dimensional topological questions;
- assuming basis existence or rank-nullity merely to complete the story; and
- textbook-section completeness.

Least squares is an external future consumer, not part of this file: it should
combine this core with a later inner-product/calculus project.

## Internal architecture

1. **Concrete preview**: vector operations and a projection on `R^2`.
2. **Real vector-space laws**: structure and elementary derived identities.
3. **Subspaces**: predicate, carrier, and induced operations.
4. **Linear maps**: property, callable space, identity/zero/composition.
5. **Kernel and range**: set-valued constructions and subspace theorems.
6. **Structural flagship**: injective iff kernel is zero.
7. **Finite infrastructure**: finite combinations, span, independence.
8. **Coordinates and dimension**: basis coordinate unique existence, then
   selected coordinate function and basis-length-independent dimension.
9. **Finite-dimensional flagship**: rank-nullity.
10. **Concrete consumer**: calculate kernel/range/rank/nullity for one map
    `R^3 -> R^2` and connect it to its matrix.

## Main theorem chain

Gate A:

```text
real vector-space laws
  -> vector zero/negative/cancellation lemmas
  -> subspace and induced vector space
  -> linear-map laws and composition
  -> linear maps preserve zero and negatives
  -> kernel and range constructions
  -> kernel/range are subspaces
  -> injective iff kernel = {0}
```

Gate B:

```text
finite sequences and finite sums
  -> linear combination
  -> span and linear independence
  -> basis
  -> coordinate existence + uniqueness
  -> callable coordinate map
  -> basis-length uniqueness
  -> dimension
  -> kernel-basis extension / range basis
  -> rank-nullity
  -> matrix representation
  -> matrix(composition) = matrix multiplication
```

The key acyclicity rule is that `dimension` cannot define the basis interface
that is later used to prove basis lengths equal. Define basis independently,
prove basis-length uniqueness, and only then select dimension.

## Scratch example ladder

1. First-coordinate projection `R^2 -> R` and its y-axis kernel -- current
   tracer; concrete, readable, and sufficient to motivate every Gate A concept.
2. Identity and zero maps in an abstract real vector space.
3. Sum-zero cancellation proves that a linear map preserves zero.
4. Projection revisited through the abstract linear-map interface.
5. General injective iff zero-kernel theorem -- Gate A flagship.
6. A chosen basis of `R^2` gives unique coordinates -- Gate B interface probe.
7. `T(x,y,z) = (x+y, y+z)`: exhibit kernel generator `(-1,1,-1)`, show full
   range, and derive nullity `1`, rank `2`, dimension `3` -- public
   finite-dimensional flagship.
8. Compute the matrix of `T` and check one composed-map/matrix product.

## Modeling decisions

- the vector-space data and laws are a `struct` because downstream theorems
  pass the package and project zero/add/smul fields.
- `is_subspace` and `is_linear_map` are `prop` relations testing supplied data.
- `kernel(T)` and `range(T)` are set-valued functions because downstream
  statements compare them, take dimensions, and build subspace structures.
- basis is a relation on finite vector data; coordinate values become a
  `have fn ... by exist!` only after coordinate existence and uniqueness.
- dimension is a canonical natural only after all bases have the same length.
  A trusted choice of a basis length is not an acceptable definition.

## Lean comparison scene

Use the theorem `injective T iff kernel T = {0}` for the same real vector-space
assumptions, followed by the concrete projection. Lean should be shown with
its idiomatic `LinearMap` and kernel API; Litex should show the fact-oriented
path from linearity and vector cancellation. Disclose that mathlib's theorem
is vastly more general and integrated. The useful contrast is how the user
interacts with the proof, not theorem novelty or library breadth.

## Acceptance gates

Gate A:

- independent release-runner success with no direct `trust`;
- one concrete coordinate map is constructed and consumed through the
  abstract interface;
- kernel and range are actual sets and verified subspaces;
- both directions of injective iff zero-kernel are proved;
- real-scalar restriction is explicit everywhere.

Gate B:

- every finite-sum/list dependency is checked and reusable;
- basis coordinates have proved existence and uniqueness before selection;
- dimension does not depend on an unproved arbitrary basis choice;
- rank-nullity is a theorem, not a kernel rule, axiom, or broad trust;
- the `R^3 -> R^2` flagship consumes the general interfaces; and
- matrix representation is basis-relative and composition uses compatible
  chosen bases.

## Expected downstream consumers

Euclidean geometry can later consume concrete vector/dot interfaces; least
squares can consume finite-dimensional range, kernel, matrices, and eventually
inner products. Repeated, stable set/function interfaces may then move to
`std`, but no scratch-to-scratch import is required for initial development.
