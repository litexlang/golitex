# Linear Algebra in Litex

These lecture notes develop selected ideas from Sheldon Axler's *Linear Algebra
Done Right*, using the real plane as a running example. They show how familiar
calculations lead to definitions, how concrete objects satisfy those definitions,
and how the resulting facts support further mathematics.

The shared field, vector-space, subspace, linear-map, finite-combination and
span, independence and basis interfaces come from
[std/algebra](../../std/algebra/README.md). This lecture retains the concrete
instances and the concrete coordinate developments. Its checkout-local
manifest imports `Algebra`, using explicit `Algebra::field` and
`Algebra::vector_space`, `Algebra::finite_span` and `Algebra::basis` paths.

Read [linear_algebra.lit](linear_algebra.lit) from beginning to end. The notes
move from coordinate operations to vector spaces and subspaces, then through
linear combinations, bases and unique coordinates, finite combination algebra
and span as a subspace, linear maps with kernels and ranges, and finally to
dependence lemmas, a concrete rank-nullity picture for projection, eigenvalues
of that projection, and the Euclidean inner product on the plane.

## From coordinates to vector spaces

We begin with the two standard directions in the real plane:

<!-- litex:skip-test -->
```litex
have e1 R × R = (1, 0)
have e2 R × R = (0, 1)
have standard_basis finite_seq(R × R, 2) = (e1, e2)

standard_basis(1) = (1, 0)
standard_basis(2) = (0, 1)
```

These lines are drawn from two places in the notes. We write the real plane
$\mathbb{R}^2 = \mathbb{R} \times \mathbb{R}$ as `R × R` in Litex,
equivalently `cart(R, R)`.
This is the same set as `finite_seq(R, 2)`: its elements are ordered pairs of
real numbers, with coordinates accessed as `v(1)` and `v(2)`.
A list of vectors has type `finite_seq(R × R, n)`, allowing repeated
directions and an empty list.

Coordinate addition and scalar multiplication suggest the vector space axioms.
The notes construct the real field and the real plane as instances of `Field`
and `VectorSpace`, checking their laws. Shared source theorems establish
uniqueness of additive identities and inverses. The coordinate axes then provide examples of subspaces.
A translated line provides a counterexample, and the two axes give a unique
decomposition of every plane vector.

## From directions to unique coordinates

The span of a list contains all vectors obtained by taking linear combinations
of its entries. Once the linear combination relation has been defined, this
mathematical description becomes a set definition:

<!-- litex:skip-test -->
```litex
# Shared definition in std/algebra/finite_span.lit:
template<K nonempty_set, field &field::Field<K>, V nonempty_set, space &vector_space::VectorSpace<K, field, V>, n N, vectors finite_seq(V, n)>:
    have span power_set(V) = {x V: $is_linear_combination(K, field, V, space, n, x, vectors)}
```

This definition excerpt uses the field/vector-space sibling exports and the
linear-combination relation in the shared module. It is checked there; it is
not a standalone consumer. It illustrates how a mathematical relation
can define an object that later proofs use directly.

The standard directions span the plane and are linearly independent, so they
form a basis. Repeating a direction yields a dependent list. The chapter then
proves that every plane vector has unique coefficients in the standard basis:
spanning supplies a representation, and independence removes ambiguity.

## Finite combinations and linear maps

A selected function `linear_combination` evaluates an arbitrary finite
coefficient list. Adding or scaling coefficients adds or scales the value, so
every finite span is a subspace. Linear maps preserve these combinations.
Composition is written `map_compose` (the name `compose` is reserved by the
language). The real-plane projection illustrates kernels and ranges on the
coordinate axes, with a concrete rank-nullity picture and its eigenvalues
`0` and `1`. The Euclidean dot product then records orthonormality of the
standard directions.

## Reading guide

| Sections | Mathematical progression |
|---|---|
| 1.1–1.3 | Coordinate operations; fields; vector spaces; the real plane; uniqueness of zero and additive inverses |
| 1.4–1.5 | Pointwise operations on functions; subspaces; a translated-line counterexample; unique axis decomposition |
| 2.1–2.2 | Finite linear combinations; two-term sums; span; the standard directions span the plane |
| 2.3–2.4 | Linear independence; repeated directions; bases; standard expansion and unique coordinates |
| 2.5–2.6 | Finite-dimensional spaces; combination add/smul; span is a subspace |
| 2.7 | Prefix/deletion; dependence; length-two dependence lemma; span reduction for a dependent pair |
| 3.1–3.7 | Linear maps; zero preservation; composition; kernel and range; projection and an affine counterexample |
| 4.1–4.5 | Basis length two; no basis of length one; standard basis plus any third vector is dependent; projection kernel/range and eigenvectors; Euclidean inner product; matrix of projection |

These are selected, connected lectures rather than a complete translation of
*Linear Algebra Done Right*. The length-two dependence lemma and span-reduction
for a redundant last vector are proved in general form. The shared algebra
package now also proves finite basis existence, invariant basis length and
ordered basis extension, and supplies a guarded finite dimension value.
General matrix representation and Gram–Schmidt remain for subsequent lectures.

The source contains no `trust`, `axiom`, or `abstract_prop`.
The inverse operation is defined only for nonzero scalars, and the same
standard expansion is reused in the proofs of spanning and independence.

[math_collections.md](math_collections.md) explains the mathematical organization
and the roles of the main interfaces. [litex.config](litex.config) exports the
module as `linear_algebra`. For command-line usage, see the repository's
[CLI documentation](../../docs/cli.md).


The shared basis export now also proves coefficient uniqueness and representation
existence/uniqueness for arbitrary finite supplied bases, and selects guarded
`basis_coordinates`. Those general results are verified separately from this
lecture's standard-plane coordinate calculation. The bounded dependence lemmas
retain their length-two statements. The later shared dependence/exchange,
basis_comparison, basis_extension and dimension exports supply the general
finite results and a guarded dimension value. The
[dimension/extension consumer](../../examples/algebra/dimension_extension/main.lit)
computes the plane value 2 and extends (e1) while preserving its first entry.
