# Mathematical Organization

The central question of these lectures is how a small collection of directions
can describe an entire vector space. We begin with coordinate arithmetic,
establish the structures in which that question makes sense, and then develop
span, independence, bases, finite combination algebra, and linear maps. The
real plane connects the abstract definitions to examples throughout.

## Vectors, scalars, and operations

The real plane is $\mathbb{R}^2 = \mathbb{R} \times \mathbb{R}$.
A plane vector is an ordered pair of real numbers, with type `R × R`
(or `cart(R, R)`).
This Cartesian product is the same set as `finite_seq(R, 2)`, so its
coordinates are accessed as `v(1)` and `v(2)`.
A list of vectors has type `finite_seq(V, n)`, so its order and length belong
to its representation. No additional record is needed for the list itself.
Equality of coordinate vectors follows from equality at each index.

A field provides scalar operations and the laws governing them.
Its inverse operation has domain `x K: x != zero`; no inverse is assigned
to zero. `Field<K>`
therefore combines these operations with their axioms in one structure.
Likewise, `VectorSpace<K, field, V>` provides vector addition, a zero vector,
and scalar multiplication over that fixed field. A predicate alone would not
supply the operations needed by subsequent constructions.

The instances `real_field` and `real_plane` connect this abstract vocabulary
to real arithmetic and coordinate operations. Their laws are established in
the notes. Uniqueness of the additive identity and of additive inverses are
then derived consequences of the vector space axioms.

Pointwise addition and scalar multiplication show how functions can play the
role of vectors. The notes illustrate those operations; establishing all
vector space laws for a function space is a further development.

## Subspaces and decomposition

A subspace uses the operations of its surrounding vector space. For a subset
`U`, the relation `is_subspace(..., U)` expresses containment of zero and
closure under addition and scalar multiplication. This is a property of an
existing subset, so it does not require a separate structure with new operations.

The sets `x_axis` and `y_axis` satisfy this relation. The set `shifted_line`
does not contain zero and hence is not a subspace. Every plane vector has a
unique decomposition into a vector from each axis. This concrete result
introduces the mathematical idea of a direct sum.

## Linear combinations and span

A finite linear combination pairs each vector with a scalar coefficient.
The relation `is_partial_sum` describes successive
partial sums, beginning with zero. `has_linear_combination_value` identifies
the final sum, and `is_linear_combination` allows the coefficients to vary.
The selected function `linear_combination` exists for every finite length.

Coefficient lists support pointwise `add_coefficients`, `neg_coefficients`,
and `smul_coefficients`. The corresponding selected-value identities show that
span is closed under addition and scalar multiplication, and contains zero;
hence every finite span is a subspace.

`span` is a set-valued template: it selects precisely the vectors satisfying
`is_linear_combination` for a given list. The predicate `spans` says that this
set is the entire ambient space. The standard directions span the plane because
a vector's own coordinates provide suitable coefficients.

## Independence, bases, and dimension

`is_linearly_independent` says that a combination giving zero must have only
zero coefficients. This is a condition on a list, not additional data attached
to its entries. The standard directions satisfy it; repeating a direction gives
a nonzero choice of coefficients whose combination is zero.

`is_basis` combines independence and spanning. Spanning provides coordinates;
independence makes them unique. The notes prove the standard expansion and
`standard_coordinates_unique` for the real plane.

`is_finite_dimensional` expresses the existence of a finite spanning list.
`has_basis_length(..., n)` expresses the existence of a basis with length `n`.
The plane has such a basis with length two. Defining a general dimension
requires the further theorems that finite-dimensional spaces have bases and
that any two bases have equal length.

## Linear maps

`is_linear_map` is a relation on an ordinary function between two vector spaces
over the same field. Kernels and ranges reuse the builtin sets
`preimage(T, zero)` and `fn_range(T)`. Composition is the template
`map_compose`. The projection onto the horizontal axis is the running example:
its kernel is the vertical axis and its range is the horizontal axis.
