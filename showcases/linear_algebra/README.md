# Linear Algebra in Litex

These lecture notes develop selected ideas from Sheldon Axler's *Linear Algebra
Done Right*, using the real plane as a running example. They show how familiar
calculations lead to definitions, how concrete objects satisfy those definitions,
and how the resulting facts support further mathematics.

Read [linear_algebra.lit](linear_algebra.lit) from beginning to end. The two
chapters move from coordinate operations to vector spaces and subspaces, then
from linear combinations to bases and unique coordinates. Definitions and proofs
appear alongside the examples that motivate them.

## From coordinates to vector spaces

We begin with the two standard directions in the real plane:

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
and `VectorSpace`, checking their laws before proving that additive identities
and inverses are unique. The coordinate axes then provide examples of subspaces.
A translated line provides a counterexample, and the two axes give a unique
decomposition of every plane vector.

## From directions to unique coordinates

The span of a list contains all vectors obtained by taking linear combinations
of its entries. Once the linear combination relation has been defined, this
mathematical description becomes a set definition:

```litex
template<K nonempty_set, field &Field<K>, V nonempty_set, space &VectorSpace<K, field, V>, n N, vectors finite_seq(V, n)>:
    have span power_set(V) = {x V: $is_linear_combination(K, field, V, space, n, x, vectors)}
```

This excerpt uses the field, vector space, and linear combination definitions
introduced earlier in the notes. It illustrates how a mathematical relation
can define an object that later proofs use directly.

The standard directions span the plane and are linearly independent, so they
form a basis. Repeating a direction yields a dependent list. The chapter then
proves that every plane vector has unique coefficients in the standard basis:
spanning supplies a representation, and independence removes ambiguity.

## Reading guide

| Sections | Mathematical progression |
|---|---|
| 1.1–1.3 | Coordinate operations; fields; vector spaces; the real plane; uniqueness of zero and additive inverses |
| 1.4–1.5 | Pointwise operations on functions; subspaces; a translated-line counterexample; unique axis decomposition |
| 2.1–2.2 | Finite linear combinations; two-term sums; span; the standard directions span the plane |
| 2.3–2.4 | Linear independence; repeated directions; bases; standard expansion and unique coordinates |
| 2.5 | Finite-dimensional spaces; a basis of length two; the motivation for dimension |

These are selected, connected lectures rather than a complete translation of
*Linear Algebra Done Right*. The general linear combination relation is defined
for finite lists; the sum construction is developed for two terms. Functions
illustrate pointwise operations, without a full construction of their vector
space. Basis extension, equality of basis lengths, and a general definition of
dimension are topics for subsequent lectures.

The source contains no `trust`, `axiom`, or `abstract_prop`.
The inverse operation is defined only for nonzero scalars, and the same
standard expansion is reused in the proofs of spanning and independence.

[math_collections.md](math_collections.md) explains the mathematical organization
and the roles of the main interfaces. [litex.config](litex.config) exports the
module as `linear_algebra`. For command-line usage, see the repository's
[CLI documentation](../../docs/cli.md).
