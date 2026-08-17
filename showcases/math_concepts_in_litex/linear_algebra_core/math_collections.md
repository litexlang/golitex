# Mathematical Design: Linear Algebra Core

## Implemented first-version slice

`main.lit` now implements Gate A concretely over `R^2`: linearity, zero
preservation, kernels, the subspace criterion, both directions of the
kernel-zero/injectivity theorem, and coordinate projection as a noninjective
example. This keeps the reader path executable without claiming that the
future generic `RealVectorSpace` structure already exists. The file contains
no direct `trust`.

## Core interface cards

### Real vector space

- **Meaning:** a carrier with zero, addition, and real scalar multiplication
  satisfying the vector-space laws.
- **Form:** `struct RealVectorSpace<VSet>`; downstream theorems pass the object
  and project its operations.
- **Rejected form:** one giant `prop` as the only public interface, because
  callers need callable operations; also reject a first-tranche generic field
  parameter that hides the reader path.
- **Use:** subspaces, linear maps, all Gate A theorems.

The first version uses the displayed coordinate operations on `R^2`; the
structure in this card is the next abstraction gate, not current API.

### Subspace

- **Meaning:** a subset containing zero and closed under addition and scalar
  multiplication.
- **Form:** `prop is_subspace(V,U)` plus a construction exposing the induced
  vector-space object once laws are proved.
- **Rejected form:** only a structure with no candidate predicate; kernel and
  range proofs naturally establish that supplied subsets satisfy laws.

### Linear map

- **Meaning:** a supplied function preserves addition and real scalar
  multiplication.
- **Form:** `prop is_linear_map(V,W,T)` plus a set/typed family of callable
  functions satisfying it.
- **Rejected form:** a theorem for each concrete map or a relation that makes
  application awkward.
- **Use:** composition, kernel, range.

### Kernel and range

- **Meaning:** vectors mapped to zero, and codomain vectors attained by the
  map.
- **Form:** set-valued constructions. Range uses an existential preimage
  relation internally.
- **Rejected form:** only membership predicates; callers need set equality,
  subspace structures, and dimension.
- **Use:** injectivity, surjectivity, rank-nullity.

### Basis and coordinates

- **Meaning:** finite vectors that are independent and span; every vector has
  one coordinate list relative to a basis.
- **Form:** basis as `prop`; candidate coordinate relation as `prop`; selected
  coordinate map via `have fn ... by exist!` after the existence/uniqueness
  theorem.
- **Rejected form:** defining coordinates by arbitrary choice or hiding
  nonunique spanning coefficients before independence is known.

### Dimension

- **Meaning:** the common length of every finite basis.
- **Form:** selected natural only after existence of a basis and uniqueness of
  basis length; domain restricted to finite-dimensional spaces.
- **Rejected form:** an axiom-valued function or the length of an unspecified
  arbitrary basis.

## Main dependency DAG

```text
R and carrier V
  -> RealVectorSpace<V>                           [signature, law]
  -> is_subspace / induced subspace               [definition, law]
  -> is_linear_map / composition                  [definition, law]
  -> kernel / range                               [definition]
  -> kernel and range are subspaces               [proof]
  -> injective iff zero kernel                    [proof]

finite sequences + finite sums
  -> linear combination                           [definition]
  -> span / independence                          [definition]
  -> basis                                        [definition]
  -> coordinate existence and uniqueness          [existence, uniqueness]
  -> coordinate map                               [selection]
  -> basis-length uniqueness                      [proof]
  -> dimension                                    [selection]
  -> rank-nullity                                 [proof]
  -> basis-relative matrix                        [definition]
  -> matrix of composition                        [proof]
```

The Gate B blockers must remain explicit. In particular, finite basis
selection, basis extension, finite sums, and basis-length uniqueness are
ordinary mathematical/library obligations. They are not reasons to make
rank-nullity a Builtin rule or to place a broad `trust` at the flagship.
