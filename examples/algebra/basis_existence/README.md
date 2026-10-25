# Finite basis existence

The main imported consumer starts with the redundant real generating list
(1,2,3), proves that it spans R using the existing unit basis and generator
inclusion, then obtains m<=3 and a basis of length m whose values come from
that list. The resulting basis is used by the existing unique representation
and guarded coordinate interfaces at vector 7. It does not prescribe a
particular basis or its coordinates.

contracts.lit checks all three new theorem interfaces over arbitrary supplied
carriers. boundaries/main.lit independently starts with the empty generating
list of the singleton zero space, obtains m=0 and a basis, and uses its
representation theorem. The real/zero-space data are shared with the existing
basis consumers through ordered context exports.

Run python3 examples/algebra/basis_existence/check.py after a release build.
The checker covers strict positive sources, nine controls rejecting only their
final statement, archive/shared-data imports and complete std/WiX equality.
The controls cover missing spanning/finite-dimensionality/removal premises,
a strict length decrease, unchanged basis length, equality of generator ranges,
wrong remaining length, empty removal length and an invalid index.

No maintained mathematical source adds trust, axiom or abstract_prop. A local
quantified induction invariant in the library is not a new public predicate.
Range inclusion guarantees value membership, not an ordered subsequence.
The later basis_comparison export proves invariant finite basis length, and
exchange provides a single-generator criterion. This example supplies no
selected dimension operation.
