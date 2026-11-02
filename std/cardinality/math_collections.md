# Cardinality dependencies and foundation boundary

## General equinumerosity

`has_equal_cardinality` is an existential bijection predicate on arbitrary sets.
Reflexivity constructs the identity; symmetry constructs a local inverse by
unique existence; transitivity uses native composition. The inverse is a local
witness for the existential theorem, not another public inverse selector.
No finite-size expression is used in these general laws.

## Source and native finiteness

`has_n_elements` uses the source's one-based initial segment. A finite set's
existing native bijective index supplies one direction of the bridge; symmetry
reverses its orientation. In the other direction, a supplied bijection from
the initial segment transports native finiteness through the existing
surjective-image law.

The native size of the segment is proved separately for zero and positive
length. The positive branch publishes the exact endpoint inequality consumed
by the native range-size rule. Native finite-bijection counting then identifies
the natural cardinal with the existing selected size. Uniqueness follows after
first deriving finiteness; it never assumes finiteness of the source set as an
additional hypothesis.

Positive cardinality implies nonemptiness by contradiction: without a member,
extensionality makes the set empty, contradicting its positive native size.
The proof uses the native nonempty-set witness interface under an arbitrary
member. Member deletion uses the existing finite-difference count, then the
proved reverse bridge to the source cardinality predicate.

`has_finite_cardinality` quantifies the natural cardinal. Both directions of its
equivalence with native finiteness are explicit theorems. The infinity result
for `N` reuses its existing native infinite-set foundation through that bridge.
No user axiom, source trust or new native rule is introduced.

## Finite images, sequences and function spaces

The image bound first constructs a map from the original domain onto its
actual finite image. The existing finite-surjection inequality supplies the
bound. The original codomain is arbitrary and need not be finite.

The sequence prefix is the actual function restriction to `1..n`. Its carrier
proof uses the explicit inclusion of that index set into `1..n+1`. A sequence
of successor length is mapped to the unique ordered pair characterized by its
prefix and last entry. Coordinate equality proves injectivity; extension by
the final value proves surjectivity. Neither construction chooses a member
from an empty set. Induction from the singleton empty sequence and the native
Cartesian-product size law gives `size(finite_seq(Y,n))=size(Y)^n`.

For finite `X`, the native bijective enumeration and its locally constructed
inverse identify complete functions `X -> Y` with finite value tables. This
bijection is proved for arbitrary `Y`, using composition, pointwise function
equality and an actual table constructed from each function. For finite `Y`,
transporting sequence-space finiteness and size proves both function-space
finiteness and its source cardinality. The primary counting theorem states
`has_n_elements` directly, so callers need no additional finite-space premise
merely to state the result. A native-size computation follows after publishing
the separate finiteness certificate.

All zero and empty cases retain their mathematical meanings: the empty
sequence/function is unique and `0^0=1`. No Choice, Regularity, user axiom,
source trust or kernel change is used in these counting proofs. The complete
module has three predicates, one prefix template, two supporting universal
facts and 23 named theorems. Existing finite union, subset, injective-image and
Cartesian-product counting laws are reused rather than duplicated. Exact
full-domain checks of all six clauses of Tao 3.6.14 are retained in the
source-ordered experiment workspace. Countability, infinite-cardinal arithmetic
and arbitrary-index summation remain later source sections.
