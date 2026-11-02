# Countability design

## Exact source conventions

`is_countably_infinite_set(X)` means `card::has_equal_cardinality(N,X)`.
`is_at_most_countable_set(X)` means finite or countably infinite.
`is_uncountable_set(X)` means neither finite nor countably infinite.
Not countably infinite alone does not imply uncountable: the empty set is the
nearest counterexample. All domains include the original native natural0.

## Well ordering and increasing enumerations

Reuse `rsub::is_least_natural_member` and full unique existence on every
nonempty natural subset, including infinite subsets and sets containing0.
The existing selector requires explicit nonempty natural-subset membership.
`is_strictly_increasing_natural_map(a)` uses adjacent strict growth on all N.
`is_increasing_natural_subset_enumeration(X,a)` combines the actual bijection
N->X with this growth. The exact exist! theorem requires X infinite.
A finite set cannot be the range of such a bijection. Recursion preserves the
original complete N input. Uniqueness compares the initial minima and the
successor minima of equal upper tails. No dependent function-valued selector
or alternate input-domain view is added.

## Subsets, images and unions

An arbitrary natural subset is at most countable. For a subset of any at-most-
countable set, use the actual preimage under a full enumeration and construct
a restriction with that preimage as its own domain. For sequence images,
`is_first_natural_occurrence(Y,f,index)` selects the first occurrence of each
value. Well ordering supplies it even when f has repetitions. Image results
conclude at-most-countability, since a constant sequence has a singleton image.
Two countably infinite sets have countably infinite union: interleaving proves
at-most-countability, and a contained infinite set rules out finiteness.

## Triangular pairs and products

`natural_triangular_number(0)=0`, and the successor difference is n+1.
The actual rank on `triangular_natural_pairs` separates rows and is injective
into N. The actual axis n->(n,0) proves infinitude. The map
(n,m)->(n+m,n) is a full bijection from N^2 to the triangular set, with inverse
(r,c)->(c,r-c). Product bijections then cover arbitrary countably infinite
X and Y. Empty or finite products are not silently declared countably infinite.

## Integers and rationals

Negation bijects N with the nonpositive integers. Their union with N is Z.
The fraction map from cart(Z,N+) has complete image Q, using the existing
native reduced-fraction theorem. N contained in Q proves infinitude. Neither
real uncountability nor a new choice axiom is used. These are library proofs;
no parser, verifier, kernel, or native-mathematics feature is changed.
