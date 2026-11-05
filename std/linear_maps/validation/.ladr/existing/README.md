# Original-hypothesis linear-map reuse

This fixture imports only Algebra. Its 33 checked claims and three retained-
context refusals accept 3.1/3.4/3.7/3.10/3.11/3.13/3.14/3.15/3.16/3.18/3.19/3.21/3.22/3.24.
See [checker](../check_existing.py) and [checker](../check_existing.py).
There is no new public mathematical declaration or native rule in this increment.

The source correspondence uses the existing linearity predicate, composition,
native preimage/range and injective/surjective predicates. Both directions of
surjectivity and full range are checked explicitly. Kernels and ranges have
their original subspace proofs; both directions of the zero-kernel criterion
are checked without finite dimension assumptions.

The basis-image claim proves actual unique existence of a linear function,
using equality of its complete mapped basis list with the prescribed list.
The existing selected extension is a witness; equality on a basis proves
uniqueness. Natural list length includes zero, and no finite target dimension
is required. Pointwise basis entries follow from the proved list equality.

The rank-nullity claim states the dimensions of the actual inherited kernel
and image spaces. It proves those spaces finite dimensional from only finite
source dimension and linearity; it does not assume finite target dimension.
The larger-domain injection and smaller-domain surjection impossibilities
retain both original finite-dimensional hypotheses.

Refusals reject a zero-kernel argument without linearity, an extension argument
without a basis, and range-subspace reuse without linearity. Every following
direct kernel/image dimension claim passes in the retained context.

The earlier 31-claim checkpoint is retained separately. Two full-range claims
were added after checking the source formulation of 3.19; the final 33-claim
file and clean boundary replay supersede that checkpoint.

The [author PDF](https://linear.axler.net/LADR4e.pdf), dated 30 October 2026,
and [errata](https://linear.axler.net/LADRErrata4e.html) were checked as a
supplement to the historical catalogue. Its absent local text path and old
ID/line anchors are not silently replaced.
