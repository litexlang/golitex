# Subspace-sum example design

Use supplied subspaces of the same actual vector space. Finiteness belongs to
the inherited restricted space of each subset, not automatically to the
ambient space. Sum/intersection closure is proved before invoking their
inherited finite-dimensional domains and selected dimensions.

The generic source proof concatenates generators to obtain a finite sum,
and bounds independent lengths to obtain finite contained subspaces. A
basis of the intersection extends to a basis of the second summand. Its
new tail appended to a basis of the first summand is a basis of the sum.
No complement or canonical basis is selected. Empty intersection bases,
empty tails, zero summands and equal summands are valid.

The plane consumer uses a concrete one-vector axis basis to establish
dimension 1. Overlap exercises a nonzero intersection. Distinct axes have
full sum and zero intersection, and the Grassmann equality computes the
remaining axis dimension. Zero/full boundaries separately expose numerical
typing of selected dimensions, including the whole space with inherited
operations, rather than assuming equality of dependent struct instances.

Generic named contracts use the exact public headers with no ambient
finite-dimensional premise. Missing domain controls distinguish a selected
value that cannot yet be formed from a false numerical conclusion. The
current verifier can report missing nonemptiness first when finite-domain
evidence is removed; these controls are WD rejections, not claims that the
subspaces are mathematically empty or infinite. Containment, spanning, tail
independence and trivial-intersection/additivity premises have separate
controls. Concrete wrong sum/intersection dimensions are rejected only after
the complete real-plane context succeeds.

The isolated README result permits an arbitrary second subspace and requires
only the first summand to be finite. No matrix representation, external
product-space construction or compiler adapter is introduced.
