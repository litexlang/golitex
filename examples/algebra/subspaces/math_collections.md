# Mathematical content and dependencies

The model comes from the preceding dimension/extension example. The new work
uses the existing supplied real Field and plane VectorSpace, the subspace
predicate and the new source-only inherited-space interfaces.

For the x-axis, closure follows from the second coordinate. A zero combination
of the one-vector list (e1) has trace endpoint c1*e1; its first coordinate forces
c1=0. Every point (x,0) is the combination with coefficient x. Transfer
independence and equality of spans to the inherited carrier, obtaining a basis
of length1. The existing guarded selector therefore returns1.

The same transfer gives the full plane its standard length2 basis. The empty
list is a basis of the singleton zero carrier: its span contains zero, and
there is no other vector. The selected dimensions2/0 check both extreme
subspaces and show that zero is a valid natural dimension.

Projection (x,y)->(x,0) preserves the supplied plane addition and scalar action.
The existing kernel/range theorems prove their subspace properties. New
nonempty/carrier/finiteness results then make them genuine finite-dimensional
VectorSpaces, to which the new dimension bound applies. No general rank-nullity
formula or separate image-finiteness-from-source theorem is asserted here.

All new mathematical laws are derived in std; the caller supplies no axiom,
trust, scalar order or replacement abstract predicate. Index comparisons in
the generic proof concern finite list lengths. Characteristic and scalar
cardinality remain unrestricted by the generic statements.
