# Finite maps and counting

Cardinality remains native finite_set_size, and mapping properties remain
native injective/surjective/bijective with their exact complete domains. No
parallel count function, function type, inverse selector or law certificate is
introduced. Empty finite sets remain allowed; a map from a nonempty set to an
empty target cannot be supplied.

The intended interface consists of named source theorems. An injection has
image cardinality equal to the source and image contained in the target; this
gives the injection bound. Surjections have the native opposite bound. A larger
source therefore has a genuine collision pair, and a larger target has a
specific omitted value. Both conclusions use existing existential/universal
facts, rather than a new proposition whose definition asserts the theorem.

Equal finite cardinalities make an injection surjective by image inclusion and
cardinality. For the converse, a duplicate can be removed without losing
surjectivity: construct an actual local map on X minus one point and redirect
the removed point's image through its distinct duplicate. Cardinality then
forces the source to be strictly larger than the target. This yields injection
for an equal-size surjection. Two opposite injections consequently make both
maps individually bijective; there is no assertion that they are mutual
inverses. A permutation counterexample will enforce this boundary.

Singleton deletion and disjoint partition cardinality use native difference,
intersection/union and finite_set_size. These are reused mechanisms, not new
cardinality rules. The dependency graph is proof edges from native cardinality
to bounds/deletion, from bounds to pigeonhole/omitted value, from image equality
to injection-bijection, and from deletion+surjection to collision bound then
surjection-bijection. No choice or existence of an arbitrary bijection is
selected. The ten source proofs and full-domain imported use probes are checked in strict mode. Binomial/Pascal functions, general
fiber sums, graphs, recurrence solving and generating functions remain future
work. The original discrete showcase is preserved and not treated as a full
course. No compiler/Lean or global release certification is implied.
