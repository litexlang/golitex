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

## Finite-set counting

The finite-set source layer uses the same native finite_set_size with union,
intersection, difference, Cartesian products and powersets. The standard
two-set formula subtracts the overlap; applying it again to union(A,B) and C,
then distributing intersection over that union, yields three-set
inclusion-exclusion. Nonnegative intersection sizes yield union bounds.
The symmetric difference is the actual union of the two disjoint differences,
not a new counting operation. A subset has the same size as its finite ambient
set exactly when the sets agree; a difference formula must retain the subset
premise. Empty, identical and nested finite sets belong to these interfaces.

The representative source result is
three_set_inclusion_exclusion(A,B,C), with three finite-set arguments and the
usual alternating sum including the triple intersection. Its immediate use
counts a genuinely overlapping three-set union. A sum of individual sizes
without overlap correction is the nearest false alternative. Named source
results for native product and powerset sizes expose standard mathematical
principles while explicitly reusing their existing builtin rules. This layer
does not introduce binomial coefficients, factorial quotient integrality,
general indexed inclusion-exclusion, probability or fiber sums.

Nested finite domains need explicit checked evidence before a cardinality
goal. Internal quantified closure facts establish that evidence inside the
module. Imported ordinary facts do not become ambient caller facts, so
symmetric_difference_is_finite(A,B) and
three_set_union_intersection_are_finite(A,B,D) expose the actual closure
conclusions as named results. Their source proofs establish the child finite
sets before the parent operations. Independent generic consumers release
these results in universal claims before stating the count goals; concrete
consumers can do the same for actual sets. Adding caller hypotheses would
unnecessarily restrict the mathematical contract, and adding a new global
strategy would change an independent automation boundary. These closure
interfaces keep the proof explicit in the existing module system.

All twelve added source results and the full-domain imported consumers pass
strict verification. Native cardinality identities remain reused dependencies;
no native Obj, Fact, reserved theorem, rule or strategy is added. The existing
single main export and original finite-map source prefix are preserved.
