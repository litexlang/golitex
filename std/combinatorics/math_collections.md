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
selected. The ten source proofs and full-domain imported use probes are checked in strict mode. General
indexed inclusion-exclusion, recurrence solving and generating functions remain future
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

## Natural binomial coefficients

The numeric construction is binomial_coefficient(n,k), with both indices
natural and result natural. Row0 is1 at column0 and0 at positive columns;
positive rows start at1 and positive columns follow the Pascal recursion on
the previous row. Recursion decreases the first index, while both recursive
column arguments remain natural. This is one callable mathematical value,
not a proposition about a supplied candidate and not a rational factorial
quotient whose integrality is deferred. The natural domain includes row0 and
all columns above the diagonal. The zero-column branch is checked first, so
its value is directly available at an arbitrary row without an extra
evaluation theorem.

The proof spine derives zero above the row and the diagonal, then the first
two nonconstant columns, symmetry, positivity and monotonicity in the row
index. Generalized row properties may be local induction invariants; they
are not public law certificates. The representative use is B(5,2)=B(5,3)=10,
alongside B(0,0)=1 and B(3,4)=0. Direct defining equations and the full
positive-column Pascal relation is checked without evaluation-wrapper
theorems. In particular, column1 must not inherit the showcase's extra r>1
restriction.

The original numeric layer does not by itself establish the factorial formula,
binomial theorem, row-sum identities or the cardinality of k-element subsets.
The natural interface, nine original source theorems and
full-domain imported use probes pass strict verification. Imported use starts
with release obj def on the actual function: imports expose definitions, while
the explicit release supplies the callable membership and guarded equations
needed by calls and theorem conclusions. An omitted release is a checked
failure boundary; it is not evidence of a missing recursive-function kernel
feature. No wrapper, extra caller premise, native rule or global strategy is
introduced.

Implementation order follows proof dependencies: above-row vanishing precedes
the diagonal; the first column precedes the second; the diagonal supports
symmetry, which supports penultimate entries; positivity supports strict row
growth. Weak row growth follows directly from the natural codomain and the
Pascal step. Local generalized row invariants stay inside three proof bodies.

## Binomial expansion and finite fibers

The extension derives the factorial product identity by row induction and
Pascal recursion, then divides by proved positive factorials. A complex-valued
`binomial_terms<n,x,y>` function is defined on all natural indices, using zero
above the row. This avoids negative powers at zero bases. Reindexing and
weighted successor sums support the row induction for the actual binomial
expansion. Finite-prefix extensionality then transfers that expansion to any
supplied function agreeing with the terms through n. The expansion theorem
also exposes the actual constructed terms directly; it requires no supplied
candidate. Row sums specialize the two complex parameters to 1,1 or -1,1.
The alternating sum retains the necessary positive-row condition.

Fiber counting uses existing preimages and native cardinality. Disjoint target
subsets have disjoint preimages; finite-subset cardinality induction therefore
proves the sum over S equals the cardinality of its preimage. Taking S=Y gives
the total fiber sum. Constant or bounded summands yield uniform, upper and
lower counts; contradiction gives generalized pigeonhole. Positive fibers
characterize surjectivity and fibers of size at most one characterize
injectivity. These contracts allow empty finite carriers and uniform value
zero, without adding nonemptiness or surjectivity to total counting.

The resumed 2026-10-30 checkpoint passes the clean 69-statement strict source,
71 clean imported statements and generic contracts for every added theorem.
A fresh Session replays the 71 positive statements and confirms 20 final-only
refusals at the intended premise, argument, WD or proof-search phase. Actual
models include the complex expansion, fibers of sizes 2,3,0 and empty/zero
boundaries. The user subsequently requested removal of this round's tests,
journals and temporary verification directory; the earlier cleanup remains
in effect. These are historical checkpoint results. This checkpoint does
not establish the subset-cardinality interpretation of binomial coefficients,
Vandermonde's identity, generating functions or indexed inclusion-exclusion.
