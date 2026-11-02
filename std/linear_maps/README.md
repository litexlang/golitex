# Linear inverses and isomorphisms

Import this module with LinearMaps = linear_maps under [import std]. It reuses
the supplied Field/VectorSpace interfaces and the existing Algebra inverse-
bijection selector. It adds source proofs without assumptions or native rules.

The inverse export defines is_two_sided_inverse by both pointwise identities,
proves bijectivity and uniqueness, and defines is_linear_isomorphism by linearity
plus an actually linear reverse with both identities. are_linearly_isomorphic
packages existence of such a map. Linearity plus bijectivity is equivalent to
isomorphism without finite dimension hypotheses. The selected inverse is linear
and unique; no competing inverse selector is introduced.

The dimension export proves that injectivity or surjectivity implies isomorphism
between finite-dimensional spaces of equal dimension. It proves both directions
between equal finite dimensions and existence of an isomorphism. The
identity_compositions export connects the pointwise definition to both composition
equalities and proves both one-sided implications under the original equal finite
dimension hypotheses. Dimension zero is included. ST acts on V and TS on W.

The [acceptance](validation/.ladr/acceptance.json) records a strict four-statement
final target after ten inverse and five dimension predecessors, 72 independent
imported statements and five retained-context refusals. Examples include x -> 2x
on R with inverse x -> x/2, x -> ix on C with inverse x -> x/i, and both
zero-dimensional coordinate spaces. Controls reject missing inverse, bijectivity
and equal-dimension premises, retaining valid complex inverse evaluation.
Run [check.py](validation/.ladr/check.py) with LITEX_CHECK_BINARY set to the pinned
executable recorded in the receipts. A metadata note preserves a corrected
helper-default executable hash; both actual gate commands used the unchanged pin.

LADR 3.59/3.60/3.61/3.63/3.65/3.68/3.69/3.70 are accepted. The
[source concordance](validation/.ladr/source_concordance.json) records the
[author PDF](https://linear.axler.net/LADR4e.pdf) and
[errata](https://linear.axler.net/LADRErrata4e.html), including the 3.68 domains.
Historical catalogue IDs and line anchors are retained. The original local text
path is absent; the supplementary online check does not replace that pinned source.

The [existing-interface audit](validation/.ladr/existing_acceptance.json) also
passes 33 Algebra-only claims and three refusals. It accepts fourteen 3A/3B IDs,
including actual unique basis extension and the direct kernel/image dimension
formula under finite source dimension alone. Both surjectivity/full-range
directions match the book's formulation. No new public interface is added there.

## Actual space of linear maps

The space export registers 46 source statements; its accepted module checkpoint
has 65. Four registered composition statements bring the current module to 69.
linear_map_carrier<K,F,V,source,W,target> is the actual subset of FnV W satisfying
the original linearity predicate. linear_map_add and linear_map_smul return that
same carrier. linear_map_space is an actual VectorSpace on it, constructed from
the proved zero/addition/scalar-multiplication tuple. No finite dimension is assumed.

The accompanying vector_function_space<K,F,X,W,target> is the actual pointwise
space of W-valued functions on any set X, including an empty domain. Its
pointwise_map_add, pointwise_map_smul and pointwise_map_zero functions have one
fixed vector-valued contract. Linear maps form a proved subspace of it.

The public space_add/space_smul/space_zero theorems expose the actual object's
operations. The corresponding function_carrier theorems support typed result
aliases; space_*_pointwise computes those result functions. This explicit route
avoids a remaining direct nested-call goal-WD miss without adding assumptions.

The canonical 46-statement target passes with its 19 predecessors. The
independent caller passes 121 statements and five refusals, including actual
real/complex sums, scaling, zero, both zero-dimensional coordinate spaces, empty
ambient function domains, and general VectorSpace theorem reuse on the new object.
The saved file and clean retained-context replay pass. LADR 3.2/3.5/3.6 are
accepted in [space acceptance](validation/.ladr/space_acceptance.json).

composition.lit passes its four-statement target after 65 predecessors, 67
independent imported statements and three retained-context refusals. It proves
whole-function associativity, both identities and both sum distributions.
Inner-sum distribution requires the outer function linear; outer-sum distribution
holds for arbitrary supplied functions. The caller checks the original all-linear
hypotheses, actual R/C values and zero-dimensional spaces. LADR 3.8 is accepted
in [composition acceptance](validation/.ladr/composition_acceptance.json).

Representing matrices, rank correspondence, systems and change of basis remain
unfinished. Complete FTA is also unfinished.
