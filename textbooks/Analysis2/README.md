# Tao Analysis II as a Litex project

This directory is the final-product surface for the Litex translation of
Terence Tao's *Analysis II*, fourth edition. The ordered project entrypoint is
[`litex.config`](litex.config).

Run the implemented project with:

```text
target/release/litex -compact -r textbooks/Analysis2
```

The project exports all eight chapters in source order as `chap1` through
`chap8`.
The Chapter 1 public metric-space surface includes:

- `$chap1::is_metric_space(X,dist)`, the concrete real, restricted,
  finite-dimensional `l1`/`l2`/`linf`, and discrete distance functions, and
  the checked defining-formula bridge `real_distance_eq_abs`;
- `$chap1::has_metric_limit`, `$chap1::is_metric_convergent`, metric balls
  with checked center-containment and membership/inequality lemmas, interior,
  exterior, boundary, closure, open/closed predicates, and the checked
  `metric_boundary_of_complement_is_boundary` bridge;
- the checked real-distance convergence equivalence, relative
  openness/closedness, subsequences, sequence limit points, Cauchy sequences,
  the checked theorems `convergent_subsequence_has_same_limit`,
  `metric_convergent_implies_cauchy`, and
  `cauchy_with_convergent_subsequence_converges`, and complete metric spaces;
- sequential compactness, boundedness, open covers, finite subcovers, and
  nested compact intersections.

For example, the checked `metric_ball_contains_center` theorem derives

```litex
center $in \chap1::metric_ball<X, dist>(center, radius)
```

from `$chap1::is_metric_space(X,dist)` and `radius $in R+`.
Examples 1.2.2 and 1.2.3 additionally identify the planar Euclidean,
taxicab, and discrete balls and the usual real ball `B(5,2)` with their
displayed geometric sets.
Examples 1.2.7 and 1.2.8 identify the exact interior, exterior, and boundary
sets of `[1,2)` and of every subset equipped with the discrete metric.

Chapter 2 currently exposes the concrete predicates
`$chap2::is_metric_delta_controlled_at`,
`$chap2::is_metric_continuous_at`, and
`$chap2::is_metric_continuous`. Its checked
`metric_continuous_implies_continuous_at` theorem projects domain continuity
to a chosen point. Theorem 2.1.4 is represented by concrete sequential and
open-neighborhood characterization predicates plus four trusted directions,
matching Tao's exercise-deferred proof boundary.
Theorem 2.1.5 has a checked sequential equivalence and concrete inverse-image
sets, while its open/closed inverse-image directions remain trusted.
Corollary 2.1.7 is checked in both its pointwise and global composition forms.
Section 2.2 currently adds a concrete real-function pairing into
`\chap1::finite_real_vector<2>` and concrete addition, subtraction,
multiplication, maximum, minimum, restricted division, and scalar maps. The
continuity statements in Lemmas 2.2.1--2.2.2 remain exercise-deferred trusts.
Corollary 2.2.3 exposes named pointwise arithmetic combinations. Its seven
global preservation theorems are checked; the pointwise composition
identifications remain explicit trusts.
Section 2.3 adds concrete function images, real-function boundedness and
extremum attainment, and uniform continuity. Uniform continuity implying
continuity is checked; compact images, the maximum principle, and the
compact-to-uniform direction retain explicit proof boundaries.
Section 2.4 concretely models separations, connected spaces and subsets,
real order intervals, and values lying between two real values. Its real-line
characterization, connected-image theorem, and intermediate value theorem
remain explicit source-facing proof boundaries.
Example 2.4.2 exposes `[1,2] union [3,4]` as a disconnected real subset.
Section 2.5 adds the optional topology layer: topology laws, neighborhoods,
topological sequence limits, interior/exterior/boundary, closure and closed
sets, relative topology, topological continuity, open covers, compactness,
and connectedness. Example 2.5.3 connects a metric-induced topology to
metric openness and checks that every positive-radius metric ball is a
neighborhood of its center. These interfaces are concrete and checkable.

Chapter 3 exposes function limits, pointwise and uniform convergence,
bounded-function spaces, relational uniform distances, uniformly Cauchy
families, function-series partial sums, sup norms, and the Weierstrass
M-test. It then gives source-facing interfaces for exchanging uniform limits
with integration and differentiation, followed by polynomial presentations,
compact support, approximations to the identity, convolution, and the staged
Weierstrass approximation theorem. Riemann integrals and continuous
derivatives use concrete local
epsilon--delta/tagged-partition definitions rather than abstract interfaces.
The value of a function limit at a point of its domain
is checked directly, and global continuity of a uniform limit is checked from
the pointwise theorem.

Chapter 4 exposes formal power-series terms and partial sums, convergence
radii, real analyticity, derivative towers and Taylor coefficients, Abel's
endpoint theorem, summation by parts, and power-series convolution. It
constructs real exponential and logarithm selections, a coordinate-based
`ComplexNumber` carrier with arithmetic, conjugation, absolute value,
reciprocal, metric, and exponential interfaces, and real and complex
trigonometric functions together with a least-positive-zero definition of
`pi_real`. For example:

```text
forall x, y R:
    power_series_term(coefficients, center, 0, x) = coefficients(0)
    complex_add((x, 0), (y, 0)) = (x + y, 0)
```

The source-assigned algebra and analysis proofs remain explicit trust
boundaries. Radius of convergence, positive-base real power, and complex
exponential-series convergence now have concrete definitions. Chapter 4's
derivative and one-sided-limit vocabulary reuses Chapter 3's typed interfaces.
Complex limit laws and the real sine/cosine value relations are concrete.
Full-period sine and cosine identities are checked consequences of the
localized trusted half-period identities. The radius of convergence now uses
the source's reciprocal tagged-limsup definition over the coefficient-root
sequence; convergence inside and divergence outside remain later theorem
conclusions rather than being folded into the definition. Termwise
differentiation now derives a displayed derivative function from the
power-series hypotheses and records uniform convergence of the derivative
series on every smaller closed interval; it no longer assumes the derivative
in order to identify it. Termwise integration likewise derives the Riemann
integral value and its exact integrated coefficient series on every closed
interval inside the radius instead of taking the integral as a premise.
Proposition 4.2.6 constructs one coherent derivative family and coefficient
family for all orders; it no longer quantifies arbitrary caller-supplied
families or assumes their factorial coefficient law. Corollary 4.2.7 returns
one global derivative family whose finite prefixes are derivative towers and
whose members are analytic, rather than asserting those facts for an
arbitrary supplied family. Taylor's formula constructs local derivative data
on the expansion interval and binds `f^(k)(a)=k!c_k` to that same family,
instead of accepting unrelated whole-line functions as derivatives.
Power-series uniqueness compares two expansions of the same `f:E -> R` on
explicit positive-radius subintervals of `E`; it does not widen the function
to all reals. Both Abel endpoint theorems retain the concrete finite tagged
radius-of-convergence premise for the displayed interval. Summation by parts
uses a general zero-indexed real-series predicate without a misleading
nonnegativity name. The power-series product theorem consumes interval-wide
analytic expansions and concludes both product analyticity and the convolution
expansion; it is not a pointwise Cauchy-product claim for arbitrary convergent
series.
The exponential theorem exposes its infinite power-series radius, pointwise
absolute convergence and selected series value, analyticity, derivative,
continuity and integral, addition, normalization, positivity, reciprocal, and
strict-order equivalence. These exercise-deferred clauses remain separate
visible trust boundaries rather than being hidden behind a weaker summary.
The logarithm interface includes both `ln(1-x)` and its reindexed Taylor
series around one, with a concrete coefficient function, radius one,
analyticity at the center, and equality on `(0,2)`.
The complex-number law layer exposes both distributive directions,
conjugation's equality and real-fixed-point equivalences, both directions of
the zero-modulus criterion, and sum, difference, scalar-product, product,
conjugate, and quotient limit laws.
The trigonometric layer exposes concrete even/odd factorial Taylor
coefficient functions for cosine and sine, their displayed power-series
values, infinite convergence radii, pointwise absolute convergence, global
real analyticity, and continuity. It also records both Euler formulas and the
defining consequences `sin(pi)=0`, `cos(pi)=-1`, and `exp(pi i)=-1`.

Chapter 5 adds continuous periodic complex functions, their inner product and
L2 norm, characters, trigonometric polynomials, Fourier coefficients,
periodic convolution, approximation kernels, Fourier convergence, and
Plancherel. Its periodicity interface includes invariance under every integer
multiple of a positive period, not only the defining one-step translation.
Examples 5.1.2 and 5.1.4 bind sine, cosine, complex exponentials, the identity,
constants, integer-frequency functions, and the square wave to their actual
pointwise formulas before stating their periods or nonperiodicity.
The Hermitian integral is exposed both as a concrete coordinate-integral
relation and as the callable selected value
`periodic_inner_product(f,g)`; a checked bridge returns the defining relation
for that selected value. The source's periodic `L2` norm and induced `L2`
distance likewise have concrete candidate relations, callable selected
values, and checked selected-value bridges.
Integer-frequency characters are defined directly by the selected complex
exponential `exp(2*pi*i*n*x)`; a checked Euler-formula theorem exposes their
cosine/sine coordinates, while continuous one-periodicity remains an explicit
source-facing proof boundary.
Trigonometric-polynomial presentations explicitly retain their
`C(R/Z;C)` domain condition. Fourier coefficients are exposed both by the
inner-product candidate relation and by the callable selected value
`fourier_coefficient(f,n)`; its selected-value graph theorem is checked while
existence and uniqueness remain a localized construction boundary.
Its convergence theorems now use the actual Fourier coefficient
coordinates and their symmetric partial sums; absolute summability and the
Plancherel energy identity are explicit rather than represented by arbitrary
sequences. Plancherel now concludes convergence of the paired
positive/negative squared-coefficient series and the zero-frequency-adjusted
energy identity; it does not assume a caller-supplied convergent energy
sequence. Remark 5.5.2 explicitly records the failure of pointwise and
uniform convergence for arbitrary continuous periodic inputs, and the
pointwise/uniform recovery under coordinatewise differentiability and
continuous differentiability; these beyond-scope source claims remain visible
trust boundaries. The periodic L2 interface also exposes non-degeneracy,
Cauchy--Schwarz, triangle, Pythagoras, and homogeneity, while finite
trigonometric coefficient recovery includes the out-of-range zero
coefficients and finite Parseval identity. Character orthonormality includes
both the Kronecker-delta inner products and the source's unit-`L2`-norm
conclusion. Its inner-product interface exposes
Hermitian symmetry, positivity and definiteness, linearity in the first
variable, and conjugate linearity in the second. Periodic convolution exposes
its coordinate-integral graph, the callable selected function
`periodic_convolution(f,g)`, and a checked selected-function graph theorem.
It also exposes closure, commutativity, both additive laws, and equality of
the three scalar placements over supplied convolution functions. The
source's subsequent identities for convolution with one character and with
an arbitrary trigonometric polynomial are explicit proof boundaries rather
than omitted prose. Periodic approximation
kernels are continuous one-periodic complex functions with an explicit real
coordinate view, not detached real functions. Chapter 6 adds finite real
coordinate spaces, linear maps,
matrices, total/directional/partial derivatives, the chain and Clairaut
interfaces, contractions, and inverse/implicit function theorems. Its
coordinate-space interface includes zero and negation, distinguishes tagged
column vectors from row vectors, and exposes transpose, standard-basis unique
existence, and coordinate decomposition. The selected dimension-dependent
objects remain explicit proof/kernel boundaries because the current verifier
cannot store their dependent result carriers. Its
coordinate-space interface exposes all eight groups of source vector-space
laws rather than using addition closure as a proxy.
The first concrete linear-map examples are callable: dilation by five,
quarter-turn rotation, first-two-coordinate projection, zero-extension
inclusion, and identity. Rotation and inclusion expose checked coordinate
graphs, while their finite construction and the five coordinatewise
linearity proofs remain visible trust boundaries. Every linear map has a
unique displayed matrix representation, and represented matrix multiplication
is tied to pointwise composition of the represented maps. The concrete
Example 6.1.12 matrix and its induced map are callable, and its two displayed
coordinate formulas remain explicit in a typed output graph. The scalar
derivative lemma exposes both directions of its equivalence with the relative
linear-approximation estimate. The first worked several-variable derivative
example exposes its concrete base point, squaring map, derivative candidate,
checked coordinate graphs, and total-differentiability conclusion. Its
directional follow-up reuses those objects at direction `(3,4)` and records
the output `(6,16)`, preserving the positive-ray definition. The
next worked example connects the polynomial map
`(x,y) |-> (x^2+xy,y^2)` to both callable partial maps, its
base-point-indexed derivative action, the matching `2` by `2` Jacobian, and
the arbitrary-direction formula; its selected coordinate graphs check while
the constructions and analytic arguments remain explicit proof boundaries.
The chain-rule section also retains its worked product-rule specialization:
pairing two scalar functions, differentiating multiplication, composing the
maps and derivative actions, and obtaining the displayed product formula are
one connected interface rather than a detached identity. The adjacent
applications bind linear postcomposition to `DTf(v)=T(Df(v))` and bind a
coordinate curve, its velocity and its composite to the finite
partial-derivative chain sum. The first `C2` example then reuses the polynomial
map and partial maps from Example 6.3.9, records all four constant
second-partial vectors in one indexed family, and exposes their mixed
symmetry. The contraction section includes callable translation, halving, and
unit-interval quadratic examples and records all five source classifications,
including both non-strictness claims. The
contraction theorem separates unconditional at-most-one uniqueness from
existence on a nonempty complete metric space. The
contraction vocabulary preserves Tao's distinction: ordinary contractions
are nonexpansive, while strict contractions carry a displayed constant
`0<c<1`; the fixed-point theorems consume the strict relation. The total
derivative relation retains Tao's limit-point hypothesis through an explicit
distinct domain point in every positive Euclidean neighborhood. The
directional-derivative relation now uses Tao's positive-ray limit and requires
the base point to be interior. Partial derivatives retain the source's
two-sided coordinate-line limit by requiring compatible directional
derivatives along both `e_j` and `-e_j`. Lemma 6.3.5 also keeps the interior
premise when deriving directional derivatives from a total derivative. The chain
rule requires both source interior-point hypotheses, requires the inner map to
land in the outer map's domain, and binds its derivative pointwise to
`Dg(Df(v))`. The continuous-partials theorem now
requires a neighborhood `F ⊆ E`, an interior base point, every partial
derivative on `F`, and continuity of each partial at that point; its supplied
linear map is bound to the source's finite coordinate-sum formula. The `C^1`
and `C^2` predicates now expose their distinct source meanings: `C^1` requires
a continuous first-partial family on an open domain, while `C^2` requires each
first partial-vector function to be `C^1`. The inverse and implicit function
theorems consume the source's `C^1` hypothesis; Clairaut consumes `C^2` and
states mixed-partial symmetry for the full `R^m`-valued map, coordinate by
coordinate, rather than exposing only the scalar reduction used in its proof.
Lemma 6.7.1 represents invertibility with a displayed two-sided inverse and
states that this inverse is linear. Its
small-perturbation lemma now concretely states injectivity on a Euclidean ball
and containment of the half-radius ball in the image. The inverse function
theorem now concretely exposes its open neighborhoods, two-sided inverse laws,
and inverse-derivative formula. The implicit function theorem now exposes the
local zero-set graph and its coordinate derivative formula.
Example 6.8.3 applies that interface to the callable surface polynomial
`xy+yz+zx+1`, records its three ambient partials, and returns one local graph
carrying both displayed implicit derivative ratios.
Chapter 7
adds pointwise-defined open and closed boxes, box covers, outer measure,
Caratheodory measurability,
countable additivity, and measurable functions. The basic outer-measure law
package now exposes empty-set value, positivity, monotonicity, finite and
countable subadditivity, and translation invariance over explicitly bound
families, unions, values, and translated sets.
Examples 7.2.8--7.2.12 now expose the rational and irrational lines, the unit
interval and its irrational part, the planar unit segment, and the full
x-axis. Infinite outer measure is represented by finite measured subsets
above every real bound, while the finite zero/one values and the arbitrarily
short rational covers retain their dimension and concrete set data. The
finite and countable
outer-measure nonadditivity results now expose actual pairwise-disjoint
families and the failed sum equalities.
Both lower and upper coordinate half-spaces are explicit, so the source's
displayed `x_n>0` case and its all-coordinate extension are represented.
Finite-additivity failure now also yields an explicit existential
nonmeasurable-set conclusion. The measurable-set law package covers
complement, translation with equal measure, binary and finite
union/intersection, open and closed boxes, and outer-null sets. Its
countable-additivity theorem covers the finite-total branch with explicit
pairwise disjointness, member measure values, their real series total, union
measurability, and the same union measure value. The `+infinity` branch remains
outside the current real-valued outer-measure carrier. Sigma closure returns
both the countable union and countable intersection of the same measurable
family. Every Euclidean open set now has an exact `N+`-indexed
decomposition whose members are open boxes or explicit empty padding; this
uniformly represents finite, countable, and empty decompositions. The Borel
property uses the Chapter 6 Euclidean distance for both its open and closed
branches, rather than the unrelated discrete metric. Its
measurable-function layer now
defines measurability by inverse images of Euclidean-open codomain sets,
rather than the stronger and incorrect requirement over every subset.
The tagged extended-real definition is now connected to ordinary real-valued
measurability: a real function and its pointwise `(0,f(x))` embedding satisfy
an explicit two-way compatibility theorem.
Continuous-function measurability requires explicit metric continuity from
the domain equipped with the restricted Euclidean distance.
The open-box criterion now records both directions of the equivalence.
Coordinate measurability uses a supplied family of real functions explicitly
bundled back into the Euclidean-valued map and records both directions of the
coordinate criterion. Closure under a continuous outer function now binds the
open intermediate range, measurable inner function, continuous outer
function, and actual pointwise composition. Absolute value, maximum with
zero, and minimum with zero are represented by concrete pointwise transforms,
and all three measurable outputs are returned together. The layer also binds
sums, differences, products, pointwise maxima, pointwise minima, and the
nonzero-denominator quotient to their supplied input functions and returns all
six measurability laws. Real-valued measurability and measurable strict
superlevel sets are connected by an explicit two-way criterion, while
null-set modification remains a separate exercise-facing theorem. It also
defines sequence suprema, infima, tail extrema, limsup, and liminf explicitly;
Definition 7.5.9 now uses a genuine tagged extended-real carrier with separate
negative-infinity, finite-real, and positive-infinity values. Lemma 7.5.10 now
uses the induced tagged order, explicit sequence and tail suprema/infima, and
pointwise supremum, infimum, limsup, liminf, and limit relations. Its
source-facing measurable-limit conclusion remains one localized proof debt.
The finite-real companion binds every output function to the measurable
family and is retained for Chapter 8, where ordinary pointwise limits are
conditional on actual convergence. Chapter 8 adds simple
functions, nonnegative and signed Lebesgue integrals, monotone/dominated
convergence, Fatou, Riemann compatibility, and Fubini. Tagged extended
nonnegative addition covers both finite sums and the absorbing positive-
infinity branch. Tonelli now relates tagged pointwise partial sums and their
supremum to tagged integral partial sums and their supremum. Dominated
convergence now uses tagged extended-real functions, Chapter 7's tagged
pointwise-limit relation, a tagged nonnegative dominator with finite integral,
and convergence of real integral values. Equal upper and
lower integral values now imply signed integrability at their common value.
Monotone convergence and Fatou now use tagged extended-nonnegative functions
and integral values. Monotone convergence binds every member function to its
integral and records the
increasing tagged integral sequence, and identifies its tagged supremum with
the integral of the pointwise function supremum. Fatou uses Chapter 7's
extended-real tail-infimum and supremum relations for both the pointwise
function liminf and the liminf of the member integrals, and concludes tagged
order rather than assuming an ordinary limit.
Upper and lower Lebesgue integral values now include epsilon-close integrable
majorant and minorant witnesses in addition to their universal bound clauses,
so they express the source infimum and supremum rather than arbitrary bounds.
The simple, nonnegative, and signed integral law interfaces expose their full
source lists, including zero-a.e. criteria, homogeneity, monotonicity,
null-set invariance, and measurable restriction where applicable.
Absolute integrability now uses the source's tagged extended-real function
carrier. Its absolute value and positive/negative parts are tagged
nonnegative, their integral values must be finite, and the signed integral is
their real difference. The old R-valued layer remains explicitly named with
`finite`. Proposition 8.3.3 and dominated convergence use the tagged source
layer and retain finite companions. Upper and lower integral relations now
also quantify tagged extended-real functions and integrable
majorants/minorants, while retaining explicitly named finite companions.
The immediate consequences after Definition 8.3.2 are also explicit: the
signed integral agrees with the nonnegative integral on a pointwise-equal
nonnegative view, and the triangle inequality retains the full chain
`|integral f| <= integral f^+ + integral f^- = integral |f|`.
Definition 8.2.2 now uses a tagged extended-nonnegative carrier containing
finite nonnegative reals and positive infinity. Its integral relation is the
least tagged upper bound of the embedded integrals of all nonnegative simple
minorants. Remark 8.2.4 binds measurable-domain restriction pointwise and
connects a nonnegative real simple function and its tagged embedding to the
same value under Definitions 8.1.6 and 8.2.2. Proposition 8.2.6 now uses the
same carrier throughout: positive
scalar multiplication, pointwise order, zero almost everywhere,
almost-everywhere equality, domain restriction, and all integral values are
tagged. Theorem 8.2.9, Lemma 8.2.10, Corollary 8.2.11, and Lemma 8.2.13 use
that carrier as well. Lemma 8.2.14 identifies a null exceptional set outside
which a function with finite tagged integral is finite. Lemma 8.2.15 is the
Borel--Cantelli theorem for a measurable-set family with summable measures;
its infinitely-often set is defined by membership beyond every cutoff.
Remark 8.2.12 now exposes the moving-bump counterexample: the supplied family
is tied to the half-open intervals `[k,k+1)`, converges pointwise to a supplied
zero function, has member integral one, and has limit integral zero.
Fubini's section functions now agree with the one-dimensional section
integrals outside explicit null exceptional sets, matching the source's
"almost every" conclusion rather than incorrectly requiring every section to
be integrable.
The example after Proposition 8.4.1 exhibits the rational indicator on
`[0,1]`: it has Lebesgue integral zero but no Riemann-integral value. Remark
8.5.2 exhibits the complementary Fubini edge case: a function supported on
the null line `x=0` has planar integral zero, while its section at `x=0` is
not absolutely integrable and every section off that line has integral zero.
The simple-function layer now follows the source distinction between finite
measurable image and the derived finite characteristic-function
decomposition. Example 8.1.2 ties a supplied characteristic function
pointwise to a measurable subset and returns both measurability and
simplicity. Lemma 8.1.3 returns both addition and arbitrary real scalar
closure; Lemma 8.1.4 returns pairwise-disjoint measurable pieces, their
indicator functions, and the exact finite pointwise sum used by the integral.
Lemma 8.1.5 additionally requires every member of its increasing approximating
family to be simple, while the general monotone convergence theorem uses the
separate unrestricted pointwise nondecreasing relation.
The source-facing simple integral now uses the same tagged
`extended_nonnegative_real` carrier as later nonnegative integration. Its
finite branch embeds the real finite-presentation value; its infinite branch
records a positive level piece of infinite outer measure. Example 8.1.7
therefore states both displayed values, `11` and positive infinity, without
forcing the latter into `R`. The finite simple-integral companion and both
extended and finite nonnegative-integral value relations retain their exact
source domains.

All 282 currently tracked numbered non-exercise items have source-facing
definitions or theorem interfaces: 62, 26, 34, 38, 22, 36, 35, and 29 items
in Chapters 1--8. The workspace ledger tracks an ongoing cross-chapter audit
of examples and remarks against the manifest policy.
Every registered chapter file gate succeeds. The chapters are not
proof-complete:
Chapter 1 contains 80 explicit `trust` statements, Chapter 2 contains 34, and
Chapter 3 contains 30. Chapters 4--8 contain 122, 26, 63, 35, and 35,
respectively. The entire project contains no `abstract_prop`.
The Section 4.6 coordinate implementation checks addition and multiplication
commutativity directly. Remaining structured-value projection limitations are
recorded as verifier blockers and are worked around with explicit coordinate
relations; this project does not modify the kernel.
Most correspond to proofs Tao assigns to exercises; others mark substantial
source proofs or finite-choice arguments not yet formalized. The `linf`
distance uses a trusted unique-maximum selection because instantiating the
more direct recursive template currently exposes a verifier name-resolution
problem. These boundaries are listed in `todo.lit` and in the working
blocker ledger under `scripts/Analysis2/`.

The mathematical interface design is maintained in
[`math_collections.md`](math_collections.md). Source inventories, translation
records, verifier captures, and blocker notes remain in
`scripts/Analysis2/`.
