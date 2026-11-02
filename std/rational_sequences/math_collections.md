# Source Cauchy-sequence dependencies

The module has ten construction templates, one actual reciprocal function,
eighteen predicates, one supporting universal index fact and 68 named theorems
(98 declarations). Source definitions and results cover sections 5.1-5.4.
Index and native representation bridges precede their consumers. Section 5.3
retains native R and its fixed arithmetic under the selected foundation scope;
there is no new quotient model, isomorphism or LIM selector.

The integer tail is an actual template-defined bounded set. Membership laws
recover its integer carrier and lower-bound condition. Numeric quantifiers
use integer variables with explicit membership guards. Cutoffs remain integers
and their source lower bound is included in the steady-after predicate. No
sequence is silently restricted to a nonnegative starting index.

The reciprocal sequence has exactly the domain n>=1. For each positive
rational epsilon, an actual positive natural cutoff above `2/epsilon` makes
both reciprocal magnitudes less than half epsilon. The triangle inequality
then proves closed source steadiness. Finite boundedness handles zero length
separately; a nonempty finite sequence uses the actual range of its absolute
values, its native finite maximum and a positive natural upper bound. All
selected bounds are rational and nonnegative.

The actual reindexing is `b(k)=a(start+k-1)` with a real return carrier for
native sequence interfaces. It preserves every rational value. To pass from
closed source rational-radius Cauchy control to strict native real-radius
control, choose a positive rational radius smaller than the supplied real
radius and translate the integer cutoff by `cutoff-start+1`. The general
integer translation theorem has no unnecessary positivity premise.

Cauchy boundedness reuses the existing checked native Cauchy-bounded theorem
on that actual reindexing. It extracts native lower and upper real bounds,
chooses a positive natural M above their absolute values, and transports the
two-sided bound back through `n-start+1` for every original index. It therefore
proves a rational bound from the source Cauchy premise, without assuming native
Cauchy, convergence, boundedness or a chosen bound as an extra hypothesis.

The imported caller checks negative starts, the reciprocal sequence, empty
and nonempty finite tuples, and a bounded oscillating sequence. Nearest false
controls cover illegal indices, missing tails, nonpositive radii, negative or
insufficient bounds, and the false converse from boundedness to Cauchy. Native
N+, real numbers, rational density, finite extrema and Archimedean bounds are
reused foundations. No new axiom, trust, parser, WD or verifier branch is used.

## Equivalent sequences (section 5.2)

Uniform closeness, tail closeness and eventual closeness use the same positive
real-radius scalar predicate. Equivalence quantifies positive rational radii,
as in the source, and is defined on arbitrary rational sequences. It assumes
no Cauchy or boundedness property. Reflexivity chooses the initial cutoff;
symmetry reverses pointwise closeness. Transitivity halves the radius and uses
`first+second-start`, proved above both original cutoffs even when they or the
start are negative. It never assumes that adding two negative cutoffs makes a
later cutoff.

The actual perturbation function is `center+coefficient*10^(-n)` on n>=1.
Induction proves the reusable growth law `n<=q^n` for q>=2 and n in N+.
For two amplitudes, let delta be their absolute difference and choose a
positive natural cutoff above `delta/epsilon`. The pointwise error is
`delta/10^n<=delta/n<epsilon`. This includes equal amplitudes (delta=0)
without dividing by delta. The numbered pair is the specialization
center=1, left=1, right=-1. No logarithm or prior limit theorem is needed.

Independent consumers cover the full six added theorem contracts, the source
pair, its actual rational terms, a selected small-radius tail, zero/equal
amplitudes, negative centers, transitivity, a negative-start common cutoff
and self-equivalence of an unbounded sequence. Different constant centers,
a premature tail, a missing growth premise, and Cauchy inferred from
self-equivalence remain false controls. This proves the sequence example,
not the decimal-expansion results of Appendix B.


## Representative arithmetic (section 5.3)

Cauchy sums and equivalent sums use half radii and the same joint-cutoff law.
The scalar bounded-product helper belongs to real_approximation and proves
`abs(x*z-y*w)<=epsilon*(x_bound+w_bound)` from bounds on x and w. Its zero-inclusive
raw inequality avoids making a zero radius an instance of the positive-radius
closeness predicate. Product Cauchy derives rational bounds from the source
Cauchy premises and uses epsilon/(M+N+1), valid when either bound is zero.
Equivalent products first derive Cauchy for the required replacement.

Native completeness supplies a unique candidate real limit for every source
Cauchy sequence. Reverse Cauchy transport uses the actual inverse index
n-start+1. Native limit tails are translated to original integer indices;
rational density and triangle inequalities prove equivalence preserves values
and common values imply equivalence. Native arithmetic limit theorems apply
to actual anonymous functions, whose pointwise identities are proved before
transporting their limits to the named rational constructors.

Finite-prefix replacement is an actual cases-defined function on the original
full domain. Eventual equality proves equivalence and Cauchy preservation;
native eventual-equality limit transport preserves the value. The rational
floor(n*x)/n construction has error<1/n for every real x, yielding native
limit x and source Cauchy. For nonzero x choose rational 0<c<abs(x)/2 and an
actual cutoff above 2/abs(x). The original tail then has magnitude>abs(x)/2;
replacing the finite prefix by c gives the full separated representative.

Uniform separation implies complete function membership into Q*. The reciprocal
template accepts exactly that nonzero-valued function contract. The scalar
inverse estimate in real_approximation uses positive lower bounds c,d and
`abs(1/x-1/y)<=abs(x-y)/(c*d)`. Radius epsilon*c*c proves reciprocal Cauchy;
epsilon*c*d proves inverse equivalence without Cauchy premises. Native quotient
limits identify 1/L only for nonzero L and pointwise nonzero denominators.

The earlier 35-declaration section-5.2 source and complete README are retained
as an exact historical snapshot in the owning experiment evidence. Current
source, generic imported contracts, applications, README snippets and false
controls have separate strict receipts. No user trust, axiom, native feature
or verifier change is introduced.


## Signed bounds and native order (section 5.4)

Four predicates express full-domain positive/negative rational uniform bounds
and their existence. Positive/negative bounds imply the absolute bound with
the same positive magnitude c. A legal initial index witnesses incompatibility
of simultaneous positive and negative separation. Actual pointwise negation
turns positive uniform separation into negative separation.

The native sequence comparison theorem is applied to the actual real reindexings
after proving transformed-index membership and pointwise comparison. The shared
source comparison theorem precedes its positivity consumers in dependency order.
Constants then transfer positive or negative rational bounds to the candidate
real limit; the resulting sign is strict because c>0. Nonnegative closure is
the zero-constant comparison case. No strict limit order is inferred from a
merely pointwise strict inequality.

For native x>0, rational floor approximants have error<x/2 after an actual
cutoff. A two-sided absolute-error bound gives approximants>=x/2; a rational
0<c<x/2 replaces the finite prefix. This constructs the full positive rational
Cauchy representative and preserves native value x. For x<0 construct a positive
representative of -x, then negate its actual values and its native limit.

Native signs, absolute value, both directions of strict/weak order definitions,
exclusive comparison trichotomy and all five ordered-field claims are audited
in the owning experiment. Positive reciprocal order, rational lower/positive
integer upper bounds, the Archimedean property and rational density reuse the
existing native contracts. They do not create redundant public operations or
new foundational assumptions. Public source proofs, full imported contracts,
README examples and nearest wrong-sign/strict-limit controls have separate gates.
