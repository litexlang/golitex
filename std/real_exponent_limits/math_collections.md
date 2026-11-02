# Real exponent limits: mathematical collections

## Purpose and conventions

Tao Analysis I 6.7.1 establishes powered rational-sequence convergence and
independence; 6.7.2 defines real exponentiation by that limit; 6.7.3 extends all
corrected 5.6.9 laws to real exponents. This module proves their correspondence
with the existing native positive-base real power operation. Original integer
tails remain complete and their starts may be arbitrary integers. Rational
inputs use the established integer_index_tail and exact rational_tail_as_real
view. The scalar exponent and every output limit are finite reals.

## Actual continuous images

real_tail_function_image constructs f(a(n)) for an actual real tail and a
complete R->R function. It is a function, rather than a predicate about a
supplied image. Continuity at the input limit and source epsilon convergence
prove the image limit. The proof consumes the existing native continuity
control as a literal preimage inclusion, and uses delta/2 as the source radius.
This preserves strict native control and closed source epsilon bounds.

The function's complete real domain is part of this contract. A punctured
function does not supply that same object, even if a particular sequence avoids
its missing point. Later relative-domain work must retain its own explicit
actual-domain contract.

## Fixed-base functions and power sequences

positive_base_real_power_function is the actual R->R+ function t -> base^t for
each base in R+. The positive base belongs to its parameter domain and the
positive value belongs to its codomain. It has an independent mathematical use
as the continuous fixed-base exponential function. An inline scalar operation
alone would not supply the stable function object consumed by image construction.

Existing power/log identities and native exp/ln inverse laws give
base^t=exp(t*log(e,base)). Existing exponential continuity and scalar continuity
then prove the actual fixed-base function continuous everywhere. Its actual
image agrees pointwise with real_tail_fixed_base_power; checked function
extension reuses that image limit. No convergence premise is put into the data
family itself.

## Source existence, uniqueness and native compatibility

For every convergent rational input tail, its exact real view and the power
image theorem give convergence to base^alpha. The rational_floor_sequence of
alpha is an actual rational function with this input limit, providing source
existence at every real exponent. Sequence-limit uniqueness identifies every
candidate powered limit with the same native value. Applying that identification
to two input sequences proves independence, including different integer starts.

The limit relation, actual approximant construction, convergence existence and
value uniqueness are distinct roles. A second power selector or an unproved
choice of rational representation would obscure the established operation.
The source characterization uses its proved limit, with explicit convergence
before any existing partial scalar selector is consumed. Rational-exponent
compatibility also reuses the accepted native/rational fraction correspondence
from real_power_laws.

## Real-exponent order and reused laws

For positive q, logarithm order, multiplication by q, exponential order and the
power identity prove x^q<y^q from x<y. Applying the same law at exponent 1/q and
using existing power iteration proves the reverse implication. An explicit 1<e
supplies the checked logarithm monotonicity premise.

For base above one, the positive power of the exponent difference and the
existing addition law give strict exponent-order preservation. For base below
one they give reversal. Trichotomy and these strict directions prove the two
converses. All exponent variables here have real domains. Existing public
real_power_laws positivity, addition, iteration, reciprocal and product results
already have real-exponent domains and supply the remaining corrected source
parts without parallel copies.

## Dependencies and source build order

Signature/definition edges: native real tails and complete real functions ->
actual image; native positive bases and real powers -> fixed-base functions and
positive sequence data. Proof/import edges: native continuity control + source
epsilon limits -> image limits; existing exp/log identities and exponential
continuity -> fixed-base continuity -> power-image limits. Existence edges:
actual rational floor approximants -> source powered-limit existence. Proof
edges: existing limit uniqueness -> native value compatibility -> independence.
Existing scalar power algebra + log/exp order -> full real-exponent order and
reflection. These are acyclic dependencies and preserve the source's
convergence/definition/law order.

The proof basis explicitly reuses existing native exp/ln and continuity support,
in addition to ordinary arithmetic and the checked sequence/power libraries.
It does not claim a fresh elementary root/Cauchy reconstruction of those native
analysis foundations. No new axiom, trust or mathematical proof hole is added.

## Interface obligations and representative uses

Preserve base>0, actual complete domains and the positive output carrier. Keep
the native power operation fixed; the limit characterization supplies
compatibility rather than an overloaded spelling or alternate value. Verify
each reused source law at its full real domain. General membership, equality
and evidence reuse belong to shared verify; exact source facts and actual
functions are the authorized proof tools here.

Uses cover floor approximants of sqrt(2), positive bases 1/2,1,2 and selected
limits; lower and upper rational approximants with different first terms;
negative/zero exponent values; and a generic square-function image. Negative
controls cover nonpositive bases, invalid positive-order exponents, strict unit
boundaries, wrong monotonicity directions, wrong input/output limits, original
index guards, nonrational input and missing complete-domain/continuity premises.
