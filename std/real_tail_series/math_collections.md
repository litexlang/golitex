# Real-tail series: mathematical collections

## Formal data, partial sums and scalar selection

Source 7.2.1 supplies an integer start and a real value at every integer n>=start.
These are the actual data parameters; there is no extra formal-series AST or
premature scalar value. real_tail_partial_sums constructs the complete function
n->sum(start,n,a) on that same original tail. Every native range sum here has
start<=n. Source 7.2.2 is the established real-tail limit of this actual sequence.

has_real_tail_series_sum is a relation between the data and a candidate finite
real value. is_convergent_real_tail_series asserts existence. Uniqueness follows
from existing real-tail limit uniqueness. The guarded real_tail_series_sum
consumes convergence and uses the established selected limit of partial sums.
The candidate, existence and canonical value retain their separate roles.

## Exact original/native correspondence

The existing real_tail_reindex constructs a complete N+ sequence from the
actual original data, with no extension outside the original domain. Ordinary
induction proves S(start+k-1)=partial_sum(reindex(a),k), using exact interval
inclusion, legal endpoint memberships and scalar output carriers. The existing
partial_sum and partial_sums definitions are explicitly released where their
source interfaces require it. Both series-candidate and convergence directions
follow from the actual partial-sum identity and established limit transport.

## Full finite-tail Cauchy criterion

Source 7.2.5 uses the actual finite_set_sum on closed_range(p,q), including empty
reversed intervals. The small-tail predicate owns a positive radius and a cutoff
in the original tail. Its endpoints also belong to that tail and are quantified
above the cutoff; this has exactly the source scope since cutoff>=start.

The finite-block difference gives the partial-sum difference when p>start and
p<=q. Its q parameter explicitly has the actual partial-sum endpoint carrier.
In the forward criterion, shifting a partial-sum steady cutoff by one supplies
the predecessor endpoint. An extensional empty-block identity handles p>q.
In the reverse criterion, both strict endpoint orders and equality give
partial-sum steadiness. Existing real Cauchy completeness then gives a candidate.
The radius convention remains the source closed <=epsilon bound.

## Zero test and absolute convergence

Source 7.2.6 transfers the existing native ordered-series zero test through the
complete original/native bridge. The original terms tend to zero on their
actual domain, for every integer start. Source 7.2.8 uses the existing
real_sequence_limsup::real_tail_absolute_values construction; no parallel
absolute-value sequence operation is introduced.

Function extensionality proves exact absolute/reindex agreement. The established
native absolute-series convergence theorem then transfers back to the original
series. To complete 7.2.9, candidate limits L for a and M for its absolute values
give abs(L)<=M. The proof exposes complete iterand membership and partial-sum
function congruence, applies finite-set triangle with the exact finite-domain
absolute callback, and uses source partial_sum_extensional and adjacent equality
chains to transport that bound to existing native absolute_terms. Existing
absolute sequence limits and limit comparison finish the result.

## Dependencies and acceptance uses

Formation edges: original tail carriers -> actual partial sums and reindex;
existing actual absolute values -> absolute series. Proof edges: finite recurrence
-> exact partial-sum identity -> both candidate/convergence bridges; finite-block
difference + partial-sum steadiness + native completeness -> full Cauchy criterion;
series bridges + existing native tests -> zero/absolute convergence; exact finite
triangle + source partial-sum extensionality + native limit order -> scalar bound.
The dependency graph preserves source order and introduces no circular premise.

The complete section7.2 correspondence includes the following additional
source constructions and laws. Independent uses check negative
integer starts, signed geometric sum -1/3, its actual absolute sum 1, exact
original partial sums and blocks, a supplied zero-series Cauchy-tail proof and
canonical values. Controls cover wrong values/limits, missing convergence guards,
out-of-domain endpoints, invalid radii/cutoffs, nonscalar or incomplete data and
invalid nonempty block premises. Exact receipts and historical failed attempts
remain in experiments. No new axiom, trust or native implementation is used;
shared verify owns general membership and evidence composition/reuse.

## Actual alternating data and both source directions

real_tail_alternating_terms constructs (-1)^n*a(n) on the actual original
integer tail, with no convergence, nonnegativity or monotonicity premise in
the data itself. Adjacent decrease implies full nonincrease after actual
reindexing, by ordinary induction. The forward theorem retains the complete
source nonnegative/decreasing/zero-limit hypotheses. Its native positive-first
alternating data is multiplied by (-1)^(start-2); exact integer-power identities
then give the literal original (-1)^n sequence, including negative starts.

For the reverse theorem, the zero test and the existing actual absolute-value
construction identify the absolute alternating data with the nonnegative
magnitudes. Function extensionality transfers their zero limit. This direction
needs nonnegativity and convergence; monotonicity is not required. Together
the two directions give the complete source7.2.12 equivalence.

## Series algebra, finite prefixes and integer translation

Existing real_tail_sum and real_tail_scaled construct actual data independently
of convergence. Exact native reindex values and ordered-series laws prove
candidate sums L+M and c*L for arbitrary real c, including zero and irrational
values. Candidate existence and guarded selection retain their established roles.

The existing real_tail_restriction supplies the actual later-domain data.
Its reindex is the native ordered tail, and the actual finite original prefix
is the corresponding native partial sum. Prefix length k belongs to N, exactly
the source nonnegative integer condition. Positive k uses those two identities;
k=0 proves the prefix empty and the complete restriction equal to the original
function by function extensionality. Neither template-argument congruence nor
a function extension outside its domain is assumed. Both candidate and
existential-convergence directions are checked.

real_tail_series_translate is the actual n->a(n-shift) function on the complete
tail beginning at start+shift. The translated domain itself owns input validity.
Its native reindex agrees pointwise with the original native data, giving the
same candidate for every integer shift, including negative shifts.

## Forward differences and general telescoping

real_tail_forward_difference constructs a(n)-a(n+1) on the original complete
tail. Successor membership is established before this construction. Its actual
native reindex is the difference of consecutive native input terms. Existing
native telescoping and the exact first-term identity give a(start)-L whenever
the original data tends to L. Source7.2.15 is the start0, limit0 specialization;
the general nonzero-limit formula is also verified.

Additional dependency edges: actual adjacent monotonicity -> native nonincrease;
exact parity/phase identities + existing alternating theorem -> original
alternating convergence; original zero test + actual absolute values -> the
reverse direction. Exact sum/scaled reindex -> series algebra. Actual restriction
+ prefix identity -> removal/restoration -> both convergence directions.
Actual translated reindex equality -> translation invariance. Actual forward
difference reindex + native telescoping -> the general source candidate.
These edges preserve the mathematical concepts and the source order.

## Full-section uses and rejection controls

Checks cover every31 theorem contract. Actual applications include the
alternating harmonic series with first term-1 and a proof of failure of absolute
convergence; an even negative start with actual alternating sum+1/3, compared
with signed geometric sum-1/3; prefix length3 value-3/8 and remaining tail1/24;
zero-prefix preservation; negative shift with unchanged sum and exact first
term; arbitrary real scaling including zero and sqrt(2); and nonzero-limit
u(n)=2+1/(n+1), whose forward differences sum to1 rather than u(0)=3.
The source zero-limit telescoping specialization is checked separately.

All51 controls reject without parse errors or termination. The monotonicity
control first proves its true nonnegative-magnitude premise, so its final
rejection specifically identifies the false decrease inequality. Other controls
cover missing zero limits, negative magnitudes, wrong sign/phase, prefix and
translation guards, missing convergence, incorrect restored/tail/scaled values,
and the incorrect nonzero-limit telescoping formula. Earlier core controls are
rerun under the complete module. The public source54, full importer137,
README63 and fresh no-wrapper applications93 are clean saved artifacts.

A separate clean25-statement consumer proves all12 general selected-sum
composition laws from their original convergence/limit hypotheses: addition,
real scaling, both prefix directions, translation and general telescoping.
Its prefix calculation publishes the finite prefix and both selected values
as real scalars before arithmetic. No extra convergence premise or native
repair is introduced.
