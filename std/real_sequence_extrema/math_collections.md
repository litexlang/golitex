# Sequence extrema dependencies and source correspondence

Source 6.3.1 uses native fn_range on the complete original integer tail and
existing extended_set_supremum / extended_set_infimum. The actual start value
witness proves nonemptiness; there is no silent change of index domain.
One-sided finite bounds place the relevant extremum between two real values;
endpoint exclusions prove real membership.

Source 6.3.6 obtains bounds, leastness/greatestness and strict approach for all
extended comparison values. The general extended_sequence_extrema set-level strict approach proof is an ordinary
contradiction from leastness/greatestness and total order; native fn_preimage
extracts a witness on the exact original sequence domain. Both infinite extrema
and unattained finite extrema remain in scope.

Source 6.3.8 first derives natural-offset and pairwise monotonicity from the
adjacent definition. The induction supplies original-domain membership and
explicit real membership of each successor value before comparison. A strict
approach point within epsilon/2 and pairwise monotonicity prove the source
closed-epsilon limit directly. The decreasing proof is dual. Exact real-witness
and selected-limit corollaries identify the original extremum without adding a
convergence or finite-extremum premise. Native real_sequences supplies the
converse boundedness implication and guarded selection.

Source 6.3.10 is checked reuse of real_series: an actual q^k native sequence
and the factor q^(start-1) give q^(start+k-1). The same-value transport theorem
proves the source q^n limit on every integer tail, including negative starts.
The separate consumer keeps this dependency outside the generic extrema module.

Independent full-domain imports check all 28 public theorem contracts. The
complete reciprocal README runs first in its fresh importer and as a standalone
saved file. Actual constant tails with a negative start, n and -n on n>=-3,
finite/infinite strict approach values and false/domain controls exercise the
interfaces. A separate fresh infinite-extrema consumer copies none of the 28
generic contract wrappers. Source/executable hashes and full receipts remain
under experiments/std-library-development.

Any future general evidence composition or goal-formation improvement belongs
to shared verify. The checked source routes here use explicit memberships,
existing public constructions and real witnesses; no native change, new axiom,
trust, changed number model or overloaded public operation is introduced.
