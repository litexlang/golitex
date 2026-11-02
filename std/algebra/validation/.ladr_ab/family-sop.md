# Finite subspace family sums

Status: modeling and authoring, 2026-10-31.

## Exact contract and dependencies

LADR 1.36, 1.40, 1.41 and 1.45 concern an arbitrary finite list of ambient
subspaces, not just a binary sum. Preserve supplied ambient operations and
allow zero subspaces and repeated summands. Permit length zero with sum {zero}
and vacuous uniqueness. Do not assume the ambient space is finite dimensional.

1. Reuse finite_span::linear_combination to define vector_list_sum with an
   all-one coefficient list. This is an ordinary V-valued function with exact
   finite_seq(V,n) input, not a new folding mechanism or native overload.
2. Prove empty/zero, termwise addition and scaling laws. Reuse existing traces,
   their uniqueness and linear-map preservation of combinations.
3. A subspace family is an actual finite_seq(power_set(V),m) satisfying the
   existing is_subspace relation at every index. A decomposition is an actual
   finite_seq(V,m) selecting its jth term from the jth subspace.
4. The sum is the set of values of vector_list_sum on these decompositions.
   Prove closure, summand inclusion and leastness.
5. Directness means unique decompositions. Prove its zero-decomposition
   criterion; retain existing binary direct_sum as a reuse bridge.

## Ownership and probes

Vector sum primitives belong in finite_span.lit; family relations and sets
belong in subspace_sums.lit after its existing dependencies. Existing structs,
native names and binary APIs remain unchanged. Prove general laws before
concrete probes. Immediate consumers must cover three summands, empty families,
zero summands and a repeated nonzero summand that is not direct.

Continue the current pinned Session (50223), whose accepted prefix includes
the algebra exports and the inverse consumer. Journal each top-level statement
and ordinary failure; do not restart or materialize incomplete proofs. Clean
source gates must demonstrate that no consumer-specific facts were needed.
