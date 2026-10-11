# Mathematical interfaces

This module presents selected pieces of a growing Analysis I development.
The exports in [litex.config](litex.config) are `naturals`, `maps`,
`finite_products` and `limits`. The first three are local source files;
`limits` reuses the existing public real-analysis file. There is one README
and one concept manual for this showcase as a whole.

## Induction

`naturals::power_two_lower_bound(n)` states `2^n >= n + 1` for `n N`.
The source shows the base and successor branches. Its domain includes zero.
The number system and exponentiation are builtin; no axiomatization or
construction of natural numbers is provided by this example.

## Maps and equal cardinality

`maps::is_injective_fn(S, T, f)` means equal function values imply equal inputs;
`maps::is_surjective_fn(S, T, f)` means every target has a preimage.
`maps::is_bijective_fn` combines these properties.
`maps::has_equal_cardinality(S, T)` asks for a bijective function from S to T.
Here S and T may be empty. These are mathematical predicates, not an assertion
that a bijection exists for all sets. They introduce no user axioms.

## Finite products

`finite_products::has_coordinate_values_in_family(n, U, X, f)` expresses
membership in the chosen factor at each index of `closed_range(1, n)`.
`n N+`, `U set`, `X fn(i closed_range(1,n)) power_set(U)` and
`f fn(i closed_range(1,n)) U` specify the domain and ambient carrier.

`finite_cartesian_product_choice_function_representation` compares the
explicit finite-sequence and function-space set builders; its premises give
those two represented sets. It proves set equality and constructs an
identity bijection using the map predicates above. The theorem does not
start with an arbitrary set carrying legacy product metadata.

`is_finite_cartesian_product_for_family` names the finite-sequence set-builder
representation. `is_in_infinite_cartesian_product` is coordinate membership
for a supplied function over an arbitrary index set; it does not prove that
such a function exists. `finite_index_product_agrees_with_chapter3_cartesian_product`
uses both predicates to establish equal cardinality for positive finite
indices. Its historical name refers to the source-book motivation; this
public module imports only the selected map predicates, not a Chapter3
manuscript or legacy tuple metadata interface.

These concepts progress from membership to set equality to a bijection.
Finite length zero, arbitrary infinite-product existence and choice are
outside the theorems supplied here.

## Sequence limits

The `limits` source uses `fn(index N+) R` as its sequence carrier.
`is_tail_close_to` gives the strict epsilon inequality after a positive index;
`has_eventual_closeness_to` asks for that index; `has_limit` quantifies over
positive epsilon. `is_convergent_sequence` asks for a limit.

`\constant_sequence<c>` is the named template with value c at every index.
`constant_sequence_has_limit` proves its limit is c. `sequence_limit_unique`
proves uniqueness, and `lim` is defined by that existence-and-uniqueness
result on convergent sequences. It is not a total selector for arbitrary
sequences. Read the [actual limit source](../math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit)
for the complete declarations and proofs.

## Acceptance boundary

All selected source files and the reused limit dependency are included in the
strict module gate recorded in [verification.json](verification.json).
[STATUS.md](STATUS.md) separately records the remaining assumptions and
unfinished chapters in the broader local development. No abstract predicates,
user trust or axioms in that private development are imported into this module.
