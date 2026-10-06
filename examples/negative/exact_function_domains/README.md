# Exact function-domain negative controls

Run each file with `target/release/litex -strict -f <file>`. Require a failed
run, successful setup statements and the failure phase in manifest.json.
The retired cart_dim case requires the explicit parser diagnostic after both
true empty-cart equalities; it is a syntax removal boundary, not a substitute
for the separate bare 2=3 rejection. None of these controls uses trust.

Positive partners are the native fn_set_member, exact_function_space_membership,
empty_parameter_domain and both_function_bodies tracers. The builtin theorem
unit gate executes this manifest and checks each original setup and failure.

The sequence carrier-alias, sequence return and sequence-space alias files
pair with `examples/infer/atomic/in_sequence_space_alias_expand.lit` and
`examples/wd/sequence_return_application.lit`. Their setup declarations must
succeed before the final out-of-range or callable-space application fails WD.

The empty_function_graph_nonempty, empty_function_graph_singleton_image and
guarded_empty_function_graph_nonempty controls require successful function
declarations followed by search_proof rejection. Their positive partner is
`examples/proof_nodes/equal/by_builtin_rule/function_empty_domain_graph.lit`.
An empty input domain has no graph entries, while its function space still
contains the empty function even when its return carrier is empty.

The recursive_return_space_nonempty and empty_nested_return_space_nonempty
controls reject cyclic existence and empty inner return spaces at search_proof.
The nested_finite_sequence_return_out_of_range declaration succeeds before
the final returned-function image fails WD at index 3. Positive partners are
`examples/proof_nodes/atomic/by_builtin_strategy/function_space_return_carrier_aliases.lit`
and `examples/proof_nodes/atomic/by_builtin_strategy/nested_sequence_space_nonempty.lit`.

The zero/one-cart controls distinguish the singleton empty function space from
the empty set, reject wrong complete length in default and native membership,
and reject out-of-range applications after successful member declarations.
The nonempty outer-function control keeps curry layers separate: an outer
domain R has graph entries even when every returned function has empty domain.
Positive partners are the empty graph identity, empty-domain space singleton,
cart_zero_one_membership and cart_zero_one_size tracers.

The finite_product controls pair with
`examples/proof_nodes/equal/by_builtin_rule/finite_product_exact_restrictions.lit`.
They reject changed callbacks/factors and nonfresh insertion at search_proof,
missing finiteness or an omitted callback input at well_defined, and assigning
the original union-domain function to the shorter function space at function_domain.
Every setup must pass; the failed target leaves stores/infers empty.

The cart_definition controls require the complete exact-domain set definition:
missing coordinates, reversed factors, wrong finite length and an infinite
domain all fail at search_proof. A diagonal set is not the full Cartesian
product even when its coordinate images cover both factors.
Their positive partner is
`examples/proof_nodes/equal/by_object_definition/cart_function_set_definition.lit`.

The tuple_equal controls pair with
`examples/stmt_nodes/release_and_expand/tuple_exact_function_extensionality.lit`.
Wrong complete length and an infinite source domain fail at function_domain;
wrong last values and only first-coordinate agreement fail at premise. The
setup and first-coordinate equality must succeed before the incomplete
extensionality claim is rejected.

The `guard_empty_domain_*` controls first prove the real exclusion lemma
`k<0 => not k>0`. Omitting the negative guard, reversing it, claiming a
singleton image of an empty graph, or treating a nonempty input domain's
empty-codomain space as `{()}` still fails at `search_proof`. All preceding
statements must succeed and the failed target must publish no facts. The
corresponding true graph/image/space and zero-length membership tracer is
[guarded_empty_function_domain.lit](../../proof_nodes/equal/by_builtin_rule/guarded_empty_function_domain.lit).

The empty_constructor controls pair with the guarded-empty positive tracer. Successful empty-domain constructors must not prove 0 in {} or permit an input. Nonempty and missing-guard constructors still fail body_in_return_set; undefined division fails body WD even under an empty carrier or excluded guards. Their manifest expected_constructor_stage is checked at the exact anonymous-constructor WD owner inside have_fn_equal, not by finding an unrelated nested proof label.

The `function_parameter_*` controls pair with
[function_value_parameter_application.lit](../../proof_nodes/equal/by_object_definition/by_fn_application/function_value_parameter_application.lit).
Their two declarations must succeed. Wrong complete lengths, input groups
and inner guards fail at `well_defined`; selecting the wrong coordinate value
fails at `search_proof`. The failed target publishes no stores or infers.

The retired_* controls cover tuple dimensions, construction projections, single/nested object brackets and both polarities of shape predicates. Each declaration prefix must succeed before the manifest-specified parser diagnostic. Their expected_prefix_count and expected_diagnostic are checked explicitly; new ordinary-call out-of-range negatives still reject at WD rather than borrowing these syntax errors.
