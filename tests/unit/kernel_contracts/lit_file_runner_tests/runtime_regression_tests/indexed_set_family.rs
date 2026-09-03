use super::*;
use crate::test_support::execute_source;

fn run(source: &str, name: &str) -> (bool, String) {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source(name);
    let (stmt_results, runtime_error) = execute_source(source, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    (succeeded, output)
}

fn assert_unknown_at_target(
    succeeded: bool,
    output: &str,
    target_fragment: &str,
    boundary_description: &str,
) {
    assert!(
        !succeeded && output.contains("unknown_error"),
        "{boundary_description}:\n{output}"
    );
    assert!(
        output.contains(target_fragment),
        "the rejection must occur at the intended target `{target_fragment}`, not in its prefix:\n{output}"
    );
}

#[test]
fn indexed_set_family_operators_cover_membership_carrier_and_empty_domain() {
    let source = r#"
have fn family(k {1}) power_set(N) = {k}
family(1) = {1}
1 $in {1}
1 $in family(1)

1 $in index_union({1}, N, family)
1 $in index_intersect({1}, N, family)
index_union({1}, N, family) $in power_set(N)
index_intersect({1}, N, family) $in power_set(N)
exist k {1} st {1 $in family(k)}
forall k {1}:
    1 $in family(k)

index_union({1}, N, family) = big_union(fn_range(family))
index_intersect({1}, N, family) = big_intersect(fn_range(family))

have fn cases_family(k {1, 2, 3}) power_set(N) by cases:
    case k = 1: {2, 3}
    case k = 2: {3, 4}
    case k = 3: {4, 5}
cases_family(1) = {2, 3}
2 $in {2, 3}
2 $in cases_family(1)
2 $in index_union({1, 2, 3}, N, cases_family)

sketch:
    have symbolic_index_set set
    have fn symbolic_family(symbolic_index symbolic_index_set) power_set(N) = {1}
    trust forall arbitrary_index symbolic_index_set:
        1 $in symbolic_family(arbitrary_index)
    1 $in index_intersect(symbolic_index_set, N, symbolic_family)

have fn empty_family(k {}) power_set(N) = {}
1 $in index_intersect({}, N, empty_family)
index_union({}, N, empty_family) = {}
index_intersect({}, N, empty_family) = N
"#;
    let (succeeded, output) = run(source, "indexed_set_family_positive");
    assert!(succeeded, "indexed set-family contract failed:\n{output}");
}

#[test]
fn indexed_set_family_domain_union_decomposes_by_exact_restrictions() {
    run_with_large_stack(
        "indexed_set_family_domain_union_decomposes_by_exact_restrictions",
        || {
            let source = r#"
have fn family(index union({1}, {2})) power_set(N) = {1}

index_union(union({1}, {2}), N, family) = union(index_union({1}, N, fn(left_index {1}) power_set(N) {family(left_index)}), index_union({2}, N, fn(right_index {2}) power_set(N) {family(right_index)}))
index_intersect(union({1}, {2}), N, family) = intersect(index_intersect({1}, N, fn(left_index {1}) power_set(N) {family(left_index)}), index_intersect({2}, N, fn(right_index {2}) power_set(N) {family(right_index)}))

have fn empty_branch_family(index union({}, {1})) power_set(N) = {1}
index_union(union({}, {1}), N, empty_branch_family) = union(index_union({}, N, fn(empty_index {}) power_set(N) {empty_branch_family(empty_index)}), index_union({1}, N, fn(right_index {1}) power_set(N) {empty_branch_family(right_index)}))
index_intersect(union({}, {1}), N, empty_branch_family) = intersect(index_intersect({}, N, fn(empty_index {}) power_set(N) {empty_branch_family(empty_index)}), index_intersect({1}, N, fn(right_index {1}) power_set(N) {empty_branch_family(right_index)}))
"#;
            let (succeeded, output) = run(source, "indexed_set_family_domain_union_positive");
            assert!(
                succeeded,
                "indexed-family domain-union decomposition failed:\n{output}"
            );
            assert!(
                output.contains("index_union over a union index domain decomposes into a union"),
                "indexed-union decomposition should expose its builtin provenance:\n{output}"
            );
            assert!(
                output.contains(
                    "index_intersect over a union index domain decomposes into an intersection"
                ),
                "indexed-intersection decomposition should expose its builtin provenance:\n{output}"
            );

            let wrong_restriction = r#"
have fn family(index union({1}, {2})) power_set(N) = {1}

index_union(union({1}, {2}), N, family) = union(index_union({1}, N, fn(left_index {1}) power_set(N) {{}}), index_union({2}, N, fn(right_index {2}) power_set(N) {family(right_index)}))
"#;
            let (succeeded, output) = run(
                wrong_restriction,
                "indexed_set_family_domain_union_wrong_restriction",
            );
            assert!(
                !succeeded,
                "a branch that is not the literal family restriction must be rejected:\n{output}"
            );
            assert!(
                output.contains("unknown_error"),
                "the well-defined equality should be rejected during verification:\n{output}"
            );
        },
    );
}

#[test]
fn indexed_set_family_phase_one_leaf_rules_cover_core_domain_and_order_calculus() {
    run_with_large_stack(
        "indexed_set_family_phase_one_leaf_rules_cover_core_domain_and_order_calculus",
        || {
            let source = r#"
have fn singleton_family(k {1}) power_set(N) = {1, 2}
singleton_family(1) = {1, 2}
index_union({1}, N, singleton_family) = singleton_family(1)
index_intersect({1}, N, singleton_family) = singleton_family(1)
index_union({1}, N, fn(k {1}) power_set(N) {{k}}) = {1}
index_intersect({1}, N, fn(k {1}) power_set(N) {{k}}) = {1}
index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {{2}}) = {2}
index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {{2}}) = {2}

have fn small(k {1, 2}) power_set(N) = {1}
small(1) $subset index_union({1, 2}, N, small)
index_intersect({1, 2}, N, small) $subset small(2)

forall k {1, 2}:
    small(k) $subset N
index_union({1, 2}, N, small) $subset index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {N})
index_intersect({1, 2}, N, small) $subset index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {N})

forall k {1, 2}:
    small(k) = {1}
index_union({1, 2}, N, small) = index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {{1}})
index_intersect({1, 2}, N, small) = index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {{1}})

index_union({1, 2}, N, small) $subset N
{} $subset N
forall k {1, 2}:
    {} $subset small(k)
{} $subset index_intersect({1, 2}, N, small)

{1} $subset {1, 2}
index_union({1}, N, fn(k {1}) power_set(N) {small(k)}) $subset index_union({1, 2}, N, small)
index_intersect({1, 2}, N, small) $subset index_intersect({1}, N, fn(k {1}) power_set(N) {small(k)})

have fn partition_family(k {1, 2}) power_set(N) = {1}
index_union({1, 2}, N, partition_family) = union(index_union(set_minus({1, 2}, {2}), N, fn(k set_minus({1, 2}, {2})) power_set(N) {partition_family(k)}), index_union(intersect({1, 2}, {2}), N, fn(k intersect({1, 2}, {2})) power_set(N) {partition_family(k)}))
index_intersect({1, 2}, N, partition_family) = intersect(index_intersect(set_minus({1, 2}, {2}), N, fn(k set_minus({1, 2}, {2})) power_set(N) {partition_family(k)}), index_intersect(intersect({1, 2}, {2}), N, fn(k intersect({1, 2}, {2})) power_set(N) {partition_family(k)}))

index_union({1, 2}, N, partition_family) = union(index_union(set_minus({1, 2}, {2}), N, fn(k set_minus({1, 2}, {2})) power_set(N) {partition_family(k)}), partition_family(2))
index_intersect({1, 2}, N, partition_family) = intersect(index_intersect(set_minus({1, 2}, {2}), N, fn(k set_minus({1, 2}, {2})) power_set(N) {partition_family(k)}), partition_family(2))

have D set
have E set
have fn common(k union(D, E)) power_set(N) = {1}
index_union(intersect(D, E), N, fn(k intersect(D, E)) power_set(N) {common(k)}) $subset intersect(index_union(D, N, fn(k D) power_set(N) {common(k)}), index_union(E, N, fn(k E) power_set(N) {common(k)}))
union(index_intersect(D, N, fn(k D) power_set(N) {common(k)}), index_intersect(E, N, fn(k E) power_set(N) {common(k)})) $subset index_intersect(intersect(D, E), N, fn(k intersect(D, E)) power_set(N) {common(k)})
set_minus(index_union(D, N, fn(k D) power_set(N) {common(k)}), index_union(E, N, fn(k E) power_set(N) {common(k)})) = set_minus(index_union(set_minus(D, E), N, fn(k set_minus(D, E)) power_set(N) {common(k)}), index_union(E, N, fn(k E) power_set(N) {common(k)}))
set_minus(index_intersect(D, N, fn(k D) power_set(N) {common(k)}), index_intersect(E, N, fn(k E) power_set(N) {common(k)})) = set_minus(index_intersect(D, N, fn(k D) power_set(N) {common(k)}), index_intersect(set_minus(E, D), N, fn(k set_minus(E, D)) power_set(N) {common(k)}))
"#;
            let (succeeded, output) = run(source, "indexed_set_family_phase_one_positive");
            assert!(
                succeeded,
                "indexed-family phase-one leaf rules failed:\n{output}"
            );
            for provenance in [
                "indexed family over a singleton equals its selected fiber",
                "nonempty indexed constant family equals its constant value",
                "selected fiber is contained in indexed union",
                "indexed intersection is contained in a selected fiber",
                "indexed-family extensionality from pointwise equality",
                "indexed-family monotonicity from pointwise subset",
                "indexed union is contained in a common pointwise upper bound",
                "common lower bound is contained in indexed intersection",
                "indexed union is monotone in its index domain",
                "indexed intersection is antitone in its index domain",
                "indexed family decomposes over a domain partition",
                "indexed family peels a selected singleton from its domain",
                "indexed family domain-intersection inclusion",
                "indexed-family domain difference retains the result-side set difference",
            ] {
                assert!(
                    output.contains(provenance),
                    "missing indexed-family provenance `{provenance}`:\n{output}"
                );
            }
        },
    );
}

#[test]
fn indexed_set_family_phase_one_leaf_rules_reject_missing_premises_and_false_strengthenings() {
    run_with_large_stack(
        "indexed_set_family_phase_one_leaf_rules_reject_missing_premises_and_false_strengthenings",
        || {
            let missing_nonempty = r#"
have D set
index_union(D, N, fn(k D) power_set(N) {{1}}) = {1}
"#;
            let (succeeded, output) = run(missing_nonempty, "indexed_constant_missing_nonempty");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "constant-family equality must require a nonempty index domain:\n{output}"
            );

            let missing_pointwise = r#"
have fn left_family(k {1}) power_set(N) = {1}
have fn right_family(k {1}) power_set(N) = {2}
index_union({1}, N, left_family) = index_union({1}, N, right_family)
"#;
            let (succeeded, output) =
                run(missing_pointwise, "indexed_extensionality_missing_forall");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "extensionality must require the stored pointwise equality:\n{output}"
            );

            let false_domain_subtraction = r#"
have D set
have E set
have fn common(k union(D, E)) power_set(N) = {1}
index_union(set_minus(D, E), N, fn(k set_minus(D, E)) power_set(N) {common(k)}) = set_minus(index_union(D, N, fn(k D) power_set(N) {common(k)}), index_union(E, N, fn(k E) power_set(N) {common(k)}))
"#;
            let (succeeded, output) = run(
                false_domain_subtraction,
                "indexed_false_domain_subtraction_equality",
            );
            assert!(
                !succeeded && output.contains("unknown_error"),
                "domain subtraction must not be strengthened to result subtraction:\n{output}"
            );

            let wrong_partition_restriction = r#"
have fn family(k {1, 2}) power_set(N) = {1}
index_union({1, 2}, N, family) = union(index_union(set_minus({1, 2}, {2}), N, fn(k set_minus({1, 2}, {2})) power_set(N) {{}}), index_union(intersect({1, 2}, {2}), N, fn(k intersect({1, 2}, {2})) power_set(N) {family(k)}))
"#;
            let (succeeded, output) = run(
                wrong_partition_restriction,
                "indexed_partition_wrong_restriction",
            );
            assert!(
                !succeeded && output.contains("unknown_error"),
                "partition branches must remain literal restrictions:\n{output}"
            );
        },
    );
}

#[test]
fn indexed_set_family_premise_sensitive_leaf_rules_reject_absent_cached_facts() {
    run_with_large_stack(
        "indexed_set_family_premise_sensitive_leaf_rules_reject_absent_cached_facts",
        || {
            let missing_pointwise_subset = r#"
have left_family fn(k {1, 2}) power_set(N)
have right_family fn(k {1, 2}) power_set(N)
index_union({1, 2}, N, left_family) $subset index_union({1, 2}, N, right_family)
"#;
            let (succeeded, output) = run(
                missing_pointwise_subset,
                "indexed_monotonicity_missing_pointwise_subset",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "index_union({1, 2}, N, left_family) $subset index_union",
                "family monotonicity must consume a stored pointwise subset",
            );

            let missing_common_upper_bound = r#"
have family fn(k {1, 2}) power_set(N)
index_union({1, 2}, N, family) $subset {1}
"#;
            let (succeeded, output) = run(
                missing_common_upper_bound,
                "indexed_union_missing_common_upper_bound",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "index_union({1, 2}, N, family) $subset {1}",
                "indexed-union upper bounds must consume the stored forall premise",
            );

            let missing_common_lower_bound = r#"
have family fn(k {1, 2}) power_set(N)
{1} $subset index_intersect({1, 2}, N, family)
"#;
            let (succeeded, output) = run(
                missing_common_lower_bound,
                "indexed_intersection_missing_common_lower_bound",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "{1} $subset index_intersect({1, 2}, N, family)",
                "indexed-intersection lower bounds must consume the stored forall premise",
            );

            let missing_nonempty_fiber = r#"
have D nonempty_set
have family fn(k D) power_set(N)
$is_nonempty_set(index_union(D, N, family))
"#;
            let (succeeded, output) = run(
                missing_nonempty_fiber,
                "indexed_union_missing_nonempty_fiber",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "$is_nonempty_set(index_union(D, N, family))",
                "a nonempty index set alone must not make its indexed union nonempty",
            );

            let missing_pointwise_finiteness = r#"
have family fn(k {1, 2}) power_set(N)
$is_finite_set(index_union({1, 2}, N, family))
"#;
            let (succeeded, output) = run(
                missing_pointwise_finiteness,
                "indexed_union_missing_pointwise_finiteness",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "$is_finite_set(index_union({1, 2}, N, family))",
                "a finite domain alone must not make an indexed union finite",
            );

            let missing_domain_finiteness = r#"
have D set
forall k D:
    $is_finite_set({1})
$is_finite_set(index_union(D, N, fn(k D) power_set(N) {{1}}))
"#;
            let (succeeded, output) = run(
                missing_domain_finiteness,
                "indexed_union_missing_domain_finiteness",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "$is_finite_set(index_union(D, N",
                "finite fibers alone must not make an arbitrary indexed union finite",
            );

            let missing_finite_intersection_source = r#"
have D nonempty_set
have family fn(k D) power_set(N)
$is_finite_set(index_intersect(D, N, family))
"#;
            let (succeeded, output) = run(
                missing_finite_intersection_source,
                "indexed_intersection_missing_finite_source",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "$is_finite_set(index_intersect(D, N, family))",
                "a nonempty domain without a finite fiber must not make the intersection finite",
            );
        },
    );
}

#[test]
fn indexed_set_family_phase_two_leaf_rules_cover_ordinary_set_operations() {
    run_with_large_stack(
        "indexed_set_family_phase_two_leaf_rules_cover_ordinary_set_operations",
        || {
            let source = r#"
have fn A(k {1, 2}) power_set(N) = {1}
have fn B(k {1, 2}) power_set(N) = {2}

set_minus(N, index_intersect({1, 2}, N, A)) = index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(N, A(k))})
set_minus(N, index_union({1, 2}, N, A)) = index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(N, A(k))})

intersect({1, 2}, index_union({1, 2}, N, A)) = index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {intersect(A(k), {1, 2})})
intersect(index_intersect({1, 2}, N, A), {1, 2}) = index_intersect({1, 2}, intersect(N, {1, 2}), fn(k {1, 2}) power_set(intersect(N, {1, 2})) {intersect({1, 2}, A(k))})
union({1, 2}, index_intersect({1, 2}, N, A)) = index_intersect({1, 2}, union({1, 2}, N), fn(k {1, 2}) power_set(union({1, 2}, N)) {union(A(k), {1, 2})})
union(index_union({1, 2}, N, A), {1, 2}) = index_union({1, 2}, union(N, {1, 2}), fn(k {1, 2}) power_set(union(N, {1, 2})) {union({1, 2}, A(k))})

set_minus(index_union({1, 2}, N, A), {2}) = index_union({1, 2}, set_minus(N, {2}), fn(k {1, 2}) power_set(set_minus(N, {2})) {set_minus(A(k), {2})})
set_minus(index_intersect({1, 2}, N, A), {2}) = index_intersect({1, 2}, set_minus(N, {2}), fn(k {1, 2}) power_set(set_minus(N, {2})) {set_minus(A(k), {2})})
set_minus({1, 2}, index_union({1, 2}, N, A)) = index_intersect({1, 2}, {1, 2}, fn(k {1, 2}) power_set({1, 2}) {set_minus({1, 2}, A(k))})
set_minus(R, index_intersect({1, 2}, N, A)) = union(set_minus(R, N), index_union({1, 2}, R, fn(k {1, 2}) power_set(R) {set_minus(R, A(k))}))
{1, 2} $subset N
set_minus({1, 2}, index_intersect({1, 2}, N, A)) = index_union({1, 2}, {1, 2}, fn(k {1, 2}) power_set({1, 2}) {set_minus({1, 2}, A(k))})

index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {union(A(k), B(k))}) = union(index_union({1, 2}, N, A), index_union({1, 2}, N, B))
index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {intersect(A(k), B(k))}) = intersect(index_intersect({1, 2}, N, A), index_intersect({1, 2}, N, B))
index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(A(k), B(k))}) = set_minus(index_intersect({1, 2}, N, A), index_union({1, 2}, N, B))

index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {intersect(A(k), B(k))}) $subset intersect(index_union({1, 2}, N, A), index_union({1, 2}, N, B))
union(index_intersect({1, 2}, N, A), index_intersect({1, 2}, N, B)) $subset index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {union(A(k), B(k))})
set_minus(index_union({1, 2}, N, A), index_union({1, 2}, N, B)) $subset index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(A(k), B(k))})
index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(A(k), B(k))}) $subset set_minus(index_union({1, 2}, N, A), index_intersect({1, 2}, N, B))

have fn empty_A(k {}) power_set(N) = {}
set_minus(N, index_intersect({}, N, empty_A)) = index_union({}, N, fn(k {}) power_set(N) {set_minus(N, empty_A(k))})
set_minus(N, index_union({}, N, empty_A)) = index_intersect({}, N, fn(k {}) power_set(N) {set_minus(N, empty_A(k))})
intersect({1}, index_union({}, N, empty_A)) = index_union({}, N, fn(k {}) power_set(N) {intersect({1}, empty_A(k))})
intersect({1}, index_intersect({}, N, empty_A)) = index_intersect({}, intersect({1}, N), fn(k {}) power_set(intersect({1}, N)) {intersect({1}, empty_A(k))})
union({1}, index_intersect({}, N, empty_A)) = index_intersect({}, union({1}, N), fn(k {}) power_set(union({1}, N)) {union({1}, empty_A(k))})
set_minus(index_union({}, N, empty_A), {1}) = index_union({}, set_minus(N, {1}), fn(k {}) power_set(set_minus(N, {1})) {set_minus(empty_A(k), {1})})
set_minus(index_intersect({}, N, empty_A), {1}) = index_intersect({}, set_minus(N, {1}), fn(k {}) power_set(set_minus(N, {1})) {set_minus(empty_A(k), {1})})
set_minus({1}, index_union({}, N, empty_A)) = index_intersect({}, {1}, fn(k {}) power_set({1}) {set_minus({1}, empty_A(k))})
set_minus({1}, index_intersect({}, N, empty_A)) = union(set_minus({1}, N), index_union({}, {1}, fn(k {}) power_set({1}) {set_minus({1}, empty_A(k))}))
"#;
            let (succeeded, output) = run(source, "indexed_set_family_phase_two_positive");
            assert!(
                succeeded,
                "indexed-family phase-two set-operation rules failed:\n{output}"
            );
            for provenance in [
                "indexed-family De Morgan law",
                "external union/intersection distributes over indexed family",
                "external set difference distributes over indexed family",
                "pointwise set operation over indexed families",
                "pointwise intersection indexed-union inclusion",
                "pointwise union indexed-intersection inclusion",
                "lower mixed set-difference indexed-union inclusion",
                "upper mixed set-difference indexed-union inclusion",
            ] {
                assert!(
                    output.contains(provenance),
                    "missing phase-two provenance `{provenance}`:\n{output}"
                );
            }
        },
    );
}

#[test]
fn indexed_set_family_phase_two_rejects_missing_corrections_premises_and_wrong_bodies() {
    run_with_large_stack(
        "indexed_set_family_phase_two_rejects_missing_corrections_premises_and_wrong_bodies",
        || {
            let missing_nonempty = r#"
have D set
have fn A(k D) power_set(N) = {1}
union({1}, index_union(D, N, A)) = index_union(D, union({1}, N), fn(k D) power_set(union({1}, N)) {union({1}, A(k))})
"#;
            let (succeeded, output) =
                run(missing_nonempty, "indexed_external_union_missing_nonempty");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "external union must retain its nonempty-domain premise:\n{output}"
            );

            let empty_external_union = r#"
have fn empty_A(k {}) power_set(N) = {}
union({1}, index_union({}, N, empty_A)) = index_union({}, union({1}, N), fn(k {}) power_set(union({1}, N)) {union({1}, empty_A(k))})
"#;
            let (succeeded, output) =
                run(empty_external_union, "indexed_external_union_empty_domain");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "external union over an empty index set must remain rejected:\n{output}"
            );

            let missing_correction = r#"
have fn A(k {1}) power_set(N) = {1}
set_minus(R, index_intersect({1}, N, A)) = index_union({1}, R, fn(k {1}) power_set(R) {set_minus(R, A(k))})
"#;
            let (succeeded, output) =
                run(missing_correction, "indexed_set_minus_missing_correction");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "C set_minus M must retain C set_minus X unless C subset X is known:\n{output}"
            );

            let wrong_body = r#"
have fn A(k {1}) power_set(N) = {1}
set_minus(N, index_union({1}, N, A)) = index_intersect({1}, N, fn(k {1}) power_set(N) {set_minus(A(k), N)})
"#;
            let (succeeded, output) = run(wrong_body, "indexed_demorgan_wrong_body");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "a merely well-typed transformed body must not match De Morgan:\n{output}"
            );

            let false_pointwise_equality = r#"
have fn A(k {1, 2}) power_set(N) = {1}
have fn B(k {1, 2}) power_set(N) = {2}
index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {intersect(A(k), B(k))}) = intersect(index_union({1, 2}, N, A), index_union({1, 2}, N, B))
"#;
            let (succeeded, output) = run(
                false_pointwise_equality,
                "indexed_false_pointwise_intersection_equality",
            );
            assert!(
                !succeeded && output.contains("unknown_error"),
                "pointwise intersection under indexed union is only an inclusion:\n{output}"
            );
        },
    );
}

#[test]
fn indexed_set_family_equality_leaf_rules_match_both_orientations() {
    run_with_large_stack(
        "indexed_set_family_equality_leaf_rules_match_both_orientations",
        || {
            let source = r#"
have fn singleton_family(k {1}) power_set(N) = {1}
singleton_family(1) = index_union({1}, N, singleton_family)

have fn A(k {1, 2}) power_set(N) = {1}
index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(N, A(k))}) = set_minus(N, index_union({1, 2}, N, A))

set_minus(cart(Z, N), cart(Z, {1})) = cart(Z, set_minus(N, {1}))
"#;
            let (succeeded, output) = run(source, "indexed_equality_reverse_orientations");
            assert!(
                succeeded,
                "indexed-family equality leaves must match either stated orientation:\n{output}"
            );
            for provenance in [
                "indexed family over a singleton equals its selected fiber",
                "indexed-family De Morgan law",
                "Cartesian product preserves set difference in one coordinate",
            ] {
                assert!(
                    output.contains(provenance),
                    "missing reversed-orientation provenance `{provenance}`:\n{output}"
                );
            }
        },
    );
}

#[test]
fn indexed_set_family_false_equality_boundaries_remain_rejected() {
    run_with_large_stack(
        "indexed_set_family_false_equality_boundaries_remain_rejected",
        || {
            let false_domain_intersection_union = r#"
have fn common(k union({1}, {2})) power_set(N) = {1}
index_union(intersect({1}, {2}), N, fn(k intersect({1}, {2})) power_set(N) {common(k)}) = intersect(index_union({1}, N, fn(k {1}) power_set(N) {common(k)}), index_union({2}, N, fn(k {2}) power_set(N) {common(k)}))
"#;
            let (succeeded, output) = run(
                false_domain_intersection_union,
                "indexed_false_domain_intersection_union_equality",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "index_union(intersect({1}, {2})",
                "domain intersection must not become intersection of indexed unions",
            );

            let false_domain_intersection_intersect = r#"
have fn common(k union({1}, {2})) power_set(N) = {1}
index_intersect(intersect({1}, {2}), N, fn(k intersect({1}, {2})) power_set(N) {common(k)}) = union(index_intersect({1}, N, fn(k {1}) power_set(N) {common(k)}), index_intersect({2}, N, fn(k {2}) power_set(N) {common(k)}))
"#;
            let (succeeded, output) = run(
                false_domain_intersection_intersect,
                "indexed_false_domain_intersection_intersect_equality",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "index_intersect(intersect({1}, {2})",
                "domain intersection must not become union of indexed intersections",
            );

            let false_pointwise_union_intersection_equality = r#"
have fn A(k {1, 2}) power_set(N) by cases:
    case k = 1: {1}
    case k = 2: {2}
have fn B(k {1, 2}) power_set(N) by cases:
    case k = 1: {2}
    case k = 2: {1}
union(index_intersect({1, 2}, N, A), index_intersect({1, 2}, N, B)) = index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {union(A(k), B(k))})
"#;
            let (succeeded, output) = run(
                false_pointwise_union_intersection_equality,
                "indexed_false_pointwise_union_intersection_equality",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "union(index_intersect({1, 2}, N, A), index_intersect",
                "pointwise union under indexed intersection is only an inclusion",
            );

            let false_lower_mixed_difference_equality = r#"
have fn A(k {1, 2}) power_set(N) by cases:
    case k = 1: {1}
    case k = 2: {}
have fn B(k {1, 2}) power_set(N) by cases:
    case k = 1: {}
    case k = 2: {1}
set_minus(index_union({1, 2}, N, A), index_union({1, 2}, N, B)) = index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(A(k), B(k))})
"#;
            let (succeeded, output) = run(
                false_lower_mixed_difference_equality,
                "indexed_false_lower_mixed_difference_equality",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "set_minus(index_union({1, 2}, N, A), index_union",
                "the lower mixed set-difference law is only an inclusion",
            );

            let false_upper_mixed_difference_equality = r#"
have fn A(k {1, 2}) power_set(N) by cases:
    case k = 1: {1}
    case k = 2: {}
have fn B(k {1, 2}) power_set(N) by cases:
    case k = 1: {1}
    case k = 2: {}
index_union({1, 2}, N, fn(k {1, 2}) power_set(N) {set_minus(A(k), B(k))}) = set_minus(index_union({1, 2}, N, A), index_intersect({1, 2}, N, B))
"#;
            let (succeeded, output) = run(
                false_upper_mixed_difference_equality,
                "indexed_false_upper_mixed_difference_equality",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "set_minus(index_union({1, 2}, N, A), index_intersect",
                "the upper mixed set-difference law is only an inclusion",
            );

            let false_general_cart_domain_split = r#"
have fn factors(k union({1}, {2})) power_set(N) = {1}
general_cart(union({1}, {2}), power_set(N), factors) = cart(general_cart({1}, power_set(N), fn(k {1}) power_set(N) {factors(k)}), general_cart({2}, power_set(N), fn(k {2}) power_set(N) {factors(k)}))
"#;
            let (succeeded, output) = run(
                false_general_cart_domain_split,
                "indexed_false_general_cart_domain_split",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "general_cart(union({1}, {2})",
                "general_cart domain splitting must not be literal Cartesian equality",
            );

            let nonempty_fibers_without_common_member = r#"
forall k {1, 2}:
    $is_nonempty_set({k})
$is_nonempty_set(index_intersect({1, 2}, {1, 2}, fn(k {1, 2}) power_set({1, 2}) {{k}}))
"#;
            let (succeeded, output) = run(
                nonempty_fibers_without_common_member,
                "indexed_nonempty_fibers_without_common_member",
            );
            assert_unknown_at_target(
                succeeded,
                &output,
                "$is_nonempty_set(index_intersect({1, 2}, {1, 2}",
                "nonempty fibers must not imply a nonempty common intersection",
            );
        },
    );
}

#[test]
fn indexed_set_family_phase_three_leaf_adapters_cover_ranges_powersets_and_products() {
    run_with_large_stack(
        "indexed_set_family_phase_three_leaf_adapters_cover_ranges_powersets_and_products",
        || {
            let source = r#"
have fn f(k union({1}, {2})) N = 1
index_union(union({1}, {2}), N, fn(k union({1}, {2})) power_set(N) {{f(k)}}) = fn_range(f)
fn_range(f) = union(fn_range(fn(k {1}) N {f(k)}), fn_range(fn(k {2}) N {f(k)}))

have fn A(k {1, 2}) power_set(N) = {1}
have fn B(k {1, 2}) power_set(N) = {2}
power_set(index_intersect({1, 2}, N, A)) = index_intersect({1, 2}, power_set(N), fn(k {1, 2}) power_set(power_set(N)) {power_set(A(k))})
index_union({1, 2}, power_set(N), fn(k {1, 2}) power_set(power_set(N)) {power_set(A(k))}) $subset power_set(index_union({1, 2}, N, A))

cart(Z, index_union({1, 2}, N, A)) = index_union({1, 2}, cart(Z, N), fn(k {1, 2}) power_set(cart(Z, N)) {cart(Z, A(k))})
cart(Z, index_intersect({1, 2}, N, A)) = index_intersect({1, 2}, cart(Z, N), fn(k {1, 2}) power_set(cart(Z, N)) {cart(Z, A(k))})
cart(index_union({1, 2}, N, A), Z) = index_union({1, 2}, cart(N, Z), fn(k {1, 2}) power_set(cart(N, Z)) {cart(A(k), Z)})
cart(index_intersect({1, 2}, N, A), Z) = index_intersect({1, 2}, cart(N, Z), fn(k {1, 2}) power_set(cart(N, Z)) {cart(A(k), Z)})
cart(Z, set_minus(N, {1})) = set_minus(cart(Z, N), cart(Z, {1}))
set_minus(cart(N, Z), cart({1}, Z)) = cart(set_minus(N, {1}), Z)

general_cart({1, 2}, power_set(N), fn(k {1, 2}) power_set(N) {intersect(A(k), B(k))}) = intersect(general_cart({1, 2}, power_set(N), A), general_cart({1, 2}, power_set(N), B))
union(general_cart({1, 2}, power_set(N), A), general_cart({1, 2}, power_set(N), B)) $subset general_cart({1, 2}, power_set(N), fn(k {1, 2}) power_set(N) {union(A(k), B(k))})
"#;
            let (succeeded, output) = run(source, "indexed_set_family_phase_three_positive");
            assert!(
                succeeded,
                "indexed-family phase-three adapters failed:\n{output}"
            );
            for provenance in [
                "indexed union of singleton fibers equals function range",
                "function range decomposes over a union domain",
                "power set commutes with indexed intersection",
                "indexed union of powersets is contained in powerset of union",
                "fixed-coordinate Cartesian product commutes with indexed family",
                "Cartesian product preserves set difference in one coordinate",
                "general Cartesian product preserves pointwise intersection",
                "general Cartesian product pointwise-union inclusion",
            ] {
                assert!(
                    output.contains(provenance),
                    "missing phase-three provenance `{provenance}`:\n{output}"
                );
            }
        },
    );
}

#[test]
fn indexed_set_family_phase_three_adapters_reject_wrong_and_strengthened_shapes() {
    run_with_large_stack(
        "indexed_set_family_phase_three_adapters_reject_wrong_and_strengthened_shapes",
        || {
            let wrong_singleton_body = r#"
have fn f(k {1}) N = 1
index_union({1}, N, fn(k {1}) power_set(N) {{2}}) = fn_range(f)
"#;
            let (succeeded, output) =
                run(wrong_singleton_body, "indexed_range_wrong_singleton_body");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "range adapter must match the literal singleton f(i):\n{output}"
            );

            let wrong_cart_difference_coordinate = r#"
cart(Z, set_minus(N, {1})) = set_minus(cart(Z, N), cart(Q, {1}))
"#;
            let (succeeded, output) = run(
                wrong_cart_difference_coordinate,
                "indexed_cart_difference_wrong_fixed_coordinate",
            );
            assert!(
                !succeeded && output.contains("unknown_error"),
                "Cartesian set difference must keep the other coordinate exact:\n{output}"
            );

            let false_powerset_equality = r#"
have fn A(k {1, 2}) power_set(N) = {1}
index_union({1, 2}, power_set(N), fn(k {1, 2}) power_set(power_set(N)) {power_set(A(k))}) = power_set(index_union({1, 2}, N, A))
"#;
            let (succeeded, output) =
                run(false_powerset_equality, "indexed_powerset_false_equality");
            assert!(
                !succeeded && output.contains("unknown_error"),
                "powerset over indexed union must remain an inclusion:\n{output}"
            );

            let false_general_cart_union_equality = r#"
have fn A(k {1, 2}) power_set(N) = {1}
have fn B(k {1, 2}) power_set(N) = {2}
union(general_cart({1, 2}, power_set(N), A), general_cart({1, 2}, power_set(N), B)) = general_cart({1, 2}, power_set(N), fn(k {1, 2}) power_set(N) {union(A(k), B(k))})
"#;
            let (succeeded, output) = run(
                false_general_cart_union_equality,
                "indexed_general_cart_false_union_equality",
            );
            assert!(
                !succeeded && output.contains("unknown_error"),
                "general_cart of pointwise unions must remain an inclusion:\n{output}"
            );
        },
    );
}

#[test]
fn indexed_set_family_phase_three_predicate_leaf_rules_cover_nonempty_and_finite_results() {
    run_with_large_stack(
        "indexed_set_family_phase_three_predicate_leaf_rules_cover_nonempty_and_finite_results",
        || {
            let source = r#"
witness exist k {1, 2} st {$is_nonempty_set({k})} from 1:
    $is_nonempty_set({1})
$is_nonempty_set(index_union({1, 2}, {1, 2}, fn(k {1, 2}) power_set({1, 2}) {{k}}))

$is_finite_set({1, 2})
forall k {1, 2}:
    $is_finite_set({k})
$is_finite_set(index_union({1, 2}, {1, 2}, fn(k {1, 2}) power_set({1, 2}) {{k}}))

have fn finite_ambient_family(k {1, 2}) power_set({1, 2}) = {1}
$is_finite_set(index_intersect({1, 2}, {1, 2}, finite_ambient_family))

witness exist k {1, 2} st {$is_finite_set({1})} from 1:
    $is_finite_set({1})
$is_finite_set(index_intersect({1, 2}, N, fn(k {1, 2}) power_set(N) {{1}}))
"#;
            let (succeeded, output) = run(source, "indexed_set_family_phase_three_predicates");
            assert!(
                succeeded,
                "indexed-family nonempty/finite leaf rules failed:\n{output}"
            );
            for provenance in [
                "indexed union is nonempty from an existing nonempty fiber",
                "indexed union is finite from finite domain and pointwise finite fibers",
                "indexed intersection is finite when its ambient set is finite",
                "nonempty indexed intersection is finite from one finite fiber",
            ] {
                assert!(
                    output.contains(provenance),
                    "missing predicate provenance `{provenance}`:\n{output}"
                );
            }
        },
    );
}

#[test]
fn indexed_set_family_operators_reject_wrong_family_signature() {
    let wrong_codomain = r#"
have fn family(k {1}) N = k
index_union({1}, N, family) $in power_set(N)
"#;
    let (succeeded, output) = run(wrong_codomain, "indexed_set_family_wrong_codomain");
    assert!(
        !succeeded,
        "a family returning elements instead of subsets must be rejected:\n{output}"
    );
    assert!(
        output.contains("failed to verify well-defined of index_union"),
        "the rejection should identify indexed-union well-definedness:\n{output}"
    );

    let wrong_domain = r#"
have fn family(k {1, 2}) power_set(N) = {1}
index_intersect({1}, N, family) $in power_set(N)
"#;
    let (succeeded, output) = run(wrong_domain, "indexed_set_family_wrong_domain");
    assert!(
        !succeeded,
        "a family with a different exact index domain must be rejected:\n{output}"
    );
    assert!(
        output.contains("failed to verify well-defined of index_intersect"),
        "the rejection should identify indexed-intersection well-definedness:\n{output}"
    );
}
