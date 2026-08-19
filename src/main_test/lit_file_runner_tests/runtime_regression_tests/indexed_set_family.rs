use super::*;

fn run(source: &str, name: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(name);
    let (stmt_results, runtime_error) = run_source_code(source, &mut runtime);
    let (succeeded, output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    (succeeded, output)
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
                output.contains("UnknownError"),
                "the well-defined equality should be rejected during verification:\n{output}"
            );
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
