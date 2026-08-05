use super::*;
use std::path::Path;

#[test]
fn let_defines_an_untyped_object_and_stores_its_equality() {
    let source_code = r#"
let x = 1
x = 1
try:
    let y = x
    y = x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "let_defines_an_untyped_object_and_stores_its_equality",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "let should define a name and store its equality:\n{}",
        run_output
    );
    assert!(runtime.is_name_used_for_identifier("x"));
    assert!(run_output.contains("\"kind\": \"declare_object\""));
    assert!(run_output.contains("\"name\": \"x\""));
    assert!(run_output.contains("\"value\": \"1\""));
    assert!(run_output.contains("\"name\": \"x\",\n          \"value\": \"1\""));
    assert!(run_output.contains("\"fact\": \"x = 1\""));
}

#[test]
fn let_rejects_undefined_right_sides_duplicate_names_and_extra_values() {
    let cases = [
        ("self reference", "let x = x", "identifier `x` not defined"),
        (
            "undefined right side",
            "let x = missing",
            "identifier `missing` not defined",
        ),
        (
            "duplicate name",
            "let x = 1\nlet x = 2",
            "identifier `x` is already bound",
        ),
        (
            "extra value",
            "let x = 1, 2",
            "unexpected token after let value expression",
        ),
        (
            "template body",
            "template<s set>:\n    let x = s",
            "template body only supports `have` and `trust have` definition statements",
        ),
    ];

    for (label, source_code, expected_message) in cases {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(format!("let_{}", label).as_str());
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded, "{} should fail:\n{}", label, run_output);
        assert!(
            run_output.contains(expected_message),
            "{} should report `{}`:\n{}",
            label,
            expected_message,
            run_output
        );
    }
}

#[test]
fn let_object_definition_has_latex_output() {
    let output = to_latex_from_source("let x = 1", "let_object_definition_has_latex_output")
        .expect("let object definition should convert to LaTeX");

    assert!(output.contains(r"\mathrm{let}\ \mathit{x} = 1"));
}

#[test]
fn builtin_rules_do_not_add_unreviewed_full_verifier_calls() {
    let builtin_rules_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("verify")
        .join("verify_builtin_rules");
    let disallowed_calls = [
        "verify_fact_full(",
        "verify_atomic_fact(",
        "verify_forall_fact(",
        "verify_exist_or_and_chain_atomic_fact(",
        "verify_or_and_chain_atomic_fact(",
        "verify_atomic_fact_with_known_forall(",
        "verify_atomic_fact_using_builtin_or_prop_definition(",
        "verify_atomic_fact_with_strategy(",
        "UseContextVerifyState::new(",
    ];
    // Full verification is permitted only inside handlers reached explicitly
    // through `by thm`. Automatic builtin dispatch must stay atomic and must
    // not regain an unrestricted verifier through a new call site.
    let explicit_builtin_theorem_handlers = [
        "try_verify_in_fact_by_symbolic_cart",
        "verify_in_fact_in_general_cart_by_defining_facts",
        "verify_in_fact_in_set_builder_by_defining_facts",
        "verify_in_fact_by_struct_obj",
        "try_verify_tuple_equality_from_dim_and_projections",
        "try_verify_symbolic_tuple_equality_from_coordinates",
        "try_less_equal_sum_pointwise_on_same_integer_range",
        "try_less_equal_finite_set_sum_pointwise_on_same_set",
        "try_less_equal_finite_set_summand_nonnegative_sum",
        "verify_general_cart_nonempty_by_choice_explicit",
    ];
    let mut violations = Vec::new();
    let mut source_files = Vec::new();
    collect_rust_files_under_dir(&builtin_rules_dir, &mut source_files);
    for path in source_files {
        let content = fs::read_to_string(&path).expect("read verify_builtin_rules source file");
        for (line_index, line) in content.lines().enumerate() {
            for disallowed_call in disallowed_calls {
                if line.contains(disallowed_call) {
                    let enclosing_function = enclosing_rust_function_name(&content, line_index);
                    if enclosing_function.as_ref().is_some_and(|name| {
                        explicit_builtin_theorem_handlers.contains(&name.as_str())
                    }) {
                        continue;
                    }
                    violations.push(format!(
                        "{}:{} contains `{}` in {:?}",
                        path.display(),
                        line_index + 1,
                        disallowed_call,
                        enclosing_function,
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "builtin rules introduced unreviewed full-verifier calls:\n{}",
        violations.join("\n")
    );
}

fn enclosing_rust_function_name(source: &str, line_index: usize) -> Option<String> {
    let preceding_lines: Vec<_> = source.lines().take(line_index + 1).collect();
    preceding_lines.into_iter().rev().find_map(|line| {
        let trimmed = line.trim_start();
        let after_fn = ["fn ", "pub fn ", "pub(crate) fn ", "pub(super) fn "]
            .into_iter()
            .find_map(|prefix| trimmed.strip_prefix(prefix))?;
        Some(after_fn.split('(').next()?.trim().to_string())
    })
}

fn collect_rust_files_under_dir(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("read verify_builtin_rules directory") {
        let entry = entry.expect("read verify_builtin_rules entry");
        let path = entry.path();
        if path.is_dir() {
            collect_rust_files_under_dir(&path, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[test]
fn reversed_literal_integer_ranges_are_well_defined_empty_sets() {
    run_with_large_stack(
        "reversed_literal_integer_ranges_are_well_defined_empty_sets",
        || {
            let source_code = r#"
range(3, 2) = {}
closed_range(3, 2) = {}
finite_set_size(range(3, 2)) = 0
finite_set_size(closed_range(3, 2)) = 0

forall i1 range(3, 2):
    1 = 0

forall i1 closed_range(3, 2):
    1 = 0

by for:
    ? forall i1 range(3, 2) => {1 = 0}
by for:
    ? forall i1 closed_range(3, 2) => {1 = 0}
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "reversed_literal_integer_ranges_are_well_defined_empty_sets",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "reversed literal integer ranges should be empty and well-defined:\n{}",
                run_output
            );
            assert!(
                run_output.contains("forall over empty parameter set"),
                "reversed literal integer ranges should make forall vacuous:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn big_union_membership_has_builtin_intro_and_elim() {
    run_with_large_stack("big_union_membership_has_builtin_intro_and_elim", || {
        let source_code = r#"
thm tmp_big_union_intro_from_member:
    ? forall x set, F set, A set:
        A $in F
        x $in A
        =>:
            x $in big_union(F)
    x $in big_union(F)

thm tmp_big_union_intro_from_exist:
    ? forall x set, F set:
        exist A F st {x $in A}
        =>:
            x $in big_union(F)
    x $in big_union(F)

thm tmp_big_union_elim_to_exist:
    ? forall x set, F set:
        x $in big_union(F)
        =>:
            exist A F st {x $in A}
    exist A F st {x $in A}
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "big_union_membership_has_builtin_intro_and_elim",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "big_union_membership_has_builtin_intro_and_elim failed:\n{}",
            run_output
        );
    });
}

#[test]
fn have_tuple_and_have_cart_define_symbolic_coordinates() {
    run_with_large_stack(
        "have_tuple_and_have_cart_define_symbolic_coordinates",
        || {
            let source_code = r#"
have n N+ = 3
have tuple f for i1 <= n, f[i1] = i1
$is_tuple(f)
tuple_dim(f) = n
forall i1 closed_range(1, n):
    f[i1] = i1

have cart c for i1 <= n, proj(c, i1) = f[i1]
$is_set(c)
$is_cart(c)
cart_dim(c) = n
forall i1 closed_range(1, n):
    proj(c, i1) = f[i1]
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_tuple_and_have_cart_define_symbolic_coordinates",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have_tuple_and_have_cart_define_symbolic_coordinates failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"tuple definition\""));
            assert!(run_output.contains("\"type\": \"cart definition\""));
            assert!(run_output.contains("\"type\": \"universal fact\""));
        },
    );
}

#[test]
fn have_seq_finite_seq_and_matrix_define_indexed_entries() {
    run_with_large_stack(
        "have_seq_finite_seq_and_matrix_define_indexed_entries",
        || {
            let source_code = r#"
have seq s seq(N+) for i1, s(i1) = i1
s $in seq(N+)
s(3) = 3

have n N+ = 3
have finite_seq f finite_seq(N+, n) for i1 <= n, f(i1) = i1
f $in finite_seq(N+, n)
f(2) = 2

have r N+ = 2
have c N+ = 3
have matrix M matrix(N+, r, c) for i1 <= r, j <= c, M(i1, j) = j
M $in matrix(N+, r, c)
M(2, 3) = 3
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_seq_finite_seq_and_matrix_define_indexed_entries",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have_seq_finite_seq_and_matrix_define_indexed_entries failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"sequence definition\""));
            assert!(run_output.contains("\"type\": \"finite sequence definition\""));
            assert!(run_output.contains("\"type\": \"matrix definition\""));
        },
    );
}

#[test]
fn finite_seq_is_its_bounded_positive_index_function_space() {
    run_with_large_stack(
        "finite_seq_is_its_bounded_positive_index_function_space",
        || {
            let positive_source = r#"
have n N+ = 3
finite_seq(R, 3) = fn(x N+: x <= 3) R
fn(y N+: y <= 3) R = finite_seq(R, 3)
finite_seq(R, n) = fn(i1 N+: i1 <= n) R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("finite_seq_fn_set_definition_positive");
            let (stmt_results, runtime_error) = run_source_code(positive_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "finite_seq should equal its bounded positive-index function space:\n{}",
                run_output
            );
            assert!(
                run_output.contains("finite_seq is its bounded positive-index function space"),
                "finite_seq equality should expose its builtin definition route:\n{}",
                run_output
            );

            let negative_cases = [
                (
                    "finite_seq_length_mismatch",
                    "finite_seq(R, 3) = fn(x N+: x <= 2) R",
                ),
                (
                    "finite_seq_codomain_mismatch",
                    "finite_seq(R, 3) = fn(x N+: x <= 3) N",
                ),
                (
                    "finite_seq_index_set_mismatch",
                    "finite_seq(R, 3) = fn(x Z: x <= 3) R",
                ),
            ];
            for (label, source_code) in negative_cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} must not be accepted as a finite_seq definition:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn seq_and_matrix_are_their_function_spaces() {
    run_with_large_stack("seq_and_matrix_are_their_function_spaces", || {
        let positive_source = r#"
seq(R) = fn(i1 N+) R
fn(j N+) R = seq(R)

have rows N+ = 2
have cols N+ = 3
matrix(R, rows, cols) = fn(i1, j N+: i1 <= rows, j <= cols) R
fn(row, col N+: row <= rows, col <= cols) R = matrix(R, rows, cols)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("seq_matrix_fn_set_definition_positive");
        let (stmt_results, runtime_error) = run_source_code(positive_source, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            run_succeeded,
            "seq and matrix should equal their corresponding function spaces:\n{}",
            run_output
        );
        assert!(
            run_output.contains("seq is its positive-index function space"),
            "seq equality should expose its builtin definition route:\n{}",
            run_output
        );
        assert!(
            run_output.contains("matrix is its bounded positive-index function space"),
            "matrix equality should expose its builtin definition route:\n{}",
            run_output
        );

        let negative_cases = [
            ("seq_index_set_mismatch", "seq(R) = fn(i1 Z) R"),
            ("seq_codomain_mismatch", "seq(R) = fn(i1 N+) N"),
            (
                "matrix_column_bound_mismatch",
                "matrix(R, 2, 3) = fn(i1, j N+: i1 <= 2, j <= 2) R",
            ),
            (
                "matrix_index_set_mismatch",
                "matrix(R, 2, 3) = fn(i1, j Z: i1 <= 2, j <= 3) R",
            ),
            (
                "matrix_codomain_mismatch",
                "matrix(R, 2, 3) = fn(i1, j N+: i1 <= 2, j <= 3) N",
            ),
        ];
        for (label, source_code) in negative_cases {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(label);
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                !run_succeeded,
                "{} must not be accepted as a sequence or matrix definition:\n{}",
                label, run_output
            );
        }
    });
}

#[test]
fn failed_have_process_checks_do_not_bind_names() {
    run_with_large_stack("failed_have_process_checks_do_not_bind_names", || {
        let cases = [
            (
                "failed_have_obj_nonempty",
                "have s set\nhave a s",
                "have a R\na $in R",
            ),
            (
                "failed_have_obj_equal_type",
                "have a N = -1",
                "have a R = 1\na = 1",
            ),
            (
                "failed_have_fn_return_type",
                "have fn bad(x R) N = x",
                "have fn bad(x R) R = x\nbad(1) = 1",
            ),
            (
                "failed_have_finite_seq_bound",
                "have n N+ = 3\nhave m N+ = 2\nhave finite_seq f finite_seq(N+, n) for i1 <= m, f(i1) = i1",
                "have finite_seq f finite_seq(N+, n) for i1 <= n, f(i1) = i1\nf(1) = 1",
            ),
        ];

        for (case_name, failing_source, recovery_source) in cases {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(case_name);

            let (stmt_results, runtime_error) = run_source_code(failing_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                !run_succeeded,
                "{} should fail before recovery:\n{}",
                case_name, run_output
            );

            let (stmt_results, runtime_error) = run_source_code(recovery_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "{} should not bind the failed have name:\n{}",
                case_name, run_output
            );
        }
    });
}

#[test]
fn have_indexed_definitions_require_for_keyword() {
    run_with_large_stack("have_indexed_definitions_require_for_keyword", || {
        let source_code = r#"
have n N+ = 3
have tuple t for i1 <= n, t[i1] = i1
t[2] = 2

have seq s seq(N+) for i1, s(i1) = i1
s(3) = 3
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("have_indexed_definitions_require_for_keyword");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "indexed definitions with `for` should work:\n{}",
            run_output
        );
        assert!(
            run_output.contains("have tuple t for i1 <= n,"),
            "tuple definition should render with `for`:\n{}",
            run_output
        );
        assert!(
            run_output.contains("have seq s seq(N+) for i1,"),
            "sequence definition should render with `for`:\n{}",
            run_output
        );
    });
}

#[test]
fn have_seq_finite_seq_and_matrix_reject_bad_for_forms() {
    run_with_large_stack(
        "have_seq_finite_seq_and_matrix_reject_bad_for_forms",
        || {
            let cases = [
                (
                    "bad seq lhs",
                    r#"
have seq s seq(N+) for i1, t(i1) = i1
"#,
                    "have seq left side must apply the sequence being defined",
                ),
                (
                    "bad matrix lhs arity",
                    r#"
have r N+ = 2
have c N+ = 3
have matrix M matrix(N+, r, c) for i1 <= r, j <= c, M(i1) = i1
"#,
                    "have matrix left side must use exactly two indices",
                ),
                (
                    "bad finite_seq bound",
                    r#"
have n N+ = 3
have m N+ = 4
have finite_seq f finite_seq(N+, n) for i1 <= m, f(i1) = i1
"#,
                    "have finite_seq for-bound must match finite_seq length",
                ),
            ];

            for (case_name, source_code, expected_error) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(case_name);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(!run_succeeded, "{} should fail:\n{}", case_name, run_output);
                assert!(
                    run_output.contains(expected_error),
                    "{} should report `{}`:\n{}",
                    case_name,
                    expected_error,
                    run_output
                );
            }
        },
    );
}

#[test]
fn have_cart_can_equal_literal_cart_by_dimension_and_projections() {
    run_with_large_stack(
        "have_cart_can_equal_literal_cart_by_dimension_and_projections",
        || {
            let source_code = r#"
have n N+ = 3

have cart real_cart for i1 <= n, proj(real_cart, i1) = R
real_cart = cart(R, R, R)

have cart rational_cart for i1 <= n, proj(rational_cart, i1) = Q
cart(Q, Q, Q) = rational_cart
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_cart_can_equal_literal_cart_by_dimension_and_projections",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have_cart_can_equal_literal_cart_by_dimension_and_projections failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("cart equality from dimension and projections"),
                "cart extensionality rule should appear in verifier output:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_tuple_can_equal_literal_tuple_by_dimension_and_projections() {
    run_with_large_stack(
        "have_tuple_can_equal_literal_tuple_by_dimension_and_projections",
        || {
            let source_code = r#"
have n N+ = 3

have tuple index_tuple for i1 <= n, index_tuple[i1] = i1
index_tuple = (1, 2, 3)

have tuple real_tuple for i1 <= n, real_tuple[i1] = R
(R, R, R) = real_tuple
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_tuple_can_equal_literal_tuple_by_dimension_and_projections",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have_tuple_can_equal_literal_tuple_by_dimension_and_projections failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("tuple equality from dimension and projections"),
                "tuple extensionality rule should appear in verifier output:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn literal_cart_member_reconstructs_only_its_canonical_coordinate_tuple() {
    run_with_large_stack(
        "literal_cart_member_reconstructs_only_its_canonical_coordinate_tuple",
        || {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "literal_cart_member_reconstructs_only_its_canonical_coordinate_tuple",
            );
            let (stmt_results, runtime_error) = run_source_code(
                r#"
forall A, B set, p cart(A, B):
    p = (p[1], p[2])
"#,
                &mut runtime,
            );
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "literal cart member reconstruction failed:\n{run_output}"
            );
            assert!(
                run_output.contains("tuple reconstruction from known Cartesian-product membership"),
                "tuple reconstruction provenance is missing:\n{run_output}"
            );

            let mut negative_runtime = Runtime::new();
            negative_runtime.new_file_path_new_env_new_name_scope(
                "literal_cart_member_does_not_swap_its_coordinates",
            );
            let (negative_results, negative_error) = run_source_code(
                r#"
forall A, B set, p cart(A, B):
    p = (p[2], p[1])
"#,
                &mut negative_runtime,
            );
            let (negative_succeeded, negative_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_results,
                &negative_error,
                false,
            );
            assert!(
                !negative_succeeded,
                "tuple reconstruction must not swap coordinates:\n{negative_output}"
            );
        },
    );
}

#[test]
fn anonymous_function_beta_reduction_computes_literal_tuple_projections() {
    run_with_large_stack(
        "anonymous_function_beta_reduction_computes_literal_tuple_projections",
        || {
            let source_code = r#"
forall A, B set, a A, b B:
    fn(p cart(A, B)) A {p[1]}((a, b)) = a
    fn(p cart(A, B)) B {p[2]}((a, b)) = b
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_function_beta_reduction_computes_literal_tuple_projections",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "beta reduction should compute literal tuple projections:\n{run_output}"
            );

            let mut negative_runtime = Runtime::new();
            negative_runtime.new_file_path_new_env_new_name_scope(
                "anonymous_function_beta_reduction_does_not_swap_tuple_projections",
            );
            let (negative_results, negative_error) = run_source_code(
                r#"
forall A set, a, b A:
    fn(p cart(A, A)) A {p[1]}((a, b)) = b
"#,
                &mut negative_runtime,
            );
            let (negative_succeeded, negative_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_results,
                &negative_error,
                false,
            );
            assert!(
                !negative_succeeded,
                "beta reduction must preserve projection order:\n{negative_output}"
            );
        },
    );
}

#[test]
fn dependent_set_membership_does_not_materialize_a_symbolic_cart_view() {
    run_with_large_stack(
        "dependent_set_membership_does_not_materialize_a_symbolic_cart_view",
        || {
            let source_code = r#"
forall family power_set(power_set(R)), container power_set(R), member family:
    member $subset container
    =>:
        member $subset container
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "dependent_set_membership_does_not_materialize_a_symbolic_cart_view",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "dependent set membership should remain set-valued, not cart-valued:\n{run_output}"
            );
            assert!(
                !run_output.contains("cart_dim(member)"),
                "dependent set membership must not materialize symbolic cart coordinates:\n{run_output}"
            );
        },
    );
}

#[test]
fn have_tuple_and_have_cart_reject_bad_symbolic_definitions() {
    run_with_large_stack(
        "have_tuple_and_have_cart_reject_bad_symbolic_definitions",
        || {
            let cases = [
                (
                    "undefined dimension",
                    "have tuple f for i1 <= n, f[i1] = i1",
                    "identifier `n` not defined",
                ),
                (
                    "small dimension",
                    r#"
have n N+ = 1
have tuple f for i1 <= n, f[i1] = i1
"#,
                    "have tuple/cart needs 2 <= n",
                ),
                (
                    "self reference",
                    r#"
have n N+ = 3
have tuple f for i1 <= n, f[i1] = f[i1]
"#,
                    "identifier `f` not defined",
                ),
                (
                    "wrong tuple lhs",
                    r#"
have n N+ = 3
have tuple f for i1 <= n, g[i1] = i1
"#,
                    "have tuple left side must index the tuple being defined",
                ),
                (
                    "wrong cart lhs",
                    r#"
have n N+ = 3
have cart c for i1 <= n, proj(d, i1) = i1
"#,
                    "have cart left side must project the cart being defined",
                ),
            ];

            for (label, source_code, expected_message) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(!run_succeeded, "{} should fail:\n{}", label, run_output);
                assert!(
                    run_output.contains(expected_message),
                    "{} had unexpected output, expected `{}`:\n{}",
                    label,
                    expected_message,
                    run_output
                );
            }
        },
    );
}

#[test]
fn tuple_and_cart_coordinate_binders_reject_active_names_and_keep_outer_bounds() {
    run_with_large_stack(
        "tuple_and_cart_coordinate_binders_reject_active_names_and_keep_outer_bounds",
        || {
            let invalid_source_code = r#"
claim:
    ? forall i1 N+:
        i1 = 2
        =>:
            0 = 0
    have tuple t for i1 <= i1, t[i1] = 0
    0 = 0
"#;

            let mut invalid_runtime = Runtime::new();
            invalid_runtime
                .new_file_path_new_env_new_name_scope("tuple_coordinate_rejects_active_outer_name");
            let (invalid_results, invalid_error) =
                run_source_code(invalid_source_code, &mut invalid_runtime);
            let (invalid_succeeded, invalid_output) = render_run_source_code_output(
                &invalid_runtime,
                &invalid_results,
                &invalid_error,
                false,
            );
            assert!(
                !invalid_succeeded,
                "a coordinate binder must not reuse an active outer spelling:\n{}",
                invalid_output
            );
            assert!(
                invalid_output.contains("name `i1` is already active in this scope"),
                "the parser should identify the active coordinate-name collision:\n{}",
                invalid_output
            );

            let valid_source_code = r#"
claim:
    ? forall i1 N+:
        i1 = 2
        =>:
            0 = 0
    have tuple t for j <= i1, t[j] = 0
    t[1] = 0
    have cart c for j <= i1, proj(c, j) = R
    proj(c, 1) = R
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "tuple_and_cart_coordinate_binders_keep_outer_bounds",
            );
            let (stmt_results, runtime_error) = run_source_code(valid_source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "distinct coordinate binders should retain the captured outer dimension:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn fn_eq_generated_forall_freshens_cross_kind_function_parameter_name() {
    run_with_large_stack(
        "fn_eq_generated_forall_freshens_cross_kind_function_parameter_name",
        || {
            // One point of equality at the captured outer x cannot prove that two real
            // functions are pointwise equal on all of R.
            let invalid_source_code = r#"
claim:
    ? forall x R, f, g fn(z R) R:
        f(x) = g(x)
        =>:
            $fn_eq(f, g)
    f(x) = g(x)
    $fn_eq(f, g)
"#;

            let mut invalid_runtime = Runtime::new();
            invalid_runtime.new_file_path_new_env_new_name_scope(
                "fn_eq_generated_forall_rejects_captured_outer_point",
            );
            let (invalid_results, invalid_error) =
                run_source_code(invalid_source_code, &mut invalid_runtime);
            let (invalid_succeeded, invalid_output) = render_run_source_code_output(
                &invalid_runtime,
                &invalid_results,
                &invalid_error,
                false,
            );
            assert!(
                !invalid_succeeded,
                "a captured outer point must not close generated pointwise equality:\n{}",
                invalid_output
            );

            let valid_source_code = r#"
claim:
    ? forall x R, f, g fn(z R) R:
        forall y R:
            f(y) = g(y)
        =>:
            $fn_eq(f, g)
    forall y R:
        f(y) = g(y)
    $fn_eq(f, g)
"#;

            let mut valid_runtime = Runtime::new();
            valid_runtime.new_file_path_new_env_new_name_scope(
                "fn_eq_generated_forall_accepts_real_pointwise_equality",
            );
            let (valid_results, valid_error) =
                run_source_code(valid_source_code, &mut valid_runtime);
            let (valid_succeeded, valid_output) =
                render_run_source_code_output(&valid_runtime, &valid_results, &valid_error, false);
            assert!(
                valid_succeeded,
                "real pointwise equality should still prove function equality:\n{}",
                valid_output
            );
        },
    );
}

#[test]
fn fn_eq_consumes_exact_pointwise_forall_before_dependent_membership_replay() {
    run_with_large_stack(
        "fn_eq_consumes_exact_pointwise_forall_before_dependent_membership_replay",
        || {
            let source_code = r#"
claim:
    ? forall X, Y nonempty_set, f, g fn(x X) Y:
        forall x X:
            f(x) = g(x)
        =>:
            $fn_eq(f, g)
    forall x X:
        f(x) = g(x)
    $fn_eq(f, g)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "fn_eq_consumes_exact_pointwise_forall_before_dependent_membership_replay",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "an exact pointwise forall over the same declared function carrier should prove fn_eq:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_cases_rejects_active_parameter_name_and_keeps_outer_singleton_domain() {
    run_with_large_stack(
        "have_fn_by_cases_rejects_active_parameter_name_and_keeps_outer_singleton_domain",
        || {
            let invalid_source_code = r#"
claim:
    ? forall x R:
        x = x
    have fn h(x {x}) R by cases:
        case x = x: 0
    x = x
"#;

            let mut invalid_runtime = Runtime::new();
            invalid_runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_cases_rejects_active_parameter_name",
            );
            let (invalid_results, invalid_error) =
                run_source_code(invalid_source_code, &mut invalid_runtime);
            let (invalid_succeeded, invalid_output) = render_run_source_code_output(
                &invalid_runtime,
                &invalid_results,
                &invalid_error,
                false,
            );
            assert!(
                !invalid_succeeded,
                "a function parameter must not reuse an active outer spelling:\n{}",
                invalid_output
            );
            assert!(
                invalid_output.contains("name `x` is already active in this scope"),
                "the parser should identify the active function-parameter collision:\n{}",
                invalid_output
            );

            let valid_source_code = r#"
claim:
    ? forall x R:
        x = x
    have fn h(y {x}) R by cases:
        case y = x: 0
    h(x) = 0
    x = x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_cases_keeps_outer_singleton_domain",
            );
            let (stmt_results, runtime_error) = run_source_code(valid_source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "a distinct function parameter should retain the captured singleton domain:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_cases_result_rewrites_membership_at_equal_indices() {
    run_with_large_stack(
        "have_fn_by_cases_result_rewrites_membership_at_equal_indices",
        || {
            let source_code = r#"
claim:
    ? forall m, k N+, parts finite_seq(power_set(R), m):
        k <= m
        =>:
            0 = 0
    claim:
        ? forall x parts(k), i1 N+:
            x $in R
            i1 <= m
            i1 = k
            =>:
                x = x
        have zero R = 0
        have fn terms(j N+: j <= m) R by cases:
            case j = k: x
            case j != k: zero
        terms(i1) = x
        terms(i1) $in parts(i1)
        x = x
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_cases_result_rewrites_membership_at_equal_indices",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "casewise function results should preserve membership through an equal index:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn known_membership_rewrites_through_equal_set_and_equal_singleton_element() {
    run_with_large_stack(
        "known_membership_rewrites_through_equal_set_and_equal_singleton_element",
        || {
            let source_code = r#"
have U power_set(R)
have W power_set(R)
have delta R
have zero R
trust delta $in intersect(U, W)
trust intersect(U, W) = {0}
trust zero = 0
delta $in {zero}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "known_membership_rewrites_through_equal_set_and_equal_singleton_element",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "membership should rewrite through a stored set equality and singleton congruence:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn current_module_qualified_struct_function_field_remains_callable() {
    run_with_large_stack(
        "current_module_qualified_struct_function_field_remains_callable",
        || {
            let source_code = r#"
struct ScalarSystem<s nonempty_set>:
    zero s
    add fn(x, y s) s

have fn real_add(x, y R) R = x + y
have real_scalars &ScalarSystem<R> = (0, real_add)

have fn coordinate_add(x, y finite_seq(R, 2)) finite_seq(R, 2) = fn(i1 N+: i1 <= 2) R {&Current::ScalarSystem<R>{Current::real_scalars}.add(x(i1), y(i1))}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "current_module_qualified_struct_function_field_remains_callable",
            );
            runtime.current_module_mut().module_name = "Current".to_string();
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a struct function field should keep its type through current-module qualification:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn instantiated_template_function_unfolds_before_curried_entry_application() {
    run_with_large_stack(
        "instantiated_template_function_unfolds_before_curried_entry_application",
        || {
            let source_code = r#"
template<n N+>:
    have fn pairwise_sum(x, y finite_seq(R, n)) finite_seq(R, n) = fn(i1 N+: i1 <= n) R {x(i1) + y(i1)}

have x, y finite_seq(R, 2)
\pairwise_sum<2>(x, y)(1) = x(1) + y(1)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "instantiated_template_function_unfolds_before_curried_entry_application",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a materialized template function should unfold before applying its returned finite sequence:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn callable_struct_field_of_selected_template_object_unfolds() {
    run_with_large_stack(
        "callable_struct_field_of_selected_template_object_unfolds",
        || {
            let source_code = r#"
struct FunctionBox<n N+>:
    length N
    entries fn(i1 N+: i1 <= n) R
    <=>:
        length = n

template<n N+>:
    have zero_box &FunctionBox<n> = (n, fn(i1 N+: i1 <= n) R {0})

trust have result &FunctionBox<2>
trust result = \zero_box<2>
&FunctionBox<2>{\zero_box<2>}.entries(1) = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "callable_struct_field_of_selected_template_object_unfolds",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a callable field of a selected template object should project and beta-reduce:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_can_define_symbolic_tuple_and_cart() {
    run_with_large_stack("template_can_define_symbolic_tuple_and_cart", || {
        let source_code = r#"
template<n N+: 2 <= n>:
    have tuple tuple_by_dim for i1 <= n, tuple_by_dim[i1] = i1

$is_tuple(\tuple_by_dim<3>)
tuple_dim(\tuple_by_dim<3>) = 3
forall i1 closed_range(1, 3):
    \tuple_by_dim<3>[i1] = i1

template<n N+: 2 <= n>:
    have cart cart_by_dim for i1 <= n, proj(cart_by_dim, i1) = R

$is_cart(\cart_by_dim<3>)
cart_dim(\cart_by_dim<3>) = 3
forall i1 closed_range(1, 3):
    proj(\cart_by_dim<3>, i1) = R
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("template_can_define_symbolic_tuple_and_cart");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "template_can_define_symbolic_tuple_and_cart failed:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_power_set_has_builtin_finite_set_size_rules() {
    run_with_large_stack("finite_power_set_has_builtin_finite_set_size_rules", || {
        let source_code = r#"
$is_finite_set(power_set({1, 2, 3}))
$is_finite_set({1, 2, 3})
finite_set_size(power_set({1, 2, 3})) = 2^finite_set_size({1, 2, 3})
finite_set_size({1, 2, 3}) = 3
2^finite_set_size({1, 2, 3}) = 2^3 = 8
finite_set_size(power_set({1, 2, 3})) = 8
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "finite_power_set_has_builtin_finite_set_size_rules",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite_power_set_has_builtin_finite_set_size_rules failed:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_set_size_is_canonical_and_count_is_available_for_user_definitions() {
    run_with_large_stack(
        "finite_set_size_is_canonical_and_count_is_available_for_user_definitions",
        || {
            let source_code = r#"
finite_set_size({1, 2, 3}) = 3
finite_set_size(1...5) = 5

have fn count(n N) N = n
count(2) = 2
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "finite_set_size_is_canonical_and_count_is_available_for_user_definitions",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "finite_set_size or user-defined count failed:\n{}",
                run_output
            );

            let mut wrong_arity_runtime = Runtime::new();
            wrong_arity_runtime
                .new_file_path_new_env_new_name_scope("finite_set_size_rejects_wrong_arity");
            let (stmt_results, runtime_error) =
                run_source_code("finite_set_size({1}, {2}) = 2", &mut wrong_arity_runtime);
            let (wrong_arity_succeeded, wrong_arity_output) = render_run_source_code_output(
                &wrong_arity_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );

            assert!(
                !wrong_arity_succeeded,
                "finite_set_size accepted two arguments:\n{}",
                wrong_arity_output
            );
            assert!(
                wrong_arity_output.contains("finite_set_size expects 1 argument"),
                "wrong-arity diagnostic should name finite_set_size:\n{}",
                wrong_arity_output
            );
        },
    );
}

#[test]
fn subset_fact_proves_power_set_membership() {
    run_with_large_stack("subset_fact_proves_power_set_membership", || {
        let source_code = r#"
have A set
have B set
trust A $subset B
A $in power_set(B)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("subset_fact_proves_power_set_membership");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "subset_fact_proves_power_set_membership failed:\n{}",
            run_output
        );
    });
}

#[test]
fn set_builder_over_alpha_equivalent_fn_set_satisfies_power_set_type() {
    run_with_large_stack(
        "set_builder_over_alpha_equivalent_fn_set_satisfies_power_set_type",
        || {
            let source_code = r#"
template<X set>:
    have reflexive_function_family power_set(fn(x X) X) = {f fn(y X) X: f = f}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "set_builder_over_alpha_equivalent_fn_set_satisfies_power_set_type",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "set builder over an alpha-equivalent function set should satisfy its power-set type:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn set_builder_subset_inference_does_not_rebind_its_filter_domain() {
    run_with_large_stack(
        "set_builder_subset_inference_does_not_rebind_its_filter_domain",
        || {
            let source_code = r#"
have fn positive_identity(x R+) R = x
have fn filtered_positive_set(n N+) power_set(R+) = {y R+: y $in R+ and positive_identity(y) > 0}
filtered_positive_set(1) $in power_set(R+)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "set_builder_subset_inference_does_not_rebind_its_filter_domain",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "set_builder_subset_inference_does_not_rebind_its_filter_domain failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn subset_inference_skips_set_builder_equality_representative() {
    run_with_large_stack(
        "subset_inference_skips_set_builder_equality_representative",
        || {
            let source_code = r#"
prop is_candidate(X power_set(R), x R):
    exist y X st {x = y}

have fn candidate_closure(X power_set(R)) power_set(R) = {x R: $is_candidate(X, x)}

thm closed_candidate_members_stay_in_set:
    ? forall X power_set(R), x R:
        candidate_closure(X) = X
        x $in candidate_closure(X)
        =>:
            x $in X
    x $in X
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "subset_inference_skips_set_builder_equality_representative",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "subset_inference_skips_set_builder_equality_representative failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn extension_uses_known_subset_facts_for_set_builder_values() {
    run_with_large_stack(
        "extension_uses_known_subset_facts_for_set_builder_values",
        || {
            let source_code = r#"
have fn builder_like(X power_set(R)) power_set(R) = {x R: x = x}
have X power_set(R)
trust builder_like(X) $subset X
trust X $subset builder_like(X)
by extension:
    ? builder_like(X) = X
builder_like(X) = X
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "extension_uses_known_subset_facts_for_set_builder_values",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "by extension should use known subset facts for set-builder values:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn compact_numeric_set_suffixes_use_existing_set_semantics() {
    run_with_large_stack(
        "compact_numeric_set_suffixes_use_existing_set_semantics",
        || {
            let source_code = r#"
have n N+
n $in N+
have zp Z+
zp $in N+
have qp Q+
qp $in Q+
have rp R+
rp $in R+
have zn Z-
zn $in Z-
have qn Q-
qn $in Q-
have rn R-
rn $in R-
have znz Z*
znz $in Z*
have qnz Q*
qnz $in Q*
have rnz R*
rnz $in R*

forall x R+:
    x $in R+

fn(x N+) R+ = fn(x N+) R+
fn(x Z-) R- = fn(x Z-) R-

1 $in N+
1 $in Z+
1 $in Q+
1 $in R+
-1 $in Z-
-1 $in Q-
-1 $in R-
1 $in Z*
1 $in Q*
1 $in R*
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compact_numeric_set_suffixes_use_existing_set_semantics",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "compact numeric-set suffixes should reuse existing semantics:\n{}",
                run_output
            );
            assert!(run_output.contains("have n N+"), "{run_output}");
            assert!(run_output.contains("have zp N+"), "{run_output}");
            assert!(run_output.contains("have qn Q-"), "{run_output}");
        },
    );
}

#[test]
fn unsupported_compact_standard_set_suffixes_still_fail() {
    for (name, source_code) in [
        ("compact_n_negative", "have n N-"),
        ("compact_nonempty_set", "have S set+"),
        ("compact_set_negative", "have S set-"),
        ("spaced_compact_n_positive", "have n N +"),
    ] {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "unsupported compact spelling `{source_code}` should fail:\n{run_output}"
        );
    }
}

#[test]
fn general_cart_builtin_definition_choice_and_membership_inference() {
    run_with_large_stack(
        "general_cart_builtin_definition_choice_and_membership_inference",
        || {
            let source_code = r#"
have I set
have X nonempty_set
trust forall x X => {$is_nonempty_set(x)}
have g fn(alpha I) X

by thm general_cart_nonempty_by_choice_from_family(general_cart(I, X, g))
$is_nonempty_set(general_cart(I, X, g))
general_cart(I, X, g) = {f fn(t I)big_union(X): forall alpha I => {f(alpha) $in g(alpha)}}
have c general_cart(I, X, g)
c $in fn(t I)big_union(X)
forall alpha I:
    c(alpha) $in g(alpha)

have J set
have h fn(beta J) X
forall beta J:
    $is_nonempty_set(h(beta))
by thm general_cart_nonempty_by_choice_from_pointwise(general_cart(J, X, h))
$is_nonempty_set(general_cart(J, X, h))
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "general_cart_builtin_definition_choice_and_membership_inference",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "general_cart builtin definition/choice test failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn general_cart_nonempty_requires_factor_nonempty_fact() {
    run_with_large_stack(
        "general_cart_nonempty_requires_factor_nonempty_fact",
        || {
            let source_code = r#"
have I set
have s nonempty_set
have g fn(alpha I) s

$is_nonempty_set(general_cart(I, s, g))
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "general_cart_nonempty_requires_factor_nonempty_fact",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "general_cart nonempty should require factor nonempty evidence:\n{}",
                run_output
            );
        },
    );
}

#[test]
pub(super) fn latex_output_is_fragment_without_default_packages() {
    let output = to_latex_from_source("1 = 1", "latex_output_is_fragment_without_default_packages")
        .expect("simple Litex source should convert to LaTeX");

    assert!(output.contains(r"\["));
    assert!(output.contains(r"\]"));
    assert!(output.contains("1 = 1"));
    assert!(!output.contains(r"\documentclass{article}"));
    assert!(!output.contains(r"\begin{document}"));
    assert!(!output.contains(r"\end{document}"));
    assert!(!output.contains(r"\paragraph{Stmt 1}"));
    assert!(!output.contains(r"\usepackage{amsmath}"));
    assert!(!output.contains(r"\usepackage{amssymb}"));
}

#[test]
fn latex_chained_field_access_uses_earlier_struct_declarations() {
    let source_code = r#"
struct Leaf:
    value R
    marker N

struct Node:
    leaf &Leaf
    marker N

forall node &Node:
    node.leaf.value $in R
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "latex_chained_field_access_uses_earlier_struct_declarations",
    );
    let output = crate::to_latex::to_latex(source_code, &mut runtime)
        .expect("LaTeX conversion should retain parsed struct metadata for field chains");

    assert!(output.contains("Leaf"));
    assert!(output.contains("Node"));
    assert!(output.contains("value"));
    assert!(
        runtime.get_struct_definition_by_name("Leaf").is_none(),
        "parse-only struct metadata must not enter the verified environment"
    );
}

#[test]
fn chained_field_access_works_across_flattened_module_and_latex() {
    run_with_large_stack(
        "chained_field_access_works_across_flattened_module_and_latex",
        || {
            let project_root = std::env::temp_dir()
                .join(format!("litex-latex-chained-fields-{}", std::process::id()));
            let app_root = project_root.join("app");
            let flat_root = project_root.join("flat");
            let _ = std::fs::remove_dir_all(&project_root);
            std::fs::create_dir_all(&app_root).expect("create importing project fixture");
            std::fs::create_dir_all(&flat_root).expect("create flattened module fixture");
            std::fs::write(
                flat_root.join("litex.config"),
                "[hierarchy]\nmodule\n\n[module]\nflatten = true\n\n[export]\nmain = \"./main.lit\"\n",
            )
            .expect("write flattened module config");
            std::fs::write(
                flat_root.join("main.lit"),
                "struct Leaf:\n    value R\n    marker N\n\nstruct Outer:\n    inner &Leaf\n    marker N\n",
            )
            .expect("write flattened struct fixture");
            std::fs::write(
                app_root.join("litex.config"),
                "[hierarchy]\nmodule\n\n[import]\nflat = \"../flat\"\n\n[export]\nmain = \"./main.lit\"\n",
            )
            .expect("write importing project config");
            std::fs::write(
                app_root.join("main.lit"),
                "forall outer &flat::Outer:\n    outer.inner.value $in R\n",
            )
            .expect("write chained field fixture");

            let repository_path = app_root.to_str().expect("temporary path must be UTF-8");
            let (run_succeeded, run_output) = run_repository_with_output(
                repository_path,
                false,
                false,
                OutputLanguage::English,
                false,
            );
            let result = crate::to_latex::to_latex_from_repository(repository_path);
            let _ = std::fs::remove_dir_all(&project_root);
            assert!(
                run_succeeded,
                "runtime field chains should resolve structs from a flattened module:\n{}",
                run_output
            );
            let output =
                result.expect("LaTeX conversion should retain flattened-module struct metadata");

            assert!(output.contains("flat"));
            assert!(output.contains("value"));
            assert!(
                !output.contains("marker"),
                "an imported module should provide parser metadata without entering root LaTeX output"
            );
        },
    );
}

#[test]
pub(super) fn python_extractor_outputs_supported_have_subset() {
    run_with_large_stack("python_extractor_outputs_supported_have_subset", || {
        let source_code = r#"
have q Q = 1
have z Z = 3

have fn f(x R) R = x + 1
have algo for f(x):
    x + 1

have fn g(x R) R = f(x) + 2
have algo for g(x):
    f(x) + 2

have fn max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
have algo for max2(x, y):
    case x >= y: x
    case x < y: y
"#;

        let output = to_python_from_source(
            source_code,
            "python_extractor_outputs_supported_have_subset",
        )
        .expect("supported Python extraction should succeed");

        assert!(output.contains("q = 1.0"));
        assert!(output.contains("z = 3.0"));
        assert!(output.contains("def f(x):"));
        assert!(output.contains("return (x + 1.0)"));
        assert!(output.contains("def g(x):"));
        assert!(output.contains("return (f(x) + 2.0)"));
        assert!(output.contains("def max2(x, y):"));
        assert!(output.contains("if x >= y:"));
        assert!(output.contains("elif x < y:"));
        assert!(output.contains("unreachable verified Litex cases"));
    });
}

#[test]
fn python_extractor_skips_non_numeric_have_obj_equal() {
    run_with_large_stack("python_extractor_skips_non_numeric_have_obj_equal", || {
        let output = to_python_from_source(
            "have s set = R",
            "python_extractor_skips_non_numeric_have_obj_equal",
        )
        .expect("non-numeric object definitions should be skipped");

        assert_eq!(output, "# No Python-extractable Litex definitions.");
    });
}

#[test]
fn python_extractor_emits_have_algo_for() {
    run_with_large_stack("python_extractor_emits_have_algo_for", || {
        let source_code = r#"
have fn f(x R) R = x

have algo for f(x):
    x
"#;

        let output = to_python_from_source(source_code, "python_extractor_emits_have_algo_for")
            .expect("have algo for implementation should be extracted in v1");
        assert!(output.contains("def f(x):"));
        assert!(output.contains("return x"));
    });
}

#[test]
fn python_extractor_emits_self_recursive_have_algo_for() {
    run_with_large_stack(
        "python_extractor_emits_self_recursive_have_algo_for",
        || {
            let source_code = r#"
have loop fn(x R) R
trust:
    forall x R:
        loop(x) = loop(x)

have algo for loop(x):
    loop(x)
"#;

            let output = to_python_from_source(
                source_code,
                "python_extractor_emits_self_recursive_have_algo_for",
            )
            .expect("self-recursive have algo for implementation should be extracted in v1");
            assert!(output.contains("def loop(x):"));
            assert!(output.contains("return loop(x)"));
        },
    );
}

#[test]
fn python_extractor_rejects_non_real_function_parameters() {
    run_with_large_stack(
        "python_extractor_rejects_non_real_function_parameters",
        || {
            let source_code = "have fn f(x Z) R = x\nhave algo for f(x):\n    x";
            let error = to_python_from_source(
                source_code,
                "python_extractor_rejects_non_real_function_parameters",
            )
            .expect_err("non-R function params should be rejected by Python extraction");
            let error_text = format!("{:?}", error);
            assert!(error_text.contains("supports only `R` function parameters"));
        },
    );
}

#[test]
fn strong_induc_requires_by_prefix() {
    run_with_large_stack("strong_induc_requires_by_prefix", || {
        let source_code = r#"
strong_induc n from 0:
    do_nothing
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("strong_induc_requires_by_prefix");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "bare strong_induc should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("strong_induc is only valid after `by`"),
            "bare strong_induc should explain its valid context:\n{}",
            run_output
        );
    });
}

#[test]
fn standalone_ellipsis_is_not_a_noop() {
    run_with_large_stack("standalone_ellipsis_is_not_a_noop", || {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("standalone_ellipsis_is_not_a_noop");
        let (stmt_results, runtime_error) = run_source_code("...", &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "standalone ellipsis should not parse as a proof step:\n{}",
            run_output
        );
    });
}

#[test]
fn list_set_membership_implies_equality_or() {
    let source_code = r#"
forall a set:
    a = 1 or a = 2 or a = 3
    =>:
        a $in {1, 2, 3}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("list_set_membership_implies_equality_or");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "list_set_membership_implies_equality_or failed:\n{}",
        run_output
    );
}

#[test]
fn user_prop_inference_exposes_its_direct_definition_clause() {
    run_with_large_stack(
        "user_prop_inference_exposes_its_direct_definition_clause",
        || {
            let source_code = r#"
prop leaf(x R):
    x = 0

prop middle(x R):
    $leaf(x)

prop outer(x R):
    $middle(x)

trust $outer(1)

$middle(1)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "user_prop_inference_exposes_its_direct_definition_clause",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "direct user-prop definition projection failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn user_prop_inference_recursively_expands_positive_prop_clauses() {
    run_with_large_stack(
        "user_prop_inference_recursively_expands_positive_prop_clauses",
        || {
            let source_code = r#"
prop leaf(x R):
    x = 0

prop middle(x R):
    $leaf(x)

prop outer(x R):
    $middle(x)

trust $outer(1)

$leaf(1)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "user_prop_inference_recursively_expands_positive_prop_clauses",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "nested positive user-prop clauses should be inferred recursively:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn obtain_exposes_direct_predicate_body_without_recursive_expansion() {
    run_with_large_stack(
        "obtain_exposes_direct_predicate_body_without_recursive_expansion",
        || {
            let source_code = r#"
prop leaf(x R):
    x = 0

prop middle(x R):
    $leaf(x)

trust exist x R st {$middle(x)}
obtain y from exist x R st {$middle(x)}
$leaf(y)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "obtain_exposes_direct_predicate_body_without_recursive_expansion",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "obtain should expose its direct predicate body:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn obtain_recursively_expands_positive_predicate_body() {
    run_with_large_stack("obtain_recursively_expands_positive_predicate_body", || {
        let source_code = r#"
prop leaf(x R):
    x = 0

prop middle(x R):
    $leaf(x)

prop outer(x R):
    $middle(x)

trust exist x R st {$outer(x)}
obtain y from exist x R st {$outer(x)}
$leaf(y)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "obtain_recursively_expands_positive_predicate_body",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "obtain should recursively expose positive predicate bodies:\n{}",
            run_output
        );
    });
}

#[test]
fn grouped_forall_law_projects_clause_over_used_nonempty_parameters() {
    run_with_large_stack(
        "grouped_forall_law_projects_clause_over_used_nonempty_parameters",
        || {
            let source_code = r#"
abstract_prop p(a, x)

prop grouped_laws(seed R):
    forall a, b, x, y R:
        $p(a, x)
        $p(b, y)

trust $grouped_laws(0)

$p(1, 2)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "grouped_forall_law_projects_clause_over_used_nonempty_parameters",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "grouped forall clause should project over its used parameters:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn known_implication_packages_as_classical_or() {
    let source_code = r#"
abstract_prop p(x)
abstract_prop q(x)

trust forall x R:
    $p(x)
    =>:
        $q(x)

forall x R:
    not $p(x) or $q(x)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_implication_packages_as_classical_or");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a known implication should package as its classical disjunction:\n{}",
        run_output
    );
}

#[test]
fn template_set_builder_definition_exposes_membership_definition() {
    let source_code = r#"
abstract_prop marked(x)

template<T set>:
    have selected power_set(T) = {x T: $marked(x)}

trust $marked(1)

1 $in \selected<R>
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "template_set_builder_definition_exposes_membership_definition",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template set-builder definitions should retain their defining membership facts:\n{}",
        run_output
    );
}

#[test]
fn membership_in_template_set_builder_definition_infers_definition() {
    let source_code = r#"
abstract_prop marked(x)

template<T set>:
    have selected power_set(T) = {x T: $marked(x)}

trust 1 $in \selected<R>

$marked(1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "membership_in_template_set_builder_definition_infers_definition",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "membership in a template set-builder definition should infer its definition:\n{}",
        run_output
    );
}

#[test]
fn template_set_builder_membership_definition_forms_equivalence() {
    let source_code = r#"
abstract_prop marked(x)

template<T set>:
    have selected power_set(T) = {x T: $marked(x)}

prop eventually_in(T set, F power_set(T), x T):
    x $in F

prop marked_eventually_equivalence(x R):
    not $marked(x) or $eventually_in(R, \selected<R>, x)
    not $eventually_in(R, \selected<R>, x) or $marked(x)

by def $marked_eventually_equivalence(1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "template_set_builder_membership_definition_forms_equivalence",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template set-builder membership should package into both equivalence directions:\n{}",
        run_output
    );
}

#[test]
fn literal_set_builder_membership_packages_known_conjunction_only() {
    let positive_source = r#"
forall x R:
    0 <= x
    x <= 1
    =>:
        x $in {y R: 0 <= y and y <= 1}
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.new_file_path_new_env_new_name_scope(
        "literal_set_builder_membership_packages_known_conjunction",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "known set-builder conjuncts should introduce membership:\n{}",
        positive_output
    );

    let negative_source = r#"
forall x R:
    0 <= x
    =>:
        x $in {y R: 0 <= y and y <= 1}
"#;
    let mut negative_runtime = Runtime::new();
    negative_runtime.new_file_path_new_env_new_name_scope(
        "literal_set_builder_membership_rejects_missing_conjunct",
    );
    let (negative_results, negative_error) =
        run_source_code(negative_source, &mut negative_runtime);
    let (negative_succeeded, _) =
        render_run_source_code_output(&negative_runtime, &negative_results, &negative_error, false);
    assert!(
        !negative_succeeded,
        "set-builder membership must not invent a missing conjunct"
    );
}

#[test]
fn set_builder_membership_folds_one_known_predicate_definition() {
    let positive_source = r#"
prop is_doubled(n N):
    exist k N st {n = 2 * k}

claim:
    ? forall n N:
        2 * n $in {m N: $is_doubled(m)}
    witness exist k N st {2 * n = 2 * k} from n
    2 * n $in {m N: $is_doubled(m)}
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.new_file_path_new_env_new_name_scope(
        "set_builder_membership_folds_one_known_predicate_definition",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a proved predicate body should introduce one-layer set-builder membership:\n{}",
        positive_output
    );

    let negative_source = r#"
prop is_doubled(n N):
    exist k N st {n = 2 * k}

have n N
n $in {m N: $is_doubled(m)}
"#;
    let mut negative_runtime = Runtime::new();
    negative_runtime.new_file_path_new_env_new_name_scope(
        "set_builder_membership_rejects_unproved_predicate_definition",
    );
    let (negative_results, negative_error) =
        run_source_code(negative_source, &mut negative_runtime);
    let (negative_succeeded, _) =
        render_run_source_code_output(&negative_runtime, &negative_results, &negative_error, false);
    assert!(
        !negative_succeeded,
        "set-builder membership must not invent an unproved predicate body"
    );
}

#[test]
fn known_set_builder_definition_membership_eliminates_to_its_predicate() {
    let positive_source = r#"
have fn above(a R) power_set(R) = {x R: x > a}
forall a R:
    above(a) = {z R: z > a}
have y R
trust y $in above(0)
y $in {x R: x > 0}
y > 0
have fn pick(a R) R = a
trust forall a R:
    pick(a) $in above(a)
forall a R:
    pick(a) $in {x R: x > a}
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.new_file_path_new_env_new_name_scope(
        "known_set_builder_definition_membership_eliminates_to_its_predicate",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "membership in a set-builder definition should expose its defining predicate:\n{}",
        positive_output
    );

    let negative_source = r#"
have fn above(a R) power_set(R) = {x R: x > a}
have y R
trust y $in above(0)
y $in {x R: x < 0}
"#;
    let mut negative_runtime = Runtime::new();
    negative_runtime.new_file_path_new_env_new_name_scope(
        "set_builder_definition_membership_does_not_invent_other_facts",
    );
    let (negative_results, negative_error) =
        run_source_code(negative_source, &mut negative_runtime);
    let (negative_succeeded, _) =
        render_run_source_code_output(&negative_runtime, &negative_results, &negative_error, false);
    assert!(
        !negative_succeeded,
        "set-builder definition transport must require the same unfolded builder"
    );

    let wrong_definition_equality_source = r#"
have fn above(a R) power_set(R) = {x R: x > a}
above(0) = {z R: z < 0}
"#;
    let mut wrong_definition_equality_runtime = Runtime::new();
    wrong_definition_equality_runtime.new_file_path_new_env_new_name_scope(
        "set_builder_definition_equality_requires_the_same_predicate",
    );
    let (wrong_equality_results, wrong_equality_error) = run_source_code(
        wrong_definition_equality_source,
        &mut wrong_definition_equality_runtime,
    );
    let (wrong_equality_succeeded, _) = render_run_source_code_output(
        &wrong_definition_equality_runtime,
        &wrong_equality_results,
        &wrong_equality_error,
        false,
    );
    assert!(
        !wrong_equality_succeeded,
        "definition unfolding must not identify set-builders with different predicates"
    );
}
