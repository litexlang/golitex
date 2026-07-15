use super::*;
use std::path::Path;

#[test]
fn builtin_rules_do_not_call_full_verifier_pipeline() {
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
    ];
    let mut violations = Vec::new();
    let mut source_files = Vec::new();
    collect_rust_files_under_dir(&builtin_rules_dir, &mut source_files);
    for path in source_files {
        let content = fs::read_to_string(&path).expect("read verify_builtin_rules source file");
        for (line_index, line) in content.lines().enumerate() {
            for disallowed_call in disallowed_calls {
                if line.contains(disallowed_call) {
                    violations.push(format!(
                        "{}:{} contains `{}`",
                        path.display(),
                        line_index + 1,
                        disallowed_call
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "builtin rules must use restricted known-atomic/builtin helpers, not the full verifier:\n{}",
        violations.join("\n")
    );
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
fn cup_membership_has_builtin_intro_and_elim() {
    run_with_large_stack("cup_membership_has_builtin_intro_and_elim", || {
        let source_code = r#"
thm tmp_cup_intro_from_member:
    ? forall x set, F set, A set:
        A $in F
        x $in A
        =>:
            x $in cup(F)
    x $in cup(F)

thm tmp_cup_intro_from_exist:
    ? forall x set, F set:
        exist A F st {x $in A}
        =>:
            x $in cup(F)
    x $in cup(F)

thm tmp_cup_elim_to_exist:
    ? forall x set, F set:
        x $in cup(F)
        =>:
            exist A F st {x $in A}
    exist A F st {x $in A}
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("cup_membership_has_builtin_intro_and_elim");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "cup_membership_has_builtin_intro_and_elim failed:\n{}",
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
have n N_pos = 3
have tuple f for i <= n, f[i] = i
$is_tuple(f)
tuple_dim(f) = n
forall i closed_range(1, n):
    f[i] = i

have cart c for i <= n, proj(c, i) = f[i]
$is_set(c)
$is_cart(c)
cart_dim(c) = n
forall i closed_range(1, n):
    proj(c, i) = f[i]
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
have seq s seq(N_pos) for i, s(i) = i
s $in seq(N_pos)
s(3) = 3

have n N_pos = 3
have finite_seq f finite_seq(N_pos, n) for i <= n, f(i) = i
f $in finite_seq(N_pos, n)
f(2) = 2

have r N_pos = 2
have c N_pos = 3
have matrix M matrix(N_pos, r, c) for i <= r, j <= c, M(i, j) = j
M $in matrix(N_pos, r, c)
M(2, 3) = 3
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
                "have n N_pos = 3\nhave m N_pos = 2\nhave finite_seq f finite_seq(N_pos, n) for i <= m, f(i) = i",
                "have finite_seq f finite_seq(N_pos, n) for i <= n, f(i) = i\nf(1) = 1",
            ),
        ];

        for (case_name, failing_source, recovery_source) in cases {
            let mut runtime = Runtime::new_with_builtin_code();
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
have n N_pos = 3
have tuple t for i <= n, t[i] = i
t[2] = 2

have seq s seq(N_pos) for i, s(i) = i
s(3) = 3
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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
            run_output.contains("have tuple t for i <= n,"),
            "tuple definition should render with `for`:\n{}",
            run_output
        );
        assert!(
            run_output.contains("have seq s seq(N_pos) for i,"),
            "sequence definition should render with `for`:\n{}",
            run_output
        );

        let mut legacy_runtime = Runtime::new_with_builtin_code();
        legacy_runtime.new_file_path_new_env_new_name_scope("indexed_definition_old_form");
        let (stmt_results, runtime_error) = run_source_code(
            "have tuple old_form by i N, old_form[i] = i",
            &mut legacy_runtime,
        );
        let (old_form_succeeded, old_form_output) =
            render_run_source_code_output(&legacy_runtime, &stmt_results, &runtime_error, false);
        assert!(
            !old_form_succeeded,
            "old index syntax unexpectedly parsed:\n{old_form_output}"
        );
        assert!(old_form_output.contains("expects `for` before the index binder"));
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
have seq s seq(N_pos) for i, t(i) = i
"#,
                    "have seq left side must apply the sequence being defined",
                ),
                (
                    "bad matrix lhs arity",
                    r#"
have r N_pos = 2
have c N_pos = 3
have matrix M matrix(N_pos, r, c) for i <= r, j <= c, M(i) = i
"#,
                    "have matrix left side must use exactly two indices",
                ),
                (
                    "bad finite_seq bound",
                    r#"
have n N_pos = 3
have m N_pos = 4
have finite_seq f finite_seq(N_pos, n) for i <= m, f(i) = i
"#,
                    "have finite_seq for-bound must match finite_seq length",
                ),
            ];

            for (case_name, source_code, expected_error) in cases {
                let mut runtime = Runtime::new_with_builtin_code();
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
have n N_pos = 3

have cart real_cart for i <= n, proj(real_cart, i) = R
real_cart = cart(R, R, R)

have cart rational_cart for i <= n, proj(rational_cart, i) = Q
cart(Q, Q, Q) = rational_cart
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
have n N_pos = 3

have tuple index_tuple for i <= n, index_tuple[i] = i
index_tuple = (1, 2, 3)

have tuple real_tuple for i <= n, real_tuple[i] = R
(R, R, R) = real_tuple
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
fn have_tuple_and_have_cart_reject_bad_symbolic_definitions() {
    run_with_large_stack(
        "have_tuple_and_have_cart_reject_bad_symbolic_definitions",
        || {
            let cases = [
                (
                    "undefined dimension",
                    "have tuple f for i <= n, f[i] = i",
                    "identifier `n` not defined",
                ),
                (
                    "small dimension",
                    r#"
have n N_pos = 1
have tuple f for i <= n, f[i] = i
"#,
                    "have tuple/cart needs 2 <= n",
                ),
                (
                    "self reference",
                    r#"
have n N_pos = 3
have tuple f for i <= n, f[i] = f[i]
"#,
                    "identifier `f` not defined",
                ),
                (
                    "wrong tuple lhs",
                    r#"
have n N_pos = 3
have tuple f for i <= n, g[i] = i
"#,
                    "have tuple left side must index the tuple being defined",
                ),
                (
                    "wrong cart lhs",
                    r#"
have n N_pos = 3
have cart c for i <= n, proj(d, i) = i
"#,
                    "have cart left side must project the cart being defined",
                ),
            ];

            for (label, source_code, expected_message) in cases {
                let mut runtime = Runtime::new_with_builtin_code();
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
fn template_can_define_symbolic_tuple_and_cart() {
    run_with_large_stack("template_can_define_symbolic_tuple_and_cart", || {
        let source_code = r#"
template<n N_pos: 2 <= n>:
    have tuple tuple_by_dim for i <= n, tuple_by_dim[i] = i

$is_tuple(\tuple_by_dim<3>)
tuple_dim(\tuple_by_dim<3>) = 3
forall i closed_range(1, 3):
    \tuple_by_dim<3>[i] = i

template<n N_pos: 2 <= n>:
    have cart cart_by_dim for i <= n, proj(cart_by_dim, i) = R

$is_cart(\cart_by_dim<3>)
cart_dim(\cart_by_dim<3>) = 3
forall i closed_range(1, 3):
    proj(\cart_by_dim<3>, i) = R
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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
finite_set_size(power_set({1, 2, 3})) = 2^finite_set_size({1, 2, 3})
finite_set_size({1, 2, 3}) = 3
2^finite_set_size({1, 2, 3}) = 2^3 = 8
finite_set_size(power_set({1, 2, 3})) = 8
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut legacy_runtime = Runtime::new_with_builtin_code();
            legacy_runtime.new_file_path_new_env_new_name_scope("legacy_count_is_not_builtin");
            let (stmt_results, runtime_error) =
                run_source_code("count({1, 2}) = 2", &mut legacy_runtime);
            let (legacy_succeeded, legacy_output) = render_run_source_code_output(
                &legacy_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );

            assert!(
                !legacy_succeeded,
                "legacy count unexpectedly remained builtin:\n{}",
                legacy_output
            );

            let mut wrong_arity_runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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
fn set_builder_subset_inference_does_not_rebind_its_filter_domain() {
    run_with_large_stack(
        "set_builder_subset_inference_does_not_rebind_its_filter_domain",
        || {
            let source_code = r#"
have fn positive_identity(x R_pos) R = x
have fn filtered_positive_set(n N_pos) power_set(R_pos) = {y R_pos: y $in R_pos and positive_identity(y) > 0}
filtered_positive_set(1) $in power_set(R_pos)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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
fn builtin_nonempty_family_witness_can_be_named_with_have() {
    run_with_large_stack(
        "builtin_nonempty_family_witness_can_be_named_with_have",
        || {
            let source_code = r#"
have X nonempty_set:
    forall! x X => {$is_nonempty_set(x)}

have A X
$is_nonempty_set(A)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "builtin_nonempty_family_witness_can_be_named_with_have",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "builtin nonempty family witness test failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn general_cart_builtin_definition_choice_and_membership_inference() {
    run_with_large_stack(
        "general_cart_builtin_definition_choice_and_membership_inference",
        || {
            let source_code = r#"
have I set
have X nonempty_set:
    forall! x X => {$is_nonempty_set(x)}
have g fn(alpha I) X

$is_nonempty_set(general_cart(I, X, g))
general_cart(I, X, g) = {f fn(t I)cup(X): forall! alpha I => {f(alpha) $in g(alpha)}}
have c general_cart(I, X, g)
c $in fn(t I)cup(X)
forall alpha I:
    c(alpha) $in g(alpha)

have J set
have h fn(beta J) X
forall beta J:
    $is_nonempty_set(h(beta))
$is_nonempty_set(general_cart(J, X, h))
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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
    let output = to_latex_from_source_after_builtins(
        "1 = 1",
        "latex_output_is_fragment_without_default_packages",
    )
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
pub(super) fn python_extractor_outputs_supported_have_subset() {
    run_with_large_stack("python_extractor_outputs_supported_have_subset", || {
        let source_code = r#"
have q Q = 1
have z Z = 3

have fn as algo f(x R) R = x + 1
have fn as algo g(x R) R = f(x) + 2

have fn as algo max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
"#;

        let output = to_python_from_source_after_builtins(
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
        let output = to_python_from_source_after_builtins(
            "have s set = R",
            "python_extractor_skips_non_numeric_have_obj_equal",
        )
        .expect("non-numeric object definitions should be skipped");

        assert_eq!(output, "# No Python-extractable Litex definitions.");
    });
}

#[test]
fn python_extractor_rejects_standalone_algo() {
    run_with_large_stack("python_extractor_rejects_standalone_algo", || {
        let source_code = r#"
have fn f(x R) R = x

algo f(x):
    x
"#;

        let error = to_python_from_source_after_builtins(
            source_code,
            "python_extractor_rejects_standalone_algo",
        )
        .expect_err("standalone algo should not be extracted in v1");
        let error_text = format!("{:?}", error);
        assert!(error_text.contains("does not support standalone `algo`"));
    });
}

#[test]
fn python_extractor_rejects_non_real_function_parameters() {
    run_with_large_stack(
        "python_extractor_rejects_non_real_function_parameters",
        || {
            let source_code = "have fn as algo f(x Z) R = x";
            let error = to_python_from_source_after_builtins(
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
fn list_set_membership_implies_equality_or() {
    let source_code = r#"
forall a set:
    a = 1 or a = 2 or a = 3
    =>:
        a $in {1, 2, 3}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
