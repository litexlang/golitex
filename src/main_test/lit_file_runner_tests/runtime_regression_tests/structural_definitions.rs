use super::*;

#[test]
fn template_instantiation_prefers_angle_brackets() {
    let source_code = r#"
template<s set: s = s>:
    have id_on_set set = s

\id_on_set<R> = R
\id_on_set{R} = R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("template_instantiation_prefers_angle_brackets");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template_instantiation_prefers_angle_brackets failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("template<"),
        "template definition display should omit the redundant header name:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("template id_on_set"),
        "template definition display should not repeat the body-defined name in the header:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\\id_on_set<R> = R"),
        "template instantiation display should use angle brackets:\n{}",
        run_output
    );
}

#[test]
fn template_header_rejects_redundant_name() {
    let source_code = r#"
template id_on_set<s set>:
    have id_on_set set = s
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("template_header_rejects_redundant_name");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "template header with redundant name should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("template definition expects `template<...>:`"),
        "old template header syntax should report the new syntax:\n{}",
        run_output
    );
}

#[test]
fn template_can_use_struct_with_function_valued_fields() {
    run_with_large_stack(
        "template_can_use_struct_with_function_valued_fields",
        || {
            let source_code = r#"
struct Group<s set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        forall x, y, z s:
            op(x, op(y, z)) = op(op(x, y), z)
        forall x s:
            op(e, x) = x
        forall x s:
            op(x, e) = x
        forall x s:
            op(x, inv(x)) = e
        forall x s:
            op(inv(x), x) = e

template<s set>:
    have group_quotient fn (g &Group<s>) power_set(s)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "template_can_use_struct_with_function_valued_fields",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template_can_use_struct_with_function_valued_fields failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn struct_filter_predicate_unfolds_for_explicit_field_view() {
    run_with_large_stack(
        "struct_filter_predicate_unfolds_for_explicit_field_view",
        || {
            let source_code = r#"
prop is_group(s nonempty_set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s nonempty_set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $is_group(s, inv, op, e)

macro G "&Group<s>{g}"

claim:
    ? forall s nonempty_set, g &Group<s>, x s:
        @G.op(@G.inv(x), x) = @G.e
    @G.op(@G.inv(x), x) = @G.e
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "struct_filter_predicate_unfolds_for_explicit_field_view",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "struct_filter_predicate_unfolds_for_explicit_field_view failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn set_alias_to_fn_set_is_nonempty_and_registers_function_type() {
    let source_code = r#"
have T set = fn(i closed_range(1, 3), j closed_range(1, 3), k closed_range(1, 3)) R
have A T
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "set_alias_to_fn_set_is_nonempty_and_registers_function_type",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "set_alias_to_fn_set_is_nonempty_and_registers_function_type failed:\n{}",
        run_output
    );
}

#[test]
fn template_set_alias_to_fn_set_is_nonempty_and_registers_function_type() {
    let source_code = r#"
template<S set, n N_pos>:
    have tensor3 set = fn(i closed_range(1, n), j closed_range(1, n), k closed_range(1, n)) S

have A \tensor3<R, 3>
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "template_set_alias_to_fn_set_is_nonempty_and_registers_function_type",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template_set_alias_to_fn_set_is_nonempty_and_registers_function_type failed:\n{}",
        run_output
    );
}

#[test]
fn weak_order_does_not_recursively_prove_equality() {
    let source_code = r#"
have a, b R
trust a <= b
a = b
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("weak_order_does_not_recursively_prove_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "recursive equality/order proof should fail, but succeeded:\n{}",
        run_output
    );
}

#[test]
fn known_forall_instantiation_fills_middle_param_from_dom_facts() {
    run_with_large_stack(
        "known_forall_instantiation_fills_middle_param_from_dom_facts",
        || {
            let source_code = r#"
abstract_prop rel(X, x, y)

trust forall X set, x, y, z X:
    $rel(X, x, y)
    $rel(X, y, z)
    =>:
        $rel(X, x, z)

thm use_rel_trans_like:
    ? forall X set, a, b, c X:
        $rel(X, a, b)
        $rel(X, b, c)
        =>:
            $rel(X, a, c)
    $rel(X, a, c)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "known_forall_instantiation_fills_middle_param_from_dom_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "known forall instantiation should infer a middle parameter from known premises:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn zero_product_cancellation_does_not_recursively_reenter_equality() {
    let source_code = r#"
have a, b, k1, k2 N
trust:
    k1 = 0
    b = a * k1
b = a * k1 = a * 0 = 0
0 * k2 = 0
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "zero_product_cancellation_does_not_recursively_reenter_equality",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "zero-product cancellation recursion regression failed:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_infers_component_uniqueness_forall() {
    let source_code = r#"
abstract_prop p(a, b)
trust exist! a, b R st {$p(a, b)}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("exist_unique_infers_component_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "exist! component uniqueness inference failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("forall a1, b1 R, a2, b2 R:")
            && run_output.contains("a1 = a2 and b1 = b2"),
        "exist! should infer a component-wise uniqueness forall:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_component_uniqueness_proves_split_then_facts() {
    let source_code = r#"
abstract_prop p(a, b)
trust exist! a, b R st {$p(a, b)}
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2
        b1 = b2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "exist_unique_component_uniqueness_proves_split_then_facts",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "component uniqueness from exist! should prove split then-facts:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_still_accepts_tuple_uniqueness_forall() {
    let source_code = r#"
sketch:
    abstract_prop p(a, b)
    trust:
        exist a, b R st {$p(a, b)}
        forall a1, b1, a2, b2 R:
            $p(a1, b1)
            $p(a2, b2)
            =>:
                (a1, b1) = (a2, b2)
    exist! a, b R st {$p(a, b)}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("exist_unique_still_accepts_tuple_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "tuple-style uniqueness should still prove exist!:\n{}",
        run_output
    );
}

#[test]
fn have_fn_by_exist_accepts_question_goal_target() {
    run_with_large_stack("have_fn_by_exist_accepts_question_goal_target", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
trust forall x A:
    exist! y B st {$F(x, y)}

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("have_fn_by_exist_accepts_question_goal_target");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! prove target should succeed:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_prove_body_can_establish_target() {
    run_with_large_stack("have_fn_by_exist_prove_body_can_establish_target", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}
    trust exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "have_fn_by_exist_prove_body_can_establish_target",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! proof body should establish the target forall:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_releases_unique_witness_direction() {
    run_with_large_stack("have_fn_by_exist_releases_unique_witness_direction", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}
    trust exist! y B st {$F(x, y)}

forall x A, y B:
    $F(x, y)
    =>:
        y = f(x)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "have_fn_by_exist_releases_unique_witness_direction",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! should release the unique witness direction:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_unique_witness_direction_keeps_all_body_facts() {
    run_with_large_stack(
        "have_fn_by_exist_unique_witness_direction_keeps_all_body_facts",
        || {
            let source_code = r#"
abstract_prop F(x, y)
abstract_prop G(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y), $G(x, y)}
    trust exist! y B st {$F(x, y), $G(x, y)}

forall x A, y B:
    $F(x, y)
    $G(x, y)
    =>:
        y = f(x)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_unique_witness_direction_keeps_all_body_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have fn by exist! uniqueness direction should keep every exist! body fact:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_exist_requires_question_goal() {
    run_with_large_stack("have_fn_by_exist_requires_question_goal", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
trust forall x A:
    exist! y B st {$F(x, y)}

have fn f by exist!:
    forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("have_fn_by_exist_requires_question_goal");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "direct forall form should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("expects a `? forall ...` goal block"),
            "direct forall rejection should report the expected goal shape:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_question_goal_requires_forall_target() {
    run_with_large_stack(
        "have_fn_by_exist_question_goal_requires_forall_target",
        || {
            let source_code = r#"
have fn f by exist!:
    ? 1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_question_goal_requires_forall_target",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "non-forall prove target should fail:\n{}",
                run_output
            );
            assert!(
                run_output.contains("goal must be a single `forall` fact"),
                "non-forall prove target should report the expected shape:\n{}",
                run_output
            );
        },
    );
}
