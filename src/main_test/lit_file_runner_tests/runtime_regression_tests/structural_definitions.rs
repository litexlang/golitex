use super::*;

#[test]
fn template_instantiation_prefers_angle_brackets() {
    let source_code = r#"
template<s set: s = s>:
    have id_on_set set = s

\id_on_set<R> = R
\id_on_set{R} = R
"#;

    let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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

            let mut runtime = Runtime::new();
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

            let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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
fn real_line_comparison_exist_witnesses_are_builtin_rules() {
    let source_code = r#"
have above R:
    above > 100
have below R:
    100 > below
have equal_to R:
    equal_to = 100
have distinct_from R:
    100 != distinct_from
exist a, b R st {a >= b}
exist a, b R st {b <= a}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "real_line_comparison_exist_witnesses_are_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "real-line comparison witnesses should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"builtin rule\"")
            && run_output.contains("exist: real-line comparison witness"),
        "real-line comparison witnesses should expose builtin provenance:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"type\": \"cite forall fact\""),
        "real-line comparison witnesses must not cite a source-level forall:\n{}",
        run_output
    );
}

#[test]
fn archimedean_reciprocal_bound_is_a_builtin_rule() {
    let source_code = r#"
forall epsilon R_pos:
    exist n N_pos st {1 / n < epsilon}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("archimedean_reciprocal_bound_is_a_builtin_rule");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "the Archimedean reciprocal bound should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist: Archimedean reciprocal bound"),
        "the Archimedean reciprocal bound should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn sufficiently_wide_real_intervals_have_integer_witnesses_as_builtin_rules() {
    let source_code = r#"
forall a, b R:
    a < b
    b - a > 1
    =>:
        exist c Z st {a < c < b}

forall a, b R:
    b - a >= 1
    =>:
        exist c Z st {a <= c <= b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "sufficiently_wide_real_intervals_have_integer_witnesses_as_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "wide real intervals should have integer witnesses:\n{}",
        run_output
    );
    for rule in [
        "exist: integer strictly inside a real interval wider than 1",
        "exist: integer inside a real interval of length at least 1",
    ] {
        assert!(
            run_output.contains(rule),
            "missing integer interval builtin provenance `{}`:\n{}",
            rule,
            run_output
        );
    }

    let mut short_interval_runtime = Runtime::new();
    short_interval_runtime.new_file_path_new_env_new_name_scope(
        "strict_real_interval_without_length_bound_has_no_integer_builtin_witness",
    );
    let (short_interval_results, short_interval_error) = run_source_code(
        r#"
forall a, b R:
    a < b
    =>:
        exist c Z st {a < c < b}
"#,
        &mut short_interval_runtime,
    );
    let (short_interval_succeeded, short_interval_output) = render_run_source_code_output(
        &short_interval_runtime,
        &short_interval_results,
        &short_interval_error,
        false,
    );
    assert!(
        !short_interval_succeeded,
        "a real interval without a length bound must not get an integer witness:\n{}",
        short_interval_output
    );
}

#[test]
fn finite_set_size_zero_is_not_nonempty_is_a_builtin_rule() {
    let source_code = r#"
forall S finite_set:
    finite_set_size(S) = 0
    =>:
        not $is_nonempty_set(S)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_set_size_zero_is_not_nonempty_is_a_builtin_rule",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a zero-size finite set should be empty:\n{}",
        run_output
    );
    assert!(
        run_output.contains("finite set size zero is not nonempty"),
        "the zero-size finite-set rule should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn negation_reverses_order_as_a_builtin_rule() {
    let source_code = r#"
forall x R:
    x < -5
    =>:
        -x > 5
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("negation_reverses_order_as_a_builtin_rule");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "negation should reverse a strict order:\n{}",
        run_output
    );
    assert!(
        run_output.contains("order: -x > y from x < -y"),
        "negation reversal should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn positive_real_powers_reflect_order_as_builtin_rules() {
    let source_code = r#"
forall a, b, q R_pos:
    a^q < b^q
    =>:
        a < b

forall a, b, q R_pos:
    a^q <= b^q
    =>:
        a <= b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "positive_real_powers_reflect_order_as_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "positive-real powers should reflect order on positive bases:\n{}",
        run_output
    );
    assert!(
        run_output.contains("a < b from positive bases and exponent, and a^q < b^q")
            && run_output.contains("a <= b from positive bases and exponent, and a^q <= b^q"),
        "the positive-power inverse rules should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn rational_integer_ratio_representation_is_a_builtin_rule() {
    let source_code = r#"
forall q Q:
    exist a Z, b Z_nz st {q = a / b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_integer_ratio_representation_is_a_builtin_rule",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "rational integer-ratio representation should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist: rational integer ratio representation"),
        "rational representation should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn rational_integer_ratio_representation_requires_a_rational_target() {
    let source_code = r#"
exist a Z, b Z_nz st {sqrt(2) = a / b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_integer_ratio_representation_requires_a_rational_target",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "the rational representation builtin must not apply to arbitrary reals:\n{}",
        run_output
    );
}

#[test]
fn real_line_comparison_builtins_require_real_operands() {
    run_with_large_stack(
        "real_line_comparison_builtins_require_real_operands",
        || {
            let positive_source = r#"
have a, b R
a = b or a < b or a > b
a <= b or a >= b
a > b or a <= b
exist x R st {x = a}
exist x R st {x > a}
"#;
            let mut positive_runtime = Runtime::new();
            positive_runtime.new_file_path_new_env_new_name_scope(
                "real_line_comparison_builtins_require_real_operands_positive",
            );
            let (positive_results, positive_error) =
                run_source_code(positive_source, &mut positive_runtime);
            let (positive_succeeded, positive_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_results,
                &positive_error,
                false,
            );
            assert!(
                positive_succeeded,
                "real-line comparison builtins should retain real examples:\n{}",
                positive_output
            );

            for (label, source_code) in [
                ("trichotomy", "have S, T set\nS = T or S < T or S > T"),
                ("comparability", "have S, T set\nS <= T or S >= T"),
                ("strict_non_strict_split", "have S, T set\nS > T or S <= T"),
                ("existence_equality", "have S set\nexist x R st {x = S}"),
                ("existence_order", "have S set\nexist x R st {x > S}"),
            ] {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    format!(
                        "real_line_comparison_builtins_require_real_operands_{}",
                        label
                    )
                    .as_str(),
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} must not apply a real-line rule to set operands:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn zero_product_split_requires_real_factors() {
    let positive_source = r#"
have a, b R
trust a * b = 0
a = 0 or b = 0
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime
        .new_file_path_new_env_new_name_scope("zero_product_split_requires_real_factors_positive");
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "zero-product splitting should retain real factors:\n{}",
        positive_output
    );
    assert!(
        positive_output.contains("zero_product_split"),
        "zero-product splitting should expose its builtin provenance:\n{}",
        positive_output
    );

    let non_real_source = r#"
have A, B set
trust A * B = 0
A = 0 or B = 0
"#;
    let mut non_real_runtime = Runtime::new();
    non_real_runtime
        .new_file_path_new_env_new_name_scope("zero_product_split_requires_real_factors_non_real");
    let (non_real_results, non_real_error) =
        run_source_code(non_real_source, &mut non_real_runtime);
    let (non_real_succeeded, non_real_output) =
        render_run_source_code_output(&non_real_runtime, &non_real_results, &non_real_error, false);
    assert!(
        !non_real_succeeded,
        "a non-real product must not become a zero-product premise:\n{}",
        non_real_output
    );
}

#[test]
fn known_forall_existential_matching_requires_exact_atomic_relation() {
    let equality_as_inequality = r#"
trust:
    forall a Z:
        exist b Z st {b = a}
have chosen Z:
    chosen != 100
"#;
    let mut equality_runtime = Runtime::new();
    equality_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_rejects_equality_as_inequality",
    );
    let (equality_results, equality_error) =
        run_source_code(equality_as_inequality, &mut equality_runtime);
    let (equality_succeeded, equality_output) =
        render_run_source_code_output(&equality_runtime, &equality_results, &equality_error, false);
    assert!(
        !equality_succeeded,
        "an equality witness must not verify a distinctness witness:\n{}",
        equality_output
    );

    let positive_as_negative = r#"
abstract_prop p(x)
trust:
    forall a Z:
        exist b Z st {$p(b)}
have chosen Z:
    not $p(chosen)
"#;
    let mut predicate_runtime = Runtime::new();
    predicate_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_rejects_positive_as_negative",
    );
    let (predicate_results, predicate_error) =
        run_source_code(positive_as_negative, &mut predicate_runtime);
    let (predicate_succeeded, predicate_output) = render_run_source_code_output(
        &predicate_runtime,
        &predicate_results,
        &predicate_error,
        false,
    );
    assert!(
        !predicate_succeeded,
        "a positive predicate witness must not verify a negated witness:\n{}",
        predicate_output
    );

    let exact_equality = r#"
trust:
    forall a Z:
        exist b Z st {b = a}
have chosen Z:
    chosen = 100
"#;
    let mut exact_runtime = Runtime::new();
    exact_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_still_accepts_exact_equality",
    );
    let (exact_results, exact_error) = run_source_code(exact_equality, &mut exact_runtime);
    let (exact_succeeded, exact_output) =
        render_run_source_code_output(&exact_runtime, &exact_results, &exact_error, false);
    assert!(
        exact_succeeded,
        "an exact existential relation should still instantiate:\n{}",
        exact_output
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

            let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2 and b1 = b2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("exist_unique_infers_component_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "exist! component uniqueness inference failed:\n{}",
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

    let mut runtime = Runtime::new();
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

    let mut runtime = Runtime::new();
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

        let mut runtime = Runtime::new();
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

        let mut runtime = Runtime::new();
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
fn have_fn_by_exist_rebinds_value_dependent_function_signature() {
    run_with_large_stack(
        "have_fn_by_exist_rebinds_value_dependent_function_signature",
        || {
            let source_code = r#"
have fn interval_identity by exist!:
    ? forall a, b R, x '[a, b]:
        a <= b
        =>:
            exist! y R st {y = x}
    witness exist y R st {y = x} from x:
        x = x
    forall y1, y2 R:
        y1 = x
        y2 = x
        =>:
            y1 = x = y2
    exist! y R st {y = x}

forall a, b R, x '[a, b]:
    a <= b
    =>:
        interval_identity(a, b, x) = x

have fn dependent_function_value by exist!:
    ? forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
        exist! y R st {y = f(x)}
    witness exist y R st {y = f(x)} from f(x):
        f(x) = f(x)
    forall y1, y2 R:
        y1 = f(x)
        y2 = f(x)
        =>:
            y1 = f(x) = y2
    exist! y R st {y = f(x)}

forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
    dependent_function_value(a, b, f, x) = f(x)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_rebinds_value_dependent_function_signature",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have fn by exist! should rebind forall parameters into its stored function signature:\n{}",
                run_output
            );
        },
    );
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

        let mut runtime = Runtime::new();
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

            let mut runtime = Runtime::new();
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

        let mut runtime = Runtime::new();
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

            let mut runtime = Runtime::new();
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

#[test]
fn elementary_set_elimination_and_subset_rules_are_builtin() {
    let source_code = r#"
have A, B, x set
trust x $in union(A, B)
x $in A or x $in B

trust not x $in A
not x $in intersect(A, B)

intersect(A, B) $subset A
intersect(A, B) $subset B
A $subset union(A, B)
B $subset union(A, B)
set_minus(A, B) $subset A
set_diff(A, B) = union(set_minus(A, B), set_minus(B, A))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "elementary_set_elimination_and_subset_rules_are_builtin",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "elementary set rules should verify without std facts:\n{}",
        run_output
    );
    for rule in [
        "intersection non-membership: non-member of the left side",
        "intersection subset operand",
        "operand subset union",
        "set minus subset left operand",
        "set diff as union of asymmetric differences",
    ] {
        assert!(
            run_output.contains(rule),
            "missing builtin rule `{rule}`:\n{}",
            run_output
        );
    }
}
