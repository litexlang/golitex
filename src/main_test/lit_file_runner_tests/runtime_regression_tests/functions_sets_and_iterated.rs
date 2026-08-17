use super::*;

#[test]
fn checked_definition_reduction_uses_only_terminating_equality_leaves() {
    let source_code = r#"
have fn left(k N+) R = k
have fn right(k N+) R = k + 1
have fn combined(k N+) R = left(k) + right(k)

left(1) = 1
right(1) = 1 + 1
have value R = 1 + (1 + 1)
value = combined(1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "checked_definition_reduction_uses_stored_function_leaf_equalities",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a direct checked-definition reduction should compare structural leaves through stored non-forall equalities or direct computation:\n{}",
        run_output
    );

    let recursive_unfold_source = r#"
have fn left(k N+) R = k
have fn right(k N+) R = k + 1
have fn combined(k N+) R = left(k) + right(k)

have value R = 1 + (1 + 1)
value = combined(1)
"#;
    let mut recursive_unfold_runtime = Runtime::new();
    recursive_unfold_runtime.new_file_path_new_env_new_name_scope(
        "checked_definition_reduction_does_not_unfold_named_child_definitions",
    );
    let (stmt_results, runtime_error) =
        run_source_code(recursive_unfold_source, &mut recursive_unfold_runtime);
    let (run_succeeded, run_output) = render_run_source_code_output(
        &recursive_unfold_runtime,
        &stmt_results,
        &runtime_error,
        false,
    );
    assert!(
        !run_succeeded,
        "structural leaves must not recursively unfold more function definitions:\n{}",
        run_output
    );

    let normalization_leaf_source = r#"
have q R
have fn with_zero(t R) cart(R, R) = (0 + t, t)
with_zero(q) = (q, q)
"#;
    let mut normalization_leaf_runtime = Runtime::new();
    normalization_leaf_runtime.new_file_path_new_env_new_name_scope(
        "checked_definition_reduction_uses_bounded_normalization_for_structural_leaves",
    );
    let (stmt_results, runtime_error) =
        run_source_code(normalization_leaf_source, &mut normalization_leaf_runtime);
    let (run_succeeded, run_output) = render_run_source_code_output(
        &normalization_leaf_runtime,
        &stmt_results,
        &runtime_error,
        false,
    );
    assert!(
        run_succeeded,
        "a structural leaf may use bounded obligation-free symbolic normalization:\n{}",
        run_output
    );

    let direct_normalization_source = r#"
have a, t R
a * t = a * t + 0
"#;
    let mut direct_normalization_runtime = Runtime::new();
    direct_normalization_runtime.new_file_path_new_env_new_name_scope(
        "terminating_equality_leaf_uses_bounded_normalization",
    );
    let (stmt_results, runtime_error) = run_source_code(
        direct_normalization_source,
        &mut direct_normalization_runtime,
    );
    let (run_succeeded, run_output) = render_run_source_code_output(
        &direct_normalization_runtime,
        &stmt_results,
        &runtime_error,
        false,
    );
    assert!(
        run_succeeded,
        "a direct comparison may use bounded obligation-free normalization:\n{}",
        run_output
    );

    let forall_leaf_source = r#"
trust have f, h fn(t R) R
trust forall t R:
    h(f(t)) = f(t)
have fn wrapped(t R) cart(R, R) = (h(f(t)), t)
have value cart(R, R) = wrapped(1)
value = (f(1), 1)
"#;
    let mut forall_leaf_runtime = Runtime::new();
    forall_leaf_runtime.new_file_path_new_env_new_name_scope(
        "checked_definition_reduction_does_not_use_forall_for_structural_leaves",
    );
    let (stmt_results, runtime_error) =
        run_source_code(forall_leaf_source, &mut forall_leaf_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&forall_leaf_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "structural leaves must not instantiate known forall facts:\n{}",
        run_output
    );

    let invalid_source = r#"
have fn guarded(k N+: 2 <= k) R = k
guarded(1) = 1
"#;
    let mut invalid_runtime = Runtime::new();
    invalid_runtime
        .new_file_path_new_env_new_name_scope("definition_reduction_does_not_bypass_domain_facts");
    let (stmt_results, runtime_error) = run_source_code(invalid_source, &mut invalid_runtime);
    let (run_succeeded, _) =
        render_run_source_code_output(&invalid_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "checked-definition reduction must not bypass the function's domain facts"
    );

    let implicit_alias_source = r#"
trust have f fn(x, y R) R
trust have a R
trust a = 1
have selected R = f(a, 0)
selected = f(1, 0)
"#;
    let mut implicit_alias_runtime = Runtime::new();
    implicit_alias_runtime.new_file_path_new_env_new_name_scope(
        "known_congruence_does_not_reopen_an_alias_representative",
    );
    let (stmt_results, runtime_error) =
        run_source_code(implicit_alias_source, &mut implicit_alias_runtime);
    let (run_succeeded, run_output) = render_run_source_code_output(
        &implicit_alias_runtime,
        &stmt_results,
        &runtime_error,
        false,
    );
    assert!(
        !run_succeeded,
        "an alias must not be reopened as an equality representative for structural congruence:\n{}",
        run_output
    );

    let one_argument_source = r#"
trust have f fn(x, y R) R
trust have a R
trust a = 1
have selected R = f(a, 0)
selected = f(a, 0) = f(1, 0)
"#;
    let mut one_argument_runtime = Runtime::new();
    one_argument_runtime.new_file_path_new_env_new_name_scope(
        "explicit_alias_bridge_then_known_argument_congruence",
    );
    let (stmt_results, runtime_error) =
        run_source_code(one_argument_source, &mut one_argument_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&one_argument_runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "an explicit alias bridge should expose the direct structural congruence step:\n{}",
        run_output
    );

    let two_argument_source = r#"
trust have f fn(x, y R) R
trust have a, b R
trust a = 1
trust b = 2
have selected R = f(a, b)
selected = f(a, b) = f(1, 2)
"#;
    let mut two_argument_runtime = Runtime::new();
    two_argument_runtime
        .new_file_path_new_env_new_name_scope("explicit_alias_bridge_then_two_argument_congruence");
    let (stmt_results, runtime_error) =
        run_source_code(two_argument_source, &mut two_argument_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&two_argument_runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "the explicit bridge should allow all corresponding arguments to use known equalities:\n{}",
        run_output
    );

    let missing_argument_equality_source = r#"
trust have f fn(x, y R) R
trust have a, b R
trust a = 1
f(a, b) = f(1, 2)
"#;
    let mut missing_argument_equality_runtime = Runtime::new();
    missing_argument_equality_runtime.new_file_path_new_env_new_name_scope(
        "known_congruence_requires_every_corresponding_argument_equality",
    );
    let (stmt_results, runtime_error) = run_source_code(
        missing_argument_equality_source,
        &mut missing_argument_equality_runtime,
    );
    let (run_succeeded, run_output) = render_run_source_code_output(
        &missing_argument_equality_runtime,
        &stmt_results,
        &runtime_error,
        false,
    );
    assert!(
        !run_succeeded,
        "componentwise congruence must fail when one paired argument equality is missing:\n{}",
        run_output
    );

    let curried_source = r#"
trust have f fn(x, y R) R
trust have g fn(m, n R) fn(u, v R) R
trust have a, b R
trust a = 3
trust b = 4
trust f = g(1, 2)
f(a, b) = g(1, 2)(3, 4)
"#;
    let mut curried_runtime = Runtime::new();
    curried_runtime
        .new_file_path_new_env_new_name_scope("known_congruence_aligns_curried_applications");
    let (stmt_results, runtime_error) = run_source_code(curried_source, &mut curried_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&curried_runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "curried applications should align trailing argument groups and compare the remaining function parts:\n{}",
        run_output
    );
}

#[test]
fn template_aliases_require_an_explicit_definition_equality() {
    let setup = r#"
struct AdditiveCarrier<v nonempty_set>:
    zero v
    add fn(a, b v) v

template<s nonempty_set, VSet, WSet nonempty_set, V &AdditiveCarrier<VSet>, W &AdditiveCarrier<WSet>>:
    have fn product_add(x, y cart(VSet, WSet)) cart(VSet, WSet) = (V.add(x[1], y[1]), W.add(x[2], y[2]))

have s, VSet, WSet nonempty_set
have v0 VSet
have w0 WSet
have V &AdditiveCarrier<VSet> = (v0, fn(a, b VSet) VSet {v0})
have W &AdditiveCarrier<WSet> = (w0, fn(a, b WSet) WSet {w0})
have x, y cart(VSet, WSet)
have xy cart(VSet, WSet) = \product_add<s, VSet, WSet, V, W>(x, y)
have expected cart(VSet, WSet) = (V.add(x[1], y[1]), W.add(x[2], y[2]))
"#;

    let implicit_source = format!("{setup}\nxy = expected\n");
    let mut implicit_runtime = Runtime::new();
    implicit_runtime.new_file_path_new_env_new_name_scope(
        "template_aliases_do_not_open_an_equality_representative_graph",
    );
    let (stmt_results, runtime_error) = run_source_code(&implicit_source, &mut implicit_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&implicit_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "two aliases must not trigger representative enumeration plus definition reduction:\n{}",
        run_output
    );

    let explicit_source = format!(
        r#"{setup}
\product_add<s, VSet, WSet, V, W>(x, y) = (V.add(x[1], y[1]), W.add(x[2], y[2]))
xy = expected
xy = (V.add(x[1], y[1]), W.add(x[2], y[2]))
"#
    );
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("explicit_template_definition_reduction");
    let (stmt_results, runtime_error) = run_source_code(&explicit_source, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "an explicit checked template definition equality should connect both aliases:\n{}",
        run_output
    );
}

#[test]
fn checked_definition_reduction_allows_direct_pure_computation() {
    let source_code = r#"
have fn square(t R) R = t^2
square(2) = 4
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "checked_definition_reduction_allows_direct_pure_computation",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "one checked definition reduction may finish by direct terminating computation:\n{}",
        run_output
    );
}

#[test]
fn structural_known_congruence_compares_interval_endpoints() {
    let source_code = r#"
have a, b, c, d R
trust a = c
trust b = d
'(a, b] = '(c, d]
'(,a] = '(,c]
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "structural_known_congruence_compares_interval_endpoints",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "bounded intervals and rays should share the central known-congruence route:\n{}",
        run_output
    );
}

#[test]
fn cart_valued_function_membership_does_not_reenter_projection_well_definedness() {
    run_with_large_stack(
        "cart_valued_function_membership_does_not_reenter_projection_well_definedness",
        || {
            let source_code = r#"
have fn pair_N(p, q cart(N, N)) cart(N, N) = (p[1] + q[1], p[2] + q[2])

forall p, q cart(N, N):
    pair_N(p, q) $in cart(N, N)
    pair_N(p, q)[1] $in N
    pair_N(p, q)[2] $in N
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "cart_valued_function_membership_does_not_reenter_projection_well_definedness",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "Cartesian-return projections should use the already registered return metadata:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_function_application_in_unfolded_forall_uses_pointwise_fact() {
    run_with_large_stack(
        "anonymous_function_application_in_unfolded_forall_uses_pointwise_fact",
        || {
            let source_code = r#"
prop simplex_shape(n N, v fn(i1 range(0, n)) R):
    forall i1 range(0, n):
        v(i1) >= 0
    finite_set_sum(range(0, n), v) = 1

claim:
    ? forall n N, a, b fn(i1 range(0, n)) R:
        forall i1 range(0, n):
            (a(i1) + b(i1)) / 2 >= 0
        finite_set_sum(range(0, n), fn(i1 range(0, n)) R {(a(i1) + b(i1)) / 2}) = 1
        =>:
            $simplex_shape(n, fn(i1 range(0, n)) R {(a(i1) + b(i1)) / 2})
    by def $simplex_shape(n, fn(i1 range(0, n)) R {(a(i1) + b(i1)) / 2})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_function_application_in_unfolded_forall_uses_pointwise_fact",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "unfolded forall should beta-reduce the anonymous function application before using the pointwise fact:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn obtain_body_well_defined_can_use_forall_domain_fact() {
    run_with_large_stack(
        "obtain_body_well_defined_can_use_forall_domain_fact",
        || {
            let source_code = r#"
prop image_like(S, T set, f fn(x S) T, A, B set):
    A $subset S
    forall y B:
        exist a A st {y = f(a)}

claim:
    ? forall S, T set, f fn(x S) T, A, B set, x S:
        A $subset S
        $image_like(S, T, f, A, B)
        f(x) $in B
        =>:
            x = x
    claim:
        ? forall a A:
            a $in S
        a $in S
    obtain a from exist a A st {f(x) = f(a)}
    a $in S
    f(x) = f(a)
    x = x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "obtain_body_well_defined_can_use_forall_domain_fact",
            );
            runtime.detail_output = true;
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "obtain_body_well_defined_can_use_forall_domain_fact failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"object definition by existence\""),
                "obtain from exist should report the semantic statement type\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(&run_output, "have by exist");
            assert!(
                !run_output.contains("HaveExistObjStmt"),
                "obtain from exist should not report the legacy statement type\n{}",
                run_output
            );
        },
    );
}

#[test]
fn function_space_membership_uses_same_domain_pointwise_values() {
    run_with_large_stack(
        "function_space_membership_uses_same_domain_pointwise_values",
        || {
            let source_code = r#"
claim:
    ? forall I set, X set, f fn(alpha I) big_union({X}):
        forall alpha I:
            f(alpha) $in X
        =>:
            f $in fn(alpha I) X
    forall alpha I:
        f(alpha) $in X
    f $in fn(alpha I) X
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "function_space_membership_uses_same_domain_pointwise_values",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "same-domain pointwise function membership failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn function_space_membership_freshens_generated_pointwise_binder() {
    run_with_large_stack(
        "function_space_membership_freshens_generated_pointwise_binder",
        || {
            let invalid_source_code = r#"
claim:
    ? forall x R, f fn(t R) R:
        f(x) = 0
        =>:
            f $in fn(x R) {0}
    f(x) = 0
    f $in fn(x R) {0}
"#;

            let mut invalid_runtime = Runtime::new();
            invalid_runtime.new_file_path_new_env_new_name_scope(
                "function_space_membership_rejects_captured_outer_value",
            );
            let (invalid_results, invalid_error) =
                run_source_code(invalid_source_code, &mut invalid_runtime);
            let (invalid_succeeded, invalid_output) = render_run_source_code_output(
                &invalid_runtime,
                &invalid_results,
                &invalid_error,
                false,
            );

            // Countermodel: outer x = 0 and f(t) = t. The premise f(x) = 0 holds,
            // but f does not map every real into {0}.
            assert!(
                !invalid_succeeded,
                "one captured point value must not prove whole-function membership:\n{}",
                invalid_output
            );

            let valid_source_code = r#"
claim:
    ? forall x R, f fn(t R) R:
        forall y R:
            f(y) $in {y}
        =>:
            f $in fn(z R) {z}
    forall y R:
        f(y) $in {y}
    f $in fn(z R) {z}
"#;

            let mut valid_runtime = Runtime::new();
            valid_runtime.new_file_path_new_env_new_name_scope(
                "function_space_membership_accepts_full_pointwise_proof_with_same_name",
            );
            let (valid_results, valid_error) =
                run_source_code(valid_source_code, &mut valid_runtime);
            let (valid_succeeded, valid_output) =
                render_run_source_code_output(&valid_runtime, &valid_results, &valid_error, false);
            assert!(
                valid_succeeded,
                "freshening must preserve a full pointwise proof:\n{}",
                valid_output
            );
        },
    );
}

#[test]
fn function_space_membership_assumes_generated_domain_facts_before_application_check() {
    run_with_large_stack(
        "function_space_membership_assumes_generated_domain_facts_before_application_check",
        || {
            let source_code = r#"
have fn f(x R: x >= 0) R = 0

forall y R:
    y >= 0
    =>:
        f(y) $in {0}

f $in fn(x R: x >= 0) {0}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "function_space_membership_assumes_generated_domain_facts_before_application_check",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "generated pointwise application must be checked after its domain facts are assumed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn parameter_membership_uses_direct_known_subset_on_demand() {
    run_with_large_stack(
        "parameter_membership_uses_direct_known_subset_on_demand",
        || {
            let source_code = r#"
have S0, T0 nonempty_set
trust S0 $subset T0
have x0 S0
x0 $in T0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "parameter_membership_uses_direct_known_subset_on_demand",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "parameter membership should use one directly known subset on demand:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn membership_builtin_does_not_rewrite_positive_order_goals() {
    run_with_large_stack(
        "membership_builtin_does_not_rewrite_positive_order_goals",
        || {
            let order_only_source = r#"
forall A power_set(R+), x A:
    0 < x
"#;
            let mut order_only_runtime = Runtime::new();
            order_only_runtime.new_file_path_new_env_new_name_scope(
                "membership_builtin_does_not_rewrite_positive_order_goals",
            );
            let (stmt_results, runtime_error) =
                run_source_code(order_only_source, &mut order_only_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &order_only_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                !run_succeeded,
                "the membership feature must not synthesize a positive-set premise from an order goal:\n{}",
                run_output
            );

            let explicit_membership_source = r#"
forall A power_set(R+), x A:
    x $in R+
    0 < x
"#;
            let mut explicit_runtime = Runtime::new();
            explicit_runtime.new_file_path_new_env_new_name_scope(
                "explicit_positive_membership_can_keep_inference_moving",
            );
            let (stmt_results, runtime_error) =
                run_source_code(explicit_membership_source, &mut explicit_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &explicit_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                run_succeeded,
                "an explicit accepted R+ membership may still trigger existing order inference:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn restricted_membership_builtin_uses_subset_in_both_fact_orders() {
    run_with_large_stack(
        "restricted_membership_builtin_uses_subset_in_both_fact_orders",
        || {
            let cases = [
                (
                    "restricted_membership_owner_before_subset",
                    r#"
have x, A, B set
trust x $in A
trust A $subset B
"#,
                ),
                (
                    "restricted_membership_subset_before_owner",
                    r#"
have x, A, B set
trust A $subset B
trust x $in A
"#,
                ),
            ];

            for (label, source_code) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} could not establish the indexed source facts:\n{}",
                    label, run_output
                );

                let x_symbol = runtime
                    .resolved_identifier_symbol("x")
                    .expect("x should have a runtime symbol");
                let b_symbol = runtime
                    .resolved_identifier_symbol("B")
                    .expect("B should have a runtime symbol");
                let target: AtomicFact = InFact::new(
                    Identifier::new_bound("x".to_string(), x_symbol).into(),
                    Identifier::new_bound("B".to_string(), b_symbol).into(),
                    default_line_file(),
                )
                .into();
                assert!(
                    !runtime.cache_known_facts_contains(&target.to_string()).0,
                    "{} must not eagerly materialize x in B",
                    label
                );
                let result = runtime
                    .verify_atomic_fact_restricted_known_builtin(
                        &target,
                        &UseContextVerifyState::new(0, false),
                    )
                    .unwrap_or_else(|error| {
                        panic!("{} restricted membership check failed: {}", label, error)
                    });
                assert!(
                    result.is_true(),
                    "{} should prove x in B through one direct subset edge",
                    label
                );
                assert!(
                    !runtime.cache_known_facts_contains(&target.to_string()).0,
                    "{} should leave the on-demand result unstored",
                    label
                );
            }
        },
    );
}

#[test]
fn restricted_membership_builtin_accepts_power_set_and_superset_edges() {
    run_with_large_stack(
        "restricted_membership_builtin_accepts_power_set_and_superset_edges",
        || {
            let cases = [
                (
                    "restricted_membership_power_set_edge",
                    r#"
have x, A, B set
trust A $in power_set(B)
trust x $in A
"#,
                ),
                (
                    "restricted_membership_superset_edge_with_multiple_owners",
                    r#"
have x, A, B, unrelated set
trust B $superset A
trust x $in unrelated
trust x $in A
"#,
                ),
            ];

            for (label, source_code) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} could not establish the indexed source facts:\n{}",
                    label, run_output
                );

                let x_symbol = runtime
                    .resolved_identifier_symbol("x")
                    .expect("x should have a runtime symbol");
                let b_symbol = runtime
                    .resolved_identifier_symbol("B")
                    .expect("B should have a runtime symbol");
                let target: AtomicFact = InFact::new(
                    Identifier::new_bound("x".to_string(), x_symbol).into(),
                    Identifier::new_bound("B".to_string(), b_symbol).into(),
                    default_line_file(),
                )
                .into();
                let result = runtime
                    .verify_atomic_fact_restricted_known_builtin(
                        &target,
                        &UseContextVerifyState::new(0, false),
                    )
                    .unwrap_or_else(|error| {
                        panic!("{} restricted membership check failed: {}", label, error)
                    });
                assert!(
                    result.is_true(),
                    "{} should prove x in B through its direct inclusion edge",
                    label
                );
            }
        },
    );
}

#[test]
fn restricted_membership_builtin_is_direct_and_forward_only() {
    run_with_large_stack(
        "restricted_membership_builtin_is_direct_and_forward_only",
        || {
            let source_code = r#"
have x, A, B, U set
trust x $in A
trust A $subset B
trust B $subset U
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "restricted_membership_builtin_is_direct_and_forward_only",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "could not establish the direct-only source facts:\n{}",
                run_output
            );

            let x_symbol = runtime
                .resolved_identifier_symbol("x")
                .expect("x should have a runtime symbol");
            let b_symbol = runtime
                .resolved_identifier_symbol("B")
                .expect("B should have a runtime symbol");
            let direct_target: AtomicFact = InFact::new(
                Identifier::new_bound("x".to_string(), x_symbol.clone()).into(),
                Identifier::new_bound("B".to_string(), b_symbol).into(),
                default_line_file(),
            )
            .into();
            let direct_result = runtime
                .verify_atomic_fact_restricted_known_builtin(
                    &direct_target,
                    &UseContextVerifyState::new(0, false),
                )
                .unwrap_or_else(|error| {
                    panic!("direct restricted membership check failed: {}", error)
                });
            assert!(
                direct_result.is_true(),
                "the first direct subset edge should prove x in B"
            );

            let u_symbol = runtime
                .resolved_identifier_symbol("U")
                .expect("U should have a runtime symbol");
            let transitive_target: AtomicFact = InFact::new(
                Identifier::new_bound("x".to_string(), x_symbol).into(),
                Identifier::new_bound("U".to_string(), u_symbol).into(),
                default_line_file(),
            )
            .into();
            let transitive_result = runtime
                .verify_atomic_fact_restricted_known_builtin(
                    &transitive_target,
                    &UseContextVerifyState::new(0, false),
                )
                .unwrap_or_else(|error| {
                    panic!("transitive restricted membership check failed: {}", error)
                });
            assert!(
                !transitive_result.is_true(),
                "restricted membership must not traverse A subset B subset U"
            );

            let reverse_source_code = r#"
have y, S, T set
trust y $in T
trust S $subset T
"#;
            let mut reverse_runtime = Runtime::new();
            reverse_runtime.new_file_path_new_env_new_name_scope(
                "restricted_membership_builtin_does_not_reverse_subset",
            );
            let (stmt_results, runtime_error) =
                run_source_code(reverse_source_code, &mut reverse_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &reverse_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                run_succeeded,
                "could not establish the reverse-safety source facts:\n{}",
                run_output
            );

            let y_symbol = reverse_runtime
                .resolved_identifier_symbol("y")
                .expect("y should have a runtime symbol");
            let s_symbol = reverse_runtime
                .resolved_identifier_symbol("S")
                .expect("S should have a runtime symbol");
            let reverse_target: AtomicFact = InFact::new(
                Identifier::new_bound("y".to_string(), y_symbol).into(),
                Identifier::new_bound("S".to_string(), s_symbol).into(),
                default_line_file(),
            )
            .into();
            let reverse_result = reverse_runtime
                .verify_atomic_fact_restricted_known_builtin(
                    &reverse_target,
                    &UseContextVerifyState::new(0, false),
                )
                .unwrap_or_else(|error| {
                    panic!("reverse restricted membership check failed: {}", error)
                });
            assert!(
                !reverse_result.is_true(),
                "restricted membership must not infer y in S from y in T and S subset T"
            );
        },
    );
}

#[test]
fn restricted_membership_builtin_uses_equal_sets_and_ignores_negative_facts() {
    run_with_large_stack(
        "restricted_membership_builtin_uses_equal_sets_and_ignores_negative_facts",
        || {
            let equal_sets_source = r#"
have x, y, A, A_equal, B, B_equal set
trust x = y
trust A = A_equal
trust B = B_equal
trust x $in A
trust A $subset B
"#;
            let mut equal_sets_runtime = Runtime::new();
            equal_sets_runtime.new_file_path_new_env_new_name_scope(
                "restricted_membership_builtin_uses_equal_sets",
            );
            let (stmt_results, runtime_error) =
                run_source_code(equal_sets_source, &mut equal_sets_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &equal_sets_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                run_succeeded,
                "could not establish the equal-set source facts:\n{}",
                run_output
            );

            let y_symbol = equal_sets_runtime
                .resolved_identifier_symbol("y")
                .expect("y should have a runtime symbol");
            let b_equal_symbol = equal_sets_runtime
                .resolved_identifier_symbol("B_equal")
                .expect("B_equal should have a runtime symbol");
            let equal_set_target: AtomicFact = InFact::new(
                Identifier::new_bound("y".to_string(), y_symbol).into(),
                Identifier::new_bound("B_equal".to_string(), b_equal_symbol).into(),
                default_line_file(),
            )
            .into();
            let equal_set_result = equal_sets_runtime
                .verify_atomic_fact_restricted_known_builtin(
                    &equal_set_target,
                    &UseContextVerifyState::new(0, false),
                )
                .expect("equal-set membership verification should not error");
            assert!(
                equal_set_result.is_true(),
                "equal elements and equal endpoint sets should share the direct membership edge"
            );

            let negative_cases = [
                (
                    "restricted_membership_negative_subset",
                    r#"
have n, S, T set
trust n $in S
trust not S $subset T
"#,
                ),
                (
                    "restricted_membership_negative_owner",
                    r#"
have n, S, T set
trust not n $in S
trust S $subset T
"#,
                ),
            ];
            for (label, source_code) in negative_cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} could not establish its negative source fact:\n{}",
                    label, run_output
                );

                let n_symbol = runtime
                    .resolved_identifier_symbol("n")
                    .expect("n should have a runtime symbol");
                let t_symbol = runtime
                    .resolved_identifier_symbol("T")
                    .expect("T should have a runtime symbol");
                let target: AtomicFact = InFact::new(
                    Identifier::new_bound("n".to_string(), n_symbol).into(),
                    Identifier::new_bound("T".to_string(), t_symbol).into(),
                    default_line_file(),
                )
                .into();
                let result = runtime
                    .verify_atomic_fact_restricted_known_builtin(
                        &target,
                        &UseContextVerifyState::new(0, false),
                    )
                    .unwrap_or_else(|error| {
                        panic!("{} restricted membership check failed: {}", label, error)
                    });
                assert!(
                    !result.is_true(),
                    "{} must not index a negated membership or subset fact",
                    label
                );
            }
        },
    );
}

#[test]
fn membership_indexes_follow_try_commit_and_rollback() {
    run_with_large_stack("membership_indexes_follow_try_commit_and_rollback", || {
        let committed_source = r#"
try:
    have x, A, B set
    trust x $in A
    trust A $subset B
"#;
        let mut committed_runtime = Runtime::new();
        committed_runtime
            .new_file_path_new_env_new_name_scope("membership_indexes_follow_try_commit");
        let (stmt_results, runtime_error) =
            run_source_code(committed_source, &mut committed_runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&committed_runtime, &stmt_results, &runtime_error, false);
        assert!(
            run_succeeded,
            "a successful try block should commit membership indexes:\n{}",
            run_output
        );

        let x_symbol = committed_runtime
            .resolved_identifier_symbol("x")
            .expect("committed x should have a runtime symbol");
        let b_symbol = committed_runtime
            .resolved_identifier_symbol("B")
            .expect("committed B should have a runtime symbol");
        let committed_target: AtomicFact = InFact::new(
            Identifier::new_bound("x".to_string(), x_symbol).into(),
            Identifier::new_bound("B".to_string(), b_symbol).into(),
            default_line_file(),
        )
        .into();
        let committed_result = committed_runtime
            .verify_atomic_fact_restricted_known_builtin(
                &committed_target,
                &UseContextVerifyState::new(0, false),
            )
            .expect("committed membership verification should not error");
        assert!(
            committed_result.is_true(),
            "a committed try block should preserve its owner and inclusion indexes"
        );

        let failed_source = r#"
try:
    have failed_x, failed_A, failed_B set
    trust failed_x $in failed_A
    trust failed_A $subset failed_B
    0 = 1
"#;
        let mut failed_runtime = Runtime::new();
        failed_runtime
            .new_file_path_new_env_new_name_scope("membership_indexes_follow_try_rollback");
        let before_counts = {
            let environment = failed_runtime.top_level_env();
            (
                environment
                    .known_owner_sets
                    .values()
                    .map(|owner_sets| owner_sets.len())
                    .sum::<usize>(),
                environment
                    .known_direct_supersets
                    .values()
                    .map(|supersets| supersets.len())
                    .sum::<usize>(),
            )
        };
        let (_, runtime_error) = run_source_code(failed_source, &mut failed_runtime);
        assert!(
            runtime_error.is_some(),
            "the deliberately false final step should roll back the try block"
        );
        let after_counts = {
            let environment = failed_runtime.top_level_env();
            (
                environment
                    .known_owner_sets
                    .values()
                    .map(|owner_sets| owner_sets.len())
                    .sum::<usize>(),
                environment
                    .known_direct_supersets
                    .values()
                    .map(|supersets| supersets.len())
                    .sum::<usize>(),
            )
        };
        assert_eq!(
            after_counts, before_counts,
            "a failed try block must not leak owner or direct-superset index entries"
        );
    });
}

#[test]
fn direct_membership_builtin_uses_facts_introduced_by_trust() {
    run_with_large_stack(
        "direct_membership_builtin_uses_facts_introduced_by_trust",
        || {
            let cases = [
                (
                    "trusted_direct_inclusion",
                    r#"
have x R
have B set
trust R $subset B

thm membership_from_trusted_inclusion:
    ? forall y set:
        x $in B
    x $in B
"#,
                ),
                (
                    "trusted_owner_membership",
                    r#"
have x R
trust x $in {1}
{1} $subset {1, 2}

thm membership_from_trusted_owner:
    ? forall y set:
        x $in {1, 2}
    x $in {1, 2}
"#,
                ),
            ];

            for (label, source_code) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} should verify through the direct membership builtin:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn membership_indexes_are_available_through_qualified_exports() {
    run_with_large_stack(
        "membership_indexes_are_available_through_qualified_exports",
        || {
            let project_root = std::env::temp_dir().join(format!(
                "litex-membership-qualified-export-{}",
                std::process::id()
            ));
            let _ = std::fs::remove_dir_all(&project_root);
            std::fs::create_dir_all(&project_root)
                .expect("create qualified-membership project fixture");
            std::fs::write(
                project_root.join("litex.config"),
                "[hierarchy]\nmodule\n\n[export]\nsource = \"./source.lit\"\nmain = \"./main.lit\"\n",
            )
            .expect("write qualified-membership project config");
            std::fs::write(
                project_root.join("source.lit"),
                "have x_import, A_import, B_import set\ntrust x_import $in A_import\ntrust A_import $subset B_import\n",
            )
            .expect("write qualified-membership source file");
            std::fs::write(
                project_root.join("main.lit"),
                "source::x_import $in source::B_import\n",
            )
            .expect("write qualified-membership target file");

            let repository_path = project_root
                .to_str()
                .expect("temporary project path should be UTF-8");
            let (run_succeeded, run_output) = run_repository_with_output(
                repository_path,
                false,
                false,
                OutputLanguage::English,
                false,
            );
            let _ = std::fs::remove_dir_all(&project_root);
            assert!(
                run_succeeded,
                "qualified exports should retain owner and inclusion indexes:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn set_builder_parameter_inherits_known_numeric_carrier() {
    run_with_large_stack(
        "set_builder_parameter_inherits_known_numeric_carrier",
        || {
            let source_code = r#"
claim:
    ? forall E power_set(R), x0 R:
        0 = 0
    have fn filtered_points(n N+) power_set(E) = {y E: abs(y - x0) < 1 / n}
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "set_builder_parameter_inherits_known_numeric_carrier",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a set-builder parameter should inherit the known carrier of its domain:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn set_builder_parameter_does_not_invent_numeric_carrier() {
    run_with_large_stack(
        "set_builder_parameter_does_not_invent_numeric_carrier",
        || {
            let source_code = r#"
claim:
    ? forall E set, x0 R:
        0 = 0
    have fn filtered_points(n N+) power_set(E) = {y E: abs(y - x0) < 1 / n}
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "set_builder_parameter_does_not_invent_numeric_carrier",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                !run_succeeded,
                "a set-builder parameter must not acquire a numeric carrier without a subset fact:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn parameter_over_set_builder_inherits_builder_domain_carrier() {
    run_with_large_stack(
        "parameter_over_set_builder_inherits_builder_domain_carrier",
        || {
            let source_code = r#"
claim:
    ? forall E power_set(R), g fn(x E) R, x0 R:
        0 = 0
    claim:
        ? forall y {x E: g(x) != 0}:
            abs(y - x0) >= 0
        abs(y - x0) >= 0
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "parameter_over_set_builder_inherits_builder_domain_carrier",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a parameter over a set builder should inherit the builder domain carrier:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn punctured_domain_parameter_inherits_ambient_real_carrier() {
    run_with_large_stack(
        "punctured_domain_parameter_inherits_ambient_real_carrier",
        || {
            let source_code = r#"
claim:
    ? forall X power_set(R), g fn(z X) R, x0 X:
        0 = 0
    have fn local_difference_quotient(x set_minus(X, {x0})) R = (g(x) - g(x0)) / (x - x0)
    0 = 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "punctured_domain_parameter_inherits_ambient_real_carrier",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a punctured-domain parameter should inherit its ambient real carrier:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_named_function_space_accepts_anonymous_function_return() {
    run_with_large_stack(
        "template_named_function_space_accepts_anonymous_function_return",
        || {
            let source_code = r#"
template<S set>:
    have FunctionCarrier set = fn(x S) S

template<S set>:
    have fn keep(f \FunctionCarrier<S>) \FunctionCarrier<S> = fn(x S) S {f(x)}

forall S set, f \FunctionCarrier<S>:
    \keep<S>(f) $in \FunctionCarrier<S>
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_named_function_space_accepts_anonymous_function_return",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template named function spaces should accept matching anonymous returns:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_function_body_must_belong_to_declared_return_set() {
    let invalid_source = r#"
fn(x R) N {x}(1 / 2) $in N
"#;

    let mut invalid_runtime = Runtime::new();
    invalid_runtime.new_file_path_new_env_new_name_scope(
        "anonymous_function_body_must_belong_to_declared_return_set",
    );
    let (stmt_results, runtime_error) = run_source_code(invalid_source, &mut invalid_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&invalid_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "an anonymous function must not trust an incompatible declared return set:\n{}",
        run_output
    );
    assert!(
        run_output.contains(
            "anonymous function body x is not verified to belong to declared return set N"
        ),
        "the rejection should identify the body and declared return set:\n{}",
        run_output
    );

    let valid_source = r#"
fn(x R) R {x}(1 / 2) = 1 / 2
"#;
    let mut valid_runtime = Runtime::new();
    valid_runtime.new_file_path_new_env_new_name_scope(
        "anonymous_function_body_in_declared_return_set_is_well_defined",
    );
    let (stmt_results, runtime_error) = run_source_code(valid_source, &mut valid_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&valid_runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a compatible anonymous function should remain well-defined:\n{}",
        run_output
    );

    let symbolic_cart_source = r#"
have n N+ = 3
have cart c for i1 <= n, proj(c, i1) = R
have fn coordinate_fn(p c) fn(i1 closed_range(1, n)) R = fn(j closed_range(1, n)) R {p[j]}
"#;
    let mut symbolic_cart_runtime = Runtime::new();
    symbolic_cart_runtime.new_file_path_new_env_new_name_scope(
        "anonymous_function_cart_coordinate_in_declared_return_set",
    );
    let (stmt_results, runtime_error) =
        run_source_code(symbolic_cart_source, &mut symbolic_cart_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&symbolic_cart_runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a symbolic Cartesian coordinate should retain its proved carrier:\n{}",
        run_output
    );
}

#[test]
fn iterated_operators_require_scalar_return_sets() {
    let invalid_cases = [
        (
            "range_sum",
            "sum(1, 2, fn(k Z) power_set(R) {R}) = sum(1, 2, fn(k Z) power_set(R) {R})",
            "sum: iterand return set power_set(R) is not verified to be a subset of C",
        ),
        (
            "range_product",
            "product(1, 2, fn(k Z) power_set(R) {R}) = product(1, 2, fn(k Z) power_set(R) {R})",
            "product: iterand return set power_set(R) is not verified to be a subset of C",
        ),
        (
            "finite_set_sum",
            "finite_set_sum({1, 2}, fn(k {1, 2}) power_set(R) {R}) = finite_set_sum({1, 2}, fn(k {1, 2}) power_set(R) {R})",
            "finite_set_sum: iterand return set power_set(R) is not verified to be a subset of C",
        ),
        (
            "finite_set_product",
            "finite_set_product({1, 2}, fn(k {1, 2}) power_set(R) {R}) = finite_set_product({1, 2}, fn(k {1, 2}) power_set(R) {R})",
            "finite_set_product: iterand return set power_set(R) is not verified to be a subset of C",
        ),
    ];

    for (label, source_code, expected_error) in invalid_cases {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(label);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            !run_succeeded,
            "{label} must reject a set-valued iterand:\n{run_output}"
        );
        assert!(
            run_output.contains(expected_error),
            "{label} should identify the non-scalar declared return set:\n{run_output}"
        );
    }

    let valid_source = r#"
sum(1, 2, fn(k Z) Z {k}) = sum(1, 2, fn(k Z) Z {k})
product(1, 2, fn(k Z) Z {k}) = product(1, 2, fn(k Z) Z {k})
finite_set_sum({1, 2}, fn(k {1, 2}) Z {k}) = finite_set_sum({1, 2}, fn(k {1, 2}) Z {k})
finite_set_product({1, 2}, fn(k {1, 2}) Z {k}) = finite_set_product({1, 2}, fn(k {1, 2}) Z {k})
finite_set_sum(3...1, fn(k Z) Z {0}) = 0
finite_set_product(3...1, fn(k Z) Z {1}) = 1
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("iterated_scalar_return_sets_remain_valid");
    let (stmt_results, runtime_error) = run_source_code(valid_source, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "scalar-valued iterands should remain well-defined:\n{run_output}"
    );
}

#[test]
fn anonymous_fn_restriction_over_abstract_subset_is_well_defined() {
    run_with_large_stack(
        "anonymous_fn_restriction_over_abstract_subset_is_well_defined_large_stack",
        || {
            let source_code = r#"
forall E2 set, E power_set(E2), f fn(x E2) R:
    fn_range(fn(x E) R {f(x)}) $subset R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_restriction_over_abstract_subset_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous function restriction over abstract subset failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn restricted_lambda_can_apply_function_on_larger_numeric_interval() {
    run_with_large_stack(
        "restricted_lambda_can_apply_function_on_larger_numeric_interval",
        || {
            let source_code = r#"
have fn piece(x '[1, 3]) R by cases:
    case x < 2: x^2
    case x = 2: 7
    case x > 2: x^3

claim:
    ? forall x '[1, 2):
        fn(y '[1, 2)) R {piece(y)}(x) = fn(y '[1, 2)) R {y^2}(x)
    x < 2
    piece(x) = x^2
    fn(y '[1, 2)) R {piece(y)}(x) = piece(x)
    fn(y '[1, 2)) R {y^2}(x) = x^2
    fn(y '[1, 2)) R {piece(y)}(x) = fn(y '[1, 2)) R {y^2}(x)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "restricted_lambda_can_apply_function_on_larger_numeric_interval",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "restricted lambda should inherit numeric interval bounds:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn casewise_function_definition_requires_a_total_disjoint_partition() {
    run_with_large_stack(
        "casewise_function_definition_requires_a_total_disjoint_partition",
        || {
            let invalid_cases = [
                (
                    "casewise_function_missing_coverage",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
"#,
                    "have fn by cases: cases do not cover the declared domain",
                ),
                (
                    "casewise_function_empty_case_list",
                    r#"
have fn f(x R) R by cases:
"#,
                    "block header missing body",
                ),
                (
                    "casewise_function_bodyless_case",
                    r#"
have fn f(x R) R by cases:
    case x = 0
"#,
                    "Unexpected end of tokens",
                ),
                (
                    "casewise_function_overlapping_cases_with_same_value",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x <= 0: 1
"#,
                    "have fn by cases: cases overlap or cannot be proved mutually exclusive",
                ),
                (
                    "casewise_function_overlapping_cases_with_conflicting_values",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x <= 0: 2
"#,
                    "have fn by cases: cases overlap or cannot be proved mutually exclusive",
                ),
            ];

            for (label, source_code, expected_error) in invalid_cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} should reject an invalid case partition:\n{}",
                    label, run_output
                );
                assert!(
                    run_output.contains(expected_error),
                    "{} should report the partition failure:\n{}",
                    label,
                    run_output
                );

                let recovery_source = r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x < 0: 2

f(0) = 1
"#;
                let (stmt_results, runtime_error) = run_source_code(recovery_source, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} should not bind the rejected function name:\n{}",
                    label, run_output
                );
            }

            let domain_relative_source = r#"
have fn only_nonnegative(x R: x >= 0) R by cases:
    case x >= 0: x

only_nonnegative(0) = 0
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("casewise_function_domain_coverage");
            let (stmt_results, runtime_error) =
                run_source_code(domain_relative_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "cases only need to cover the declared function domain:\n{}",
                run_output
            );

            let negated_membership_source = r#"
have fn rational_indicator(x R) R by cases:
    case x $in Q: 1
    case not x $in Q: 0

rational_indicator(0) = 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "casewise_function_negated_membership_condition",
            );
            let (stmt_results, runtime_error) =
                run_source_code(negated_membership_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "casewise functions should accept a leading negated atomic condition:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_body_can_use_singleton_parameter_equality() {
    run_with_large_stack(
        "anonymous_fn_body_can_use_singleton_parameter_equality_large_stack",
        || {
            let source_code = r#"
have fn ambient(x '[1, 3]) R = x

fn(x {2}) R {ambient(x)} = fn(x {2}) R {ambient(x)}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_body_can_use_singleton_parameter_equality",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a singleton-domain anonymous function should expose its parameter equality:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn conditional_contribution_family_reindexes_to_equal_finite_sum() {
    run_with_large_stack(
        "conditional_contribution_family_reindexes_to_equal_finite_sum_large_stack",
        || {
            let source_code = r#"
prop synthetic_stieltjes_contribution(J power_set(R), t R):
    exist height R st {t = height}

prop synthetic_ordinary_contribution(J power_set(R), t R):
    exist height R st {t = height}

prop synthetic_contribution_family(P finite_set, c fn(J P) R):
    forall J P:
        J $in power_set(R)
        =>:
            $synthetic_stieltjes_contribution(J, c(J))

thm synthetic_stieltjes_contribution_to_ordinary:
    ? forall J power_set(R), t R:
        $synthetic_stieltjes_contribution(J, t)
        =>:
            $synthetic_ordinary_contribution(J, t)
    obtain height from exist height R st {t = height}
    witness exist height0 R st {t = height0} from height:
        t = height
    $synthetic_ordinary_contribution(J, t)

have P finite_set = {{}}
have fn c(J P) R = 0

claim:
    ? $synthetic_contribution_family(P, c)
    claim:
        ? forall J P:
            J $in power_set(R)
            =>:
                $synthetic_stieltjes_contribution(J, c(J))
        witness exist height R st {c(J) = height} from 0:
            c(J) = 0
        $synthetic_stieltjes_contribution(J, c(J))
    $synthetic_contribution_family(P, c)

claim:
    ? forall J P:
        J $in power_set(R)
        =>:
            $synthetic_ordinary_contribution(J, c(J))
    $synthetic_stieltjes_contribution(J, c(J))
    by thm synthetic_stieltjes_contribution_to_ordinary(J, c(J))
    $synthetic_ordinary_contribution(J, c(J))

claim:
    ? $fn_eq(fn(J P) R {0}, c)
    forall K P:
        fn(J P) R {0}(K) = 0
        c(K) = 0
        fn(J P) R {0}(K) = c(K)
    $fn_eq(fn(J P) R {0}, c)

fn(J P) R {0} = c
finite_set_sum(P, fn(J P) R {0}) = finite_set_sum(P, c)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "conditional_contribution_family_reindexes_to_equal_finite_sum",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "conditional contribution family should reindex through an explicit function equality:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_applications_beta_reduce_before_structural_equality_comparison() {
    run_with_large_stack(
        "anonymous_fn_applications_beta_reduce_before_structural_equality_comparison",
        || {
            let positive_source_code = r#"
forall f, g fn(x R) R, a R:
    forall x R:
        f(x) = f(-x)
        g(x) = g(-x)
    =>:
        f(a) = f(-a)
        g(a) = g(-a)
        fn(x R) R {f(x) * g(x)}(a) = fn(x R) R {f(x) * g(x)}(-a)
"#;

            let mut positive_runtime = Runtime::new();
            positive_runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_applications_beta_reduce_before_structural_equality_comparison_positive",
            );
            let (positive_stmt_results, positive_runtime_error) =
                run_source_code(positive_source_code, &mut positive_runtime);
            let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_stmt_results,
                &positive_runtime_error,
                false,
            );
            assert!(
                positive_run_succeeded,
                "anonymous applications should beta-reduce before their bodies are compared structurally:\n{}",
                positive_run_output
            );

            let negative_source_code = r#"
forall f, g fn(x R) R, a, b R:
    f(a) = f(b)
    =>:
        fn(x R) R {f(x) * g(x)}(a) = fn(x R) R {f(x) * g(x)}(b)
"#;

            let mut negative_runtime = Runtime::new();
            negative_runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_applications_beta_reduce_before_structural_equality_comparison_negative",
            );
            let (negative_stmt_results, negative_runtime_error) =
                run_source_code(negative_source_code, &mut negative_runtime);
            let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_stmt_results,
                &negative_runtime_error,
                false,
            );
            assert!(
                !negative_run_succeeded,
                "beta reduction plus structural equality must not invent the missing equality g(a) = g(b):\n{}",
                negative_run_output
            );
        },
    );
}

#[test]
fn curried_have_fn_equal_unfolds_pointwise() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N+) R = fn(n N+) R {a(n) + b(n)}

forall a, b seq(R), k N+:
    seq_add(a, b)(k) = a(k) + b(k)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("curried_have_fn_equal_unfolds_pointwise");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "curried have fn equality should unfold pointwise:\n{}",
        run_output
    );
}

#[test]
fn fn_application_returning_fn_set_verifies_sequence_membership() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N+) R = fn(n N+) R {a(n) + b(n)}

forall a, b seq(R):
    seq_add(a, b) $in seq(R)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "fn_application_returning_fn_set_verifies_sequence_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "function application returning a fn set should verify seq membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_unfolds_for_membership() {
    let source_code = r#"
have fn circle(r R+) power_set(cart(R, R)) = {x cart(R, R): x[1]^2 + x[2]^2 = r^2}
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(3, 4) $in circle(5)
(2, 2) $in line(1, -1, 0)

forall a, b R:
    a != 0 or b != 0
    =>:
        (0, 0) $in line(a, b, 0)

forall p cart(R, R):
    p $in circle(5)
    =>:
        p[1]^2 + p[2]^2 = 5^2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_unfolds_for_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "set-valued have fn applications should unfold for membership:\n{}",
        run_output
    );
}

#[test]
fn function_valued_set_family_preserves_member_cart_carrier() {
    let source_code = r#"
have fn row(x N+) power_set(cart(N+, N+)) = {point cart(N+, N+): point[1] = x}
have fn rows(n N+) fn(K N+) power_set(cart(N+, N+)) = fn(x N+) power_set(cart(N+, N+)) {row(x)}

forall n, K N+, point rows(n)(K):
    point[1] $in N+
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "function_valued_set_family_preserves_member_cart_carrier",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "function-valued set family should expose its member cart carrier:\n{}",
        run_output
    );
}

#[test]
fn function_valued_scalar_set_family_does_not_invent_tuple_carrier() {
    let source_code = r#"
have fn scalar_row(x N+) power_set(N+) = {x}
have fn scalar_rows(n N+) fn(K N+) power_set(N+) = fn(x N+) power_set(N+) {scalar_row(x)}

forall n, K N+, point scalar_rows(n)(K):
    point[1] $in N+
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "function_valued_scalar_set_family_does_not_invent_tuple_carrier",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded && run_output.contains("index target point is not a tuple"),
        "scalar-set members must remain non-tuples:\n{}",
        run_output
    );
}

#[test]
fn exactly_indexed_named_set_builder_unfolds_for_membership() {
    let source_code = r#"
have nonnegative_reals power_set(R) = {x R: x >= 0}
1 $in nonnegative_reals
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "exactly_indexed_named_set_builder_unfolds_for_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a named set with an exact set-builder index should unfold one membership layer:\n{}",
        run_output
    );
}

#[test]
fn exactly_indexed_named_set_builder_keeps_predicate_obligation() {
    let source_code = r#"
have positive_reals power_set(R) = {x R: x > 0}
0 $in positive_reals
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "exactly_indexed_named_set_builder_keeps_predicate_obligation",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "named set-builder membership must not bypass its defining predicate:\n{}",
        run_output
    );
}

#[test]
fn template_set_valued_have_fn_application_unfolds_for_membership() {
    let source_code = r#"
template<s set>:
    have fn selected(S power_set(s)) power_set(s) = {x s: x $in S}

1 $in \selected<R>({1})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "template_set_valued_have_fn_application_unfolds_for_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a materialized template function returning a set builder should unfold for membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_keeps_side_conditions() {
    let source_code = r#"
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(0, 0) $in line(0, 0, 0)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_keeps_side_conditions",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "set-valued have fn unfolding should not bypass argument side conditions:\n{}",
        run_output
    );
}

#[test]
fn unary_numeric_objects_respect_argument_equality() {
    let source_code = r#"
forall x, y R:
    x = y
    =>:
        abs(x) = abs(y)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("unary_numeric_objects_respect_argument_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "unary numeric objects should respect argument equality:\n{}",
        run_output
    );
}

#[test]
fn iterated_operator_equality_uses_fn_eq_for_function_arg() {
    run_with_large_stack(
        "iterated_operator_equality_uses_fn_eq_for_function_arg_large_stack",
        || {
            let positive_source_code = r#"
sum(1, 3, fn(x Z) Z {x}) = sum(1, 3, fn(y Z) Z {y})
product(1, 3, fn(x Z) Z {x}) = product(1, 3, fn(y Z) Z {y})

forall f, g fn(x Z) Z:
    sum(1, 3, fn(x Z) Z {f(x) + g(x)}) = sum(1, 3, fn(y Z) Z {g(y) + f(y)})
"#;

            let mut positive_runtime = Runtime::new();
            positive_runtime
                .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_positive");
            let (positive_stmt_results, positive_runtime_error) =
                run_source_code(positive_source_code, &mut positive_runtime);
            let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_stmt_results,
                &positive_runtime_error,
                false,
            );
            assert!(
                positive_run_succeeded,
                "sum/product equality should compare function args by fn_eq:\n{}",
                positive_run_output
            );

            let negative_source_code = r#"
product(1, 3, fn(x Z) Z {x}) = product(1, 4, fn(y Z) Z {y})
"#;

            let mut negative_runtime = Runtime::new();
            negative_runtime
                .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_negative");
            let (negative_stmt_results, negative_runtime_error) =
                run_source_code(negative_source_code, &mut negative_runtime);
            let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_stmt_results,
                &negative_runtime_error,
                false,
            );
            assert!(
                !negative_run_succeeded,
                "product equality should still require equal ranges:\n{}",
                negative_run_output
            );
        },
    );
}

#[test]
fn finite_sum_order_uses_pointwise_bounds() {
    run_with_large_stack("finite_sum_order_uses_pointwise_bounds_large_stack", || {
        let source_code = r#"
thm finite_series_comparison_test:
    ? forall a, b fn(i1 Z) R, m, n Z:
        m <= n
        forall i1 Z:
            m <= i1 <= n
            =>:
                a(i1) <= b(i1)
        =>:
            sum(m, n, fn(i1 Z) R {a(i1)}) <= sum(m, n, fn(i1 Z) R {b(i1)})

    sum(m, n, fn(i1 Z) R {a(i1)}) <= sum(m, n, fn(i1 Z) R {b(i1)})

thm finite_series_comparison_n_pos_index_test:
    ? forall a, b fn(i1 N+) R, m, n N+:
        m <= n
        forall i1 N+:
            m <= i1 <= n
            =>:
                a(i1) <= b(i1)
        =>:
            sum(m, n, fn(i1 N+) R {a(i1)}) <= sum(m, n, fn(i1 N+) R {b(i1)})

    sum(m, n, fn(i1 N+) R {a(i1)}) <= sum(m, n, fn(i1 N+) R {b(i1)})

thm finite_series_triangle_test:
    ? forall a fn(i1 Z) R, m, n Z:
        m <= n
        =>:
            abs(sum(m, n, fn(i1 Z) R {a(i1)})) <= sum(m, n, fn(i1 Z) R {abs(a(i1))})

    abs(sum(m, n, fn(i1 Z) R {a(i1)})) <= sum(m, n, fn(i1 Z) R {abs(a(i1))})

thm finite_series_scalar_mul_test:
    ? forall a fn(i1 Z) R, c R, m, n Z:
        m <= n
        =>:
            sum(m, n, fn(i1 Z) R {c * a(i1)}) = c * sum(m, n, fn(i1 Z) R {a(i1)})

    sum(m, n, fn(i1 Z) R {c * a(i1)}) = c * sum(m, n, fn(i1 Z) R {a(i1)})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_sum_order_uses_pointwise_bounds");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite sum order should use pointwise bounds:\n{}",
            run_output
        );
    });
}

#[test]
fn iterated_operator_range_order_is_required_for_symbolic_bounds() {
    run_with_large_stack(
        "iterated_operator_range_order_is_required_for_symbolic_bounds_large_stack",
        || {
            let cases = [
                (
                    "sum_symbolic_empty_range",
                    r#"
thm bad_symbolic_empty_sum:
    ? forall a fn(i1 Z) R, m Z:
        sum(m, m - 1, fn(i1 Z) R {a(i1)}) = 0

    trust:
        sum(m, m - 1, fn(i1 Z) R {a(i1)}) = 0
"#,
                    "sum: cannot verify start <= end for the summation range",
                ),
                (
                    "product_symbolic_empty_range",
                    r#"
thm bad_symbolic_empty_product:
    ? forall a fn(i1 Z) R, m Z:
        product(m, m - 1, fn(i1 Z) R {a(i1)}) = 1

    trust:
        product(m, m - 1, fn(i1 Z) R {a(i1)}) = 1
"#,
                    "product: cannot verify start <= end for the product range",
                ),
            ];

            for (name, source_code, expected_message) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(name);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(
                    !run_succeeded,
                    "{} should reject reversed symbolic bounds:\n{}",
                    name, run_output
                );
                assert!(
                    run_output.contains(expected_message),
                    "{} should report the range-order well-definedness failure:\n{}",
                    name,
                    run_output
                );
            }
        },
    );
}

#[test]
fn nested_iterated_operator_with_positive_index_is_well_defined() {
    run_with_large_stack(
        "nested_iterated_operator_with_positive_index_is_well_defined_large_stack",
        || {
            let source_code = r#"
eval sum(1, 3, fn(x N+) N+ {sum(1, x, fn(y N+) N+ {x + y})})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "nested_iterated_operator_with_positive_index_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "nested range sum should be well-defined for positive integer indices:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn builtin_function_properties_verify_and_unfold() {
    run_with_large_stack("builtin_function_properties_verify_and_unfold", || {
        let source_code = r#"
have fn identity_on_three(x {1, 2, 3}) {1, 2, 3} = x

forall x1, x2 {1, 2, 3}:
    identity_on_three(x1) = identity_on_three(x2)
    =>:
        x1 = identity_on_three(x1) = identity_on_three(x2) = x2
by def $injective({1, 2, 3}, {1, 2, 3}, identity_on_three)
$injective({1, 2, 3}, {1, 2, 3}, identity_on_three)

claim:
    ? forall y {1, 2, 3}:
        exist x {1, 2, 3} st {y = identity_on_three(x)}
    y = identity_on_three(y)
    witness exist x {1, 2, 3} st {y = identity_on_three(x)} from y
by def $surjective({1, 2, 3}, {1, 2, 3}, identity_on_three)
$surjective({1, 2, 3}, {1, 2, 3}, identity_on_three)
by def $bijective({1, 2, 3}, {1, 2, 3}, identity_on_three)
$bijective({1, 2, 3}, {1, 2, 3}, identity_on_three)

thm builtin_injective_unfolds:
    ? forall A, B set, f fn(x A) B, x1, x2 A:
        $injective(A, B, f)
        f(x1) = f(x2)
        =>:
            x1 = x2
    x1 = x2

thm builtin_surjective_unfolds:
    ? forall A, B set, f fn(x A) B, y B:
        $surjective(A, B, f)
        =>:
            exist x A st {y = f(x)}
    exist x A st {y = f(x)}

thm builtin_bijective_unfolds:
    ? forall A, B set, f fn(x A) B:
        $bijective(A, B, f)
        =>:
            $injective(A, B, f)
            $surjective(A, B, f)
    $injective(A, B, f)
    $surjective(A, B, f)
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("builtin_function_properties_verify_and_unfold");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "builtin function properties should verify and expose their definitions:\n{}",
            run_output
        );
        assert!(
            run_output.contains("builtin function-property definition"),
            "function-property verification should expose builtin provenance:\n{}",
            run_output
        );
    });
}

#[test]
fn builtin_function_property_negation_uses_by_contra() {
    run_with_large_stack("builtin_function_property_negation_uses_by_contra", || {
        let source_code = r#"
have fn constant(x {1, 2}) {0} = 0

by contra:
    ? not $injective({1, 2}, {0}, constant)
    constant(1) = 0
    constant(2) = 0
    constant(1) = 0 = constant(2)
    1 = 2
    impossible 1 = 2
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "builtin_function_property_negation_uses_by_contra",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "a constant map on a two-element source should be proved non-injective by contra:\n{}",
            run_output
        );
    });
}

#[test]
fn known_forall_matches_alpha_equivalent_set_builder_binders() {
    run_with_large_stack(
        "known_forall_matches_alpha_equivalent_set_builder_binders",
        || {
            let source_code = r#"
abstract_prop p(a, b)
abstract_prop q(a, b)

forall:
    forall a, b R:
        $p(a, {x R: $p(x, b)})
        $q(1, {x R: $q(a + b, x)})
    =>:
        $p(1, {y R: $p(y, 2)})
        $q(1, {z R: $q(1 + 2, z)})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "known_forall_matches_alpha_equivalent_set_builder_binders",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "set-builder binder spelling and identity should be alpha-equivalent:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_source_function_property_rules() {
    run_with_large_stack("finite_source_function_property_rules", || {
        let source_code = r#"
thm finite_injection_preserves_size_onto_range:
    ? forall A finite_set, B set, f fn(x A) B:
        $injective(A, B, f)
        =>:
            finite_set_size(fn_range(f)) = finite_set_size(A)
    finite_set_size(fn_range(f)) = finite_set_size(A)

thm finite_surjection_has_finite_bounded_codomain:
    ? forall A finite_set, B set, f fn(x A) B:
        $surjective(A, B, f)
        =>:
            $is_finite_set(B)
            finite_set_size(B) <= finite_set_size(A)
    $is_finite_set(B)
    finite_set_size(B) <= finite_set_size(A)

thm finite_bijection_preserves_size:
    ? forall A finite_set, B set, f fn(x A) B:
        $bijective(A, B, f)
        =>:
            $is_finite_set(B)
            finite_set_size(A) = finite_set_size(B)
    $is_finite_set(B)
    finite_set_size(A) = finite_set_size(B)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_source_function_property_rules");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite-source function-property rules should verify:\n{}",
            run_output
        );
        for expected_rule in [
            "finite injection has range cardinality equal to its source",
            "finite codomain of a surjection from a finite set",
            "finite surjection bounds codomain cardinality by source cardinality",
            "finite bijection preserves cardinality",
        ] {
            assert!(
                run_output.contains(expected_rule),
                "finite-source verification should expose rule `{}`:\n{}",
                expected_rule,
                run_output
            );
        }
    });
}

#[test]
fn builtin_function_properties_reject_malformed_arguments() {
    let source_code = r#"
$injective({1}, {1}, 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "builtin_function_properties_require_matching_function_signature",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject a non-function third argument:\n{}",
        run_output
    );
    assert!(
        run_output.contains("requires sets A and B and a function with type fn(x A) B"),
        "wrong function-property signature should report the required function type:\n{}",
        run_output
    );

    let mismatch_source_code = r#"
have fn mismatched_codomain(x {1}) {2} = 2
$injective({1}, {1}, mismatched_codomain)
"#;
    let mut mismatch_runtime = Runtime::new();
    mismatch_runtime.new_file_path_new_env_new_name_scope(
        "builtin_function_properties_reject_mismatched_codomain",
    );
    let (stmt_results, runtime_error) =
        run_source_code(mismatch_source_code, &mut mismatch_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&mismatch_runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject a function with the wrong codomain:\n{}",
        run_output
    );
    assert!(
        run_output.contains("requires sets A and B and a function with type fn(x A) B"),
        "mismatched codomain should report the required function type:\n{}",
        run_output
    );

    let mut arity_runtime = Runtime::new();
    arity_runtime
        .new_file_path_new_env_new_name_scope("builtin_function_properties_reject_wrong_arity");
    let (stmt_results, runtime_error) = run_source_code("$injective({1}, {1})", &mut arity_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&arity_runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject two arguments:\n{}",
        run_output
    );
    assert!(
        run_output.contains("fact `injective` expects 3 argument(s), but got 2"),
        "wrong function-property arity should report the expected argument count:\n{}",
        run_output
    );
}

#[test]
fn finite_surjection_rules_do_not_bootstrap_finiteness_cycle() {
    let source_code = r#"
have A, B set
have f fn(x A) B
have g fn(y B) A
trust $surjective(A, B, f)
trust $surjective(B, A, g)
$is_finite_set(A)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_surjection_rules_do_not_bootstrap_finiteness_cycle",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "cyclic surjections without a finite source must not infer finiteness:\n{}",
        run_output
    );
}

#[test]
fn finite_set_sum_core_rules() {
    run_with_large_stack("finite_set_sum_core_rules", || {
        let source_code = r#"
thm finite_set_sum_in_union_from_left:
    ? forall z set, A set, B set:
        z $in A
        =>:
            z $in union(A, B)
    z $in union(A, B)

thm finite_set_sum_in_union_from_right:
    ? forall z set, A set, B set:
        z $in B
        =>:
            z $in union(A, B)
    z $in union(A, B)

finite_set_sum({1, 2, 3}, fn(x Z) Z {x}) = 1 + 2 + 3
finite_set_sum({}, fn(x Z) Z {x}) = 0
finite_set_sum(1...3, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x})
have P finite_set = {1, 2}
finite_set_sum(P, fn(x P) R {x}) = 3
finite_set_sum({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_sum({1, 2}, fn(x N+) N+ {x}) $in N+

sketch:
    have X finite_set
    have c Z
    finite_set_sum(X, fn(x X) Z {c}) = finite_set_size(X) * c

sketch:
    have X power_set(Z)
    trust $is_finite_set(X)
    finite_set_sum(X, fn(x X) Z {x + 0}) = finite_set_sum(X, fn(x X) Z {x})

thm finite_set_sum_substitution_tmp:
    ? forall X, Y finite_set, f fn(x X) R, g fn(y Y) X:
        $bijective(Y, X, g)
        =>:
            finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})
    finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})

thm finite_set_sum_range_matches_series_tmp:
    ? forall a fn(i1 Z) R, m, n Z:
        m <= n
        =>:
            sum(m, n, fn(i1 Z) R {a(i1)}) = finite_set_sum(m...n, fn(i1 m...n) R {a(i1)})
    sum(m, n, fn(i1 Z) R {a(i1)}) = finite_set_sum(m...n, fn(i1 m...n) R {a(i1)})

thm finite_set_sum_disjoint_union_tmp:
    ? forall X, Y finite_set, f fn(z union(X, Y)) R:
        intersect(X, Y) = {}
        =>:
            finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
    finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})

thm finite_set_sum_add_tmp:
    ? forall X finite_set, f, g fn(x X) R:
        finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)
    finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)

thm finite_set_sum_scalar_mul_tmp:
    ? forall X finite_set, f fn(x X) R, c R:
        finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)
    finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)

thm finite_set_sum_monotone_tmp:
    ? forall X finite_set, f, g fn(x X) R:
        forall x X:
            f(x) <= g(x)
        =>:
            finite_set_sum(X, f) <= finite_set_sum(X, g)
    finite_set_sum(X, f) <= finite_set_sum(X, g)

thm finite_set_sum_member_le_nonnegative_sum_tmp:
    ? forall X finite_set, f fn(x X) R, x X:
        forall y X:
            f(y) >= 0
        =>:
            f(x) <= finite_set_sum(X, f)
    f(x) <= finite_set_sum(X, f)

thm finite_set_sum_triangle_tmp:
    ? forall X finite_set, f fn(x X) R:
        abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})
    abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_sum_core_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite_set_sum core rules should verify:\n{}",
            run_output
        );
    });
}

#[test]
fn restricting_a_function_from_a_union_domain_is_well_defined() {
    run_with_large_stack(
        "restricting_a_function_from_a_union_domain_is_well_defined",
        || {
            let source_code = r#"
thm finite_set_sum_disjoint_union_restriction:
    ? forall X, Y finite_set, f fn(z union(X, Y)) R:
        intersect(X, Y) = {}
        =>:
            finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
    finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "restricting_a_function_from_a_union_domain_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a function on union(X, Y) should restrict to X and Y:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_sum_cartesian_product_and_fubini() {
    run_with_large_stack("finite_set_sum_cartesian_product_and_fubini", || {
        let source_code = r#"
thm finite_double_sum_over_cartesian_product_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)

thm finite_double_sum_over_cartesian_product_reversed_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)
    finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)

thm finite_fubini_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_sum_cartesian_product_and_fubini");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite-set Cartesian-product/Fubini rules should verify:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_set_sum_bijective_enumerations_are_well_defined() {
    run_with_large_stack(
        "finite_set_sum_bijective_enumerations_are_well_defined",
        || {
            let source_code = r#"
template<X finite_set, f fn(x X) R, g fn(i1 closed_range(1, finite_set_size(X))) X: finite_set_size(X) >= 1, $bijective(closed_range(1, finite_set_size(X)), X, g)>:
    have self_finite_set_sum R = sum(1, finite_set_size(X), fn(i1 closed_range(1, finite_set_size(X))) R {f(g(i1))})

thm finite_set_sum_raw_enumeration_well_defined:
    ? forall X finite_set, f fn(x X) R, g fn(i1 closed_range(1, finite_set_size(X))) X, h fn(i1 closed_range(1, finite_set_size(X))) X:
        finite_set_size(X) >= 1
        $bijective(closed_range(1, finite_set_size(X)), X, g)
        $bijective(closed_range(1, finite_set_size(X)), X, h)
        =>:
            sum(1, finite_set_size(X), fn(i1 closed_range(1, finite_set_size(X))) R {f(g(i1))}) = sum(1, finite_set_size(X), fn(i1 closed_range(1, finite_set_size(X))) R {f(h(i1))})
    sum(1, finite_set_size(X), fn(i1 closed_range(1, finite_set_size(X))) R {f(g(i1))}) = sum(1, finite_set_size(X), fn(i1 closed_range(1, finite_set_size(X))) R {f(h(i1))})

thm finite_set_sum_template_enumeration_well_defined:
    ? forall X finite_set, f fn(x X) R, g fn(i1 closed_range(1, finite_set_size(X))) X, h fn(i1 closed_range(1, finite_set_size(X))) X:
        finite_set_size(X) >= 1
        $bijective(closed_range(1, finite_set_size(X)), X, g)
        $bijective(closed_range(1, finite_set_size(X)), X, h)
        =>:
            \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>
    \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "finite_set_sum_bijective_enumerations_are_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "finite_set_sum bijective enumeration rules should verify:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_product_core_rules() {
    let source_code = r#"
finite_set_product({2, 3, 4}, fn(x Z) Z {x}) = 2 * 3 * 4
finite_set_product({}, fn(x Z) Z {x}) = 1
finite_set_product(1...3, fn(x Z) Z {x}) = product(1, 3, fn(x Z) Z {x})
finite_set_product({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_product({1, 2}, fn(x N+) N+ {x}) $in N+
finite_set_product({}, fn(x N+) N+ {x}) $in N+

sketch:
    have X finite_set
    have c R
    finite_set_product(X, fn(x X) R {c}) = c ^ finite_set_size(X)

sketch:
    have X power_set(Z)
    trust $is_finite_set(X)
    finite_set_product(X, fn(x X) Z {x + 0}) = finite_set_product(X, fn(x X) Z {x})

forall X finite_set, f, g fn(x X) Z:
    finite_set_product(X, fn(x X) Z {f(x) * g(x)}) = finite_set_product(X, f) * finite_set_product(X, g)

forall X finite_set, f, g fn(x X) Z:
    $fn_eq_in(f, g, X)
    =>:
        finite_set_product(X, f) = finite_set_product(X, g)

forall X, Y finite_set, f fn(x X) Z, g fn(y Y) X:
    $bijective(Y, X, g)
    =>:
        finite_set_product(X, f) = finite_set_product(Y, fn(y Y) Z {f(g(y))})

thm finite_set_product_fresh_insertion:
    ? forall x Z, S finite_set:
        S $subset Z
        not x $in S
        =>:
            finite_set_product(union({x}, S), fn(y union({x}, S)) Z {y}) = finite_set_product(S, fn(y S) Z {y}) * x
    finite_set_product(union({x}, S), fn(y union({x}, S)) Z {y}) = finite_set_product(S, fn(y S) Z {y}) * x

thm finite_set_product_remove_member:
    ? forall A finite_set, x A:
        A $subset Z
        =>:
            finite_set_product(A, fn(y A) Z {y}) = finite_set_product(set_minus(A, {x}), fn(y set_minus(A, {x})) Z {y}) * x
    finite_set_product(A, fn(y A) Z {y}) = finite_set_product(set_minus(A, {x}), fn(y set_minus(A, {x})) Z {y}) * x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("finite_set_product_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite_set_product core rules should verify:\n{}",
        run_output
    );
    assert!(
        run_output
            .contains("equality: finite-set product distributes over pointwise multiplication")
            && run_output.contains("equality: finite-set product substitution along a bijection"),
        "finite-set product algebra and reindexing should expose builtin provenance:\n{run_output}"
    );
}

#[test]
fn dependent_fn_param_set_uses_previous_arg() {
    run_with_large_stack(
        "dependent_fn_param_set_uses_previous_arg_large_stack",
        || {
            let source_code = r#"
have f fn(n N+, x closed_range(1, n)) R
f(3, 2) = f(3, 2)
"#;

            let mut runtime = Runtime::new();
            runtime
                .new_file_path_new_env_new_name_scope("dependent_fn_param_set_uses_previous_arg");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "dependent_fn_param_set_uses_previous_arg failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn dependent_fn_return_set_instantiates_with_arguments() {
    run_with_large_stack(
        "dependent_fn_return_set_instantiates_with_arguments_large_stack",
        || {
            let source_code = r#"
have g fn(S power_set(R)) fn(x S) R
g(R)(0) = g(R)(0)

have fn difference_quotient(X power_set(R), f fn(z X) R, x0 X) fn(y set_minus(X, {x0})) R = fn(x set_minus(X, {x0})) R {(f(x) - f(x0)) / (x - x0)}
difference_quotient(R, fn(z R) R {z}, 0)(1) = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "dependent_fn_return_set_instantiates_with_arguments",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "dependent return sets should verify and instantiate:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn known_equality_implies_weak_order() {
    let source_code = r#"
have a, b R
trust a = b
a <= b
a >= b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_equality_implies_weak_order");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known_equality_implies_weak_order failed:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_uses_standard_set_subset_direction() {
    let source_code = r#"
abstract_prop p(x)
have x set
trust:
    forall u set:
        $p(u)
        =>:
            u $in Z
trust $p(x)
x $in Q
x $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_uses_standard_set_subset_direction",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall with `u $in Z` should prove broader memberships:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_narrowing_requires_known_fact() {
    let source_code = r#"
abstract_prop p(x)
have x set
trust:
    forall u set:
        $p(u)
        =>:
        u $in R
trust $p(x)
x $in Z
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_narrowing_requires_known_fact",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "`u $in R` should not prove narrower `x $in Z` without a known `x $in Z` fact:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_substitute_captured_outer_param() {
    let source_code = r#"
abstract_prop p(x, S)

claim:
    ? forall S, T set:
        forall x R:
            $p(x, S)
        =>:
            $p(1, T)
    $p(1, T)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_substitute_captured_outer_param",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "known forall must keep captured outer parameters rigid:\n{}",
        run_output
    );
}

#[test]
fn known_forall_accepts_identical_captured_outer_param() {
    let source_code = r#"
abstract_prop p(x, S)

claim:
    ? forall S set:
        forall x R:
            $p(x, S)
        =>:
            $p(1, S)
    $p(1, S)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_accepts_identical_captured_outer_param",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall should accept an unchanged captured outer parameter:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_substitute_captured_exist_param() {
    let source_code = r#"
abstract_prop p(x, S)

prop all_p(S set):
    forall x R:
        $p(x, S)

witness exist S, T set st {$all_p(S), $p(1, T)} from N, {}:
    trust $all_p(S)
    $p(1, T)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_substitute_captured_exist_param",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "known forall must keep captured existential parameters rigid:\n{}",
        run_output
    );
}

#[test]
fn parser_rejects_same_name_forall_and_exist_bindings_while_both_are_active() {
    let source_code = r#"
abstract_prop p(x)
have S set

trust:
    forall x set:
        exist x x st {$p(x)}

exist y S st {$p(y)}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "parser_rejects_same_name_forall_and_exist_bindings_while_both_are_active",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "different binder kinds must not reuse an active spelling:\n{}",
        run_output
    );
    assert!(
        run_output.contains("name `x` is already active in this scope"),
        "the parser should identify the active-name collision:\n{}",
        run_output
    );
}

#[test]
fn known_forall_matcher_entry_points_keep_captured_params_rigid() {
    let cases = [
        (
            "equality_rejects_changed_capture",
            r#"
claim:
    ? forall a, b R:
        forall x R:
            x + a = x
        =>:
            1 + b = 1
    1 + b = 1
"#,
            false,
        ),
        (
            "equality_accepts_same_capture",
            r#"
claim:
    ? forall a R:
        forall x R:
            x + a = x
        =>:
            1 + a = 1
    1 + a = 1
"#,
            true,
        ),
        (
            "and_rejects_changed_capture",
            r#"
abstract_prop p(x, S)
abstract_prop q(x, S)
claim:
    ? forall S, T set:
        forall x R:
            $p(x, S) and $q(x, S)
        =>:
            $p(1, T) and $q(1, T)
    $p(1, T) and $q(1, T)
"#,
            false,
        ),
        (
            "and_accepts_same_capture",
            r#"
abstract_prop p(x, S)
abstract_prop q(x, S)
claim:
    ? forall S set:
        forall x R:
            $p(x, S) and $q(x, S)
        =>:
            $p(1, S) and $q(1, S)
    $p(1, S) and $q(1, S)
"#,
            true,
        ),
        (
            "or_rejects_changed_capture",
            r#"
abstract_prop p(x, S)
abstract_prop q(x, S)
claim:
    ? forall S, T set:
        forall x R:
            $p(x, S) or $q(x, S)
        =>:
            $p(1, T) or $q(1, T)
    $p(1, T) or $q(1, T)
"#,
            false,
        ),
        (
            "or_accepts_same_capture",
            r#"
abstract_prop p(x, S)
abstract_prop q(x, S)
claim:
    ? forall S set:
        forall x R:
            $p(x, S) or $q(x, S)
        =>:
            $p(1, S) or $q(1, S)
    $p(1, S) or $q(1, S)
"#,
            true,
        ),
        (
            "exist_rejects_changed_capture",
            r#"
abstract_prop p(x, S)
claim:
    ? forall S, T set:
        forall x R:
            exist y R st {$p(x, S), y = x}
        =>:
            exist z R st {$p(1, T), z = 1}
    exist z R st {$p(1, T), z = 1}
"#,
            false,
        ),
        (
            "exist_accepts_same_capture",
            r#"
abstract_prop p(x, S)
claim:
    ? forall S set:
        forall x R:
            exist y R st {$p(x, S), y = x}
        =>:
            exist z R st {$p(1, S), z = 1}
    exist z R st {$p(1, S), z = 1}
"#,
            true,
        ),
        (
            "strategy_rejects_changed_capture",
            r#"
abstract_prop p(x, S)
have S, T set
strategy use_p:
    ? forall x R:
        $p(x, S)

    trust:
        forall y R:
            $p(y, S)
use strategy use_p
$p(1, T)
"#,
            false,
        ),
        (
            "strategy_accepts_same_capture",
            r#"
abstract_prop p(x, S)
have S set
strategy use_p:
    ? forall x R:
        $p(x, S)

    trust:
        forall y R:
            $p(y, S)
use strategy use_p
$p(1, S)
"#,
            true,
        ),
    ];

    for (name, source_code, expected_success) in cases {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert_eq!(
            run_succeeded, expected_success,
            "known-forall matcher case {name} returned the wrong result:\n{run_output}"
        );
    }
}

#[test]
fn instantiation_avoids_capturing_forall_arguments() {
    let cases = [
        (
            "definition_rejects_captured_argument",
            r#"
abstract_prop p(x)

prop q(n R):
    $p(n)
    forall n R:
        $p(n)

claim:
    ? forall n R:
        $p(n)
        =>:
            $q(n)
    $q(n)
"#,
            false,
        ),
        (
            "theorem_rejects_captured_argument",
            r#"
abstract_prop p(x, y)
abstract_prop q(x)
axiom t:
    ? forall a R:
        forall n R:
            $p(a, n)
        =>:
            $q(a)
claim:
    ? forall n R:
        $p(n, n)
        =>:
            $q(n)
    by thm t(n)
    $q(n)
"#,
            false,
        ),
        (
            "compound_argument_rejects_capture",
            r#"
abstract_prop p(x, y)
abstract_prop q(x)
axiom t:
    ? forall a R:
        forall n R:
            $p(a, n)
        =>:
            $q(a)
claim:
    ? forall n R:
        $p(n + 0, n)
        =>:
            $q(n + 0)
    by thm t(n + 0)
    $q(n + 0)
"#,
            false,
        ),
        (
            "forall_iff_rejects_captured_argument",
            r#"
abstract_prop p(x, y)
abstract_prop r(x, y)
prop q(a R):
    forall n R:
        =>:
            $p(a, n)
        <=>:
            $r(a, n)
claim:
    ? forall n R:
        $p(n, n)
        $r(n, n)
        =>:
            $q(n)
    $q(n)
"#,
            false,
        ),
        (
            "alpha_rename_preserves_same_named_identifier_in_binder_type",
            r#"
have n set
abstract_prop p(x, y)
abstract_prop q(x)
axiom t:
    ? forall a set:
        forall n n:
            $p(a, n)
        =>:
            $q(a)
claim:
    ? forall n set:
        n $in n
        $p(n, n)
        =>:
            $q(n)
    by thm t(n)
    $q(n)
"#,
            false,
        ),
        (
            "definition_accepts_explicit_universal_premise",
            r#"
abstract_prop p(x)

prop q(a R):
    $p(a)
    forall m R:
        $p(m)

claim:
    ? forall n R:
        $p(n)
        forall m R:
            $p(m)
        =>:
            $q(n)
    $q(n)
"#,
            true,
        ),
        (
            "theorem_accepts_explicit_universal_premise",
            r#"
abstract_prop p(x, y)
abstract_prop q(x)
axiom t:
    ? forall a R:
        forall k R:
            $p(a, k)
        =>:
            $q(a)
claim:
    ? forall n R:
        forall k R:
            $p(n, k)
        =>:
            $q(n)
    by thm t(n)
    $q(n)
"#,
            true,
        ),
    ];

    for (name, source_code, expected_success) in cases {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert_eq!(
            run_succeeded, expected_success,
            "capture-avoiding instantiation case {name} returned the wrong result:\n{run_output}"
        );
    }
}

#[test]
fn instantiation_avoids_capturing_exist_arguments() {
    let cases = [
        (
            "exist_rejects_captured_definition_argument",
            r#"
abstract_prop p(x, y)
prop q(a R):
    exist n R st {$p(a, n)}

trust exist w R st {$p(w, w)}
witness exist n R st {$q(n)} from 0:
    $q(n)
"#,
            false,
        ),
        (
            "exist_accepts_an_explicit_witness_after_alpha_rename",
            r#"
abstract_prop p(x, y)
prop q(a R):
    exist n R st {$p(a, n)}

trust $p(0, 1)
witness exist n R st {$q(n)} from 0:
    witness exist m R st {$p(n, m)} from 1
    $q(n)
"#,
            true,
        ),
    ];

    for (name, source_code, expected_success) in cases {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert_eq!(
            run_succeeded, expected_success,
            "exist capture-avoidance case {name} returned the wrong result:\n{run_output}"
        );
    }
}

#[test]
fn known_forall_equality_uses_indexed_function_head() {
    let source_code = r#"
have f fn(x R) R
trust forall a R:
    f(a) = a
f(1) = 1
"#;

    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("known_forall_equality_uses_indexed_function_head");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "indexed equality-in-forall should prove matching function applications:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_indexes_forall_param_side_as_wildcard() {
    let source_code = r#"
have f fn(x R) R
trust forall a R:
    a = f(a)
1 + 1 = f(1 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_indexes_forall_param_side_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param equality side should match non-atom target sides:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
have g fn(x R) R
trust forall f fn(x R) R, a R:
    f(a) = a
g(1) = 1
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads should be checked through the fallback equality bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_forall_param_arg_as_wildcard() {
    let source_code = r#"
abstract_prop p(x)
trust forall x R:
    $p(x)
$p(1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_indexes_forall_param_arg_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param prop arg should match concrete target args through arg-shape index:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_expression_arg_shape() {
    let source_code = r#"
abstract_prop p(x)
trust forall x R:
    $p(x + 1)
$p(1 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_expression_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "expression prop args should be indexed by their top-level operator shape:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_multi_arg_shape() {
    let source_code = r#"
abstract_prop p(a, b)
trust forall a, b R:
    $p(a, b + 1)
$p(2, 3 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_multi_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "multi-arg prop facts should match wildcard and exact arg-shape positions:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
abstract_prop p(x)
have g fn(x R) R
trust forall f fn(x R) R:
    $p(f(2))
$p(g(2))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads in prop args should be checked through the fallback bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_matches_function_param_application_inside_anonymous_fn_body() {
    let source_code = r#"
abstract_prop p(x)

trust forall f, g fn(x R) R:
    $p(f)
    $p(g)
    =>:
        $p(fn(x R) R {f(x) + g(x)})

claim:
    ? forall a, b, c fn(x R) R:
        $p(a)
        $p(b)
        $p(c)
        =>:
            $p(fn(x R) R {a(x) + (b(x) + c(x))})
    $p(fn(x R) R {b(x) + c(x)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_matches_function_param_application_inside_anonymous_fn_body",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall should infer g = anonymous fn from g(x) inside the anonymous body:\n{}",
        run_output
    );
}

#[test]
fn known_forall_binds_named_function_prefix_inside_different_codomain_anonymous_body() {
    let source_code = r#"
abstract_prop p(x)

trust forall F fn(K {1}) power_set({1}):
    forall K {1}:
        $is_finite_set(F(K))
    =>:
        $p(fn(K {1}) N {finite_set_size(F(K))})

have fn rows(a R) fn(L {1}) power_set({1}) = fn(t {1}) power_set({1}) {{1}}

claim:
    ? forall a R:
        forall M {1}:
            $is_finite_set(rows(a)(M))
        =>:
            $p(fn(x {1}) N {finite_set_size(rows(a)(x))})
    claim:
        ? forall M {1}:
            $is_finite_set(rows(a)(M))
        rows(a)(M) = {1}
    $p(fn(x {1}) N {finite_set_size(rows(a)(x))})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_binds_named_function_prefix_inside_different_codomain_anonymous_body",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall should bind F to the callable rows(a) prefix, not synthesize an N-valued function:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_strip_nonmatching_named_function_suffix() {
    let source_code = r#"
abstract_prop p(x)

trust forall F fn(K {1}) power_set({1}):
    forall K {1}:
        $is_finite_set(F(K))
    =>:
        $p(fn(K {1}) N {finite_set_size(F(K))})

have fn rows(a R) fn(L {1}) power_set({1}) = fn(t {1}) power_set({1}) {{1}}

claim:
    ? forall a R:
        forall M {1}:
            $is_finite_set(rows(a)(M))
        =>:
            $p(fn(x {1}) N {finite_set_size(rows(a)(1))})
    claim:
        ? forall M {1}:
            $is_finite_set(rows(a)(M))
        rows(a)(M) = {1}
    $p(fn(x {1}) N {finite_set_size(rows(a)(1))})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_strip_nonmatching_named_function_suffix",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded && run_output.contains("atomic fact unknown"),
        "only an exact anonymous-binder suffix may be stripped:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_infer_function_from_single_point_application() {
    let source_code = r#"
abstract_prop p(x)

trust forall g fn(x R) R:
    $p(fn(x R) R {g(0)})

have h fn(x R) R
$p(fn(x R) R {h(x)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_infer_function_from_single_point_application",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "known forall should not infer a whole function from a single point application:\n{}",
        run_output
    );
}

#[test]
fn eval_recursive_algo_memoizes_overlapping_calls() {
    run_with_large_stack(
        "eval_recursive_algo_memoizes_overlapping_calls_large_stack",
        || {
            let source_code = r#"
sketch:
    have fib fn(x N) N

    trust:
        forall x N:
            x = 0
            =>:
                fib(x) = 0

        forall x N:
            x = 1
            =>:
                fib(x) = 1

        forall x N:
            x > 1
            =>:
                fib(x) = fib(x - 1) + fib(x - 2)

    have algo for fib(x):
        case x = 0: 0
        case x = 1: 1
        case x > 1: fib(x - 1) + fib(x - 2)

    eval fib(25)
    fib(25) = 75025
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "eval_recursive_algo_memoizes_overlapping_calls",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "eval_recursive_algo_memoizes_overlapping_calls failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn reduce_and_finite_set_reduce_obey_order_empty_and_operation_law_contracts() {
    run_with_large_stack(
        "reduce_and_finite_set_reduce_obey_order_empty_and_operation_law_contracts",
        || {
            let positive_source = r#"
have fn id_z(x Z) Z = x
have fn sub_z(x, y Z) Z = x - y
have fn add_z(x, y Z) Z = x + y
have fn mul_z(x, y Z) Z = x * y

reduce(1, 3, id_z, sub_z, 0) = -6
reduce(3, 2, id_z, sub_z, 10) = 10
reduce(1, 3, id_z, sub_z, 0) $in Z
reduce(1, 3, id_z, add_z, 0) = sum(1, 3, id_z)
reduce(1, 3, id_z, mul_z, 1) = product(1, 3, id_z)
reduce(1, 4, id_z, sub_z, 0) = reduce(3, 4, id_z, sub_z, reduce(1, 2, id_z, sub_z, 0))

forall T set, a, b Z, f fn(x Z) T, op fn(x, y T) T, seed T:
    a <= b
    =>:
        reduce(a, b, f, op, seed) = reduce(0, b - a, fn(k Z) T {f(a + k)}, op, seed)
        reduce(a, b, f, op, seed) = reduce(a + 1, b, f, op, op(seed, f(a)))
        reduce(a, b, f, op, seed) = op(reduce(a, b - 1, f, op, seed), f(b))

forall a, b, c, d Z, f fn(x Z) Z, op fn(x, y Z) Z, seed Z:
    a <= b
    b - a = d - c
    =>:
        reduce(a, b, f, op, seed) = reduce(c, d, fn(k Z) Z {f(a + (k - c))}, op, seed)

forall a, b Z, f fn(x Z) Z, op fn(x, y Z) Z, seed Z:
    b < a
    =>:
        reduce(a, b, f, op, seed) = reduce(0, b - a, fn(k Z) Z {f(a + k)}, op, seed)

finite_set_reduce({3, 1, 2}, id_z, add_z, 0) = 6
finite_set_reduce({}, id_z, add_z, 5) = 5
finite_set_reduce({1, 2}, id_z, add_z, 0) $in Z
finite_set_reduce(1...3, id_z, add_z, 0) = reduce(1, 3, id_z, add_z, 0)
finite_set_reduce({1, 2, 3}, id_z, add_z, 0) = finite_set_sum({1, 2, 3}, id_z)
finite_set_reduce({1, 2, 3}, id_z, mul_z, 1) = finite_set_product({1, 2, 3}, id_z)

not 3 $in {1, 2}
finite_set_reduce(union({3}, {1, 2}), id_z, add_z, 0) = 3 + finite_set_reduce({1, 2}, id_z, add_z, 0)

prop is_add_operation_z(op fn(x, y Z) Z):
    forall x, y Z:
        op(x, y) = x + y

forall op fn(x, y Z) Z:
    $is_add_operation_z(op)
    =>:
        reduce(1, 3, id_z, op, 0) = sum(1, 3, id_z)

forall f, g fn(x Z) Z:
    $fn_eq_in(f, g, 1...3)
    =>:
        reduce(1, 3, f, add_z, 0) = reduce(1, 3, g, add_z, 0)
        finite_set_reduce(1...3, f, add_z, 0) = finite_set_reduce(1...3, g, add_z, 0)

forall A, B finite_set:
    A $subset Z
    B $subset Z
    intersect(A, B) = {}
    =>:
        finite_set_reduce(union(A, B), id_z, add_z, 5) = finite_set_reduce(A, id_z, add_z, finite_set_reduce(B, id_z, add_z, 5))

prop reduce_assoc_comm(T set, op fn(x, y T) T):
    forall x, y, z T:
        op(op(x, y), z) = op(x, op(y, z))
    forall x, y T:
        op(x, y) = op(y, x)

forall T set, op fn(x, y T) T, seed T, A, B finite_set, f fn(x A) T, g fn(y B) A:
    $reduce_assoc_comm(T, op)
    $bijective(B, A, g)
    =>:
        finite_set_reduce(A, f, op, seed) = finite_set_reduce(B, fn(y B) T {f(g(y))}, op, seed)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("reduce_positive_contracts");
            let (stmt_results, runtime_error) = run_source_code(positive_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "reduce positive contracts should verify:\n{}",
                run_output
            );

            let noncommutative_source = r#"
finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(x, y Z) Z {x - y}, 0) = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(x, y Z) Z {x - y}, 0)
"#;
            let mut rejected_runtime = Runtime::new();
            rejected_runtime
                .new_file_path_new_env_new_name_scope("finite_set_reduce_rejects_subtraction");
            let (stmt_results, runtime_error) =
                run_source_code(noncommutative_source, &mut rejected_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &rejected_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                !run_succeeded,
                "finite_set_reduce must reject a nonassociative operation:\n{}",
                run_output
            );
            assert!(
                run_output.contains("not verified associative"),
                "the rejection should expose the failed operation law:\n{}",
                run_output
            );

            let wrong_seed_source = r#"
have fn id_z(x Z) Z = x
have fn add_z(x, y Z) Z = x + y
reduce(1, 3, id_z, add_z, 1) = sum(1, 3, id_z)
"#;
            let mut wrong_seed_runtime = Runtime::new();
            wrong_seed_runtime.new_file_path_new_env_new_name_scope("reduce_wrong_sum_seed");
            let (stmt_results, runtime_error) =
                run_source_code(wrong_seed_source, &mut wrong_seed_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &wrong_seed_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                !run_succeeded,
                "the sum bridge must reject a nonzero seed:\n{}",
                run_output
            );

            let missing_bijection_source = r#"
have fn add_z(x, y Z) Z = x + y
forall A, B finite_set, f fn(x A) Z, g fn(y B) A:
    finite_set_reduce(A, f, add_z, 0) = finite_set_reduce(B, fn(y B) Z {f(g(y))}, add_z, 0)
"#;
            let mut missing_bijection_runtime = Runtime::new();
            missing_bijection_runtime
                .new_file_path_new_env_new_name_scope("reduce_requires_bijection_for_reindexing");
            let (stmt_results, runtime_error) =
                run_source_code(missing_bijection_source, &mut missing_bijection_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &missing_bijection_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                !run_succeeded,
                "finite_set_reduce reindexing must not invent a bijection:\n{}",
                run_output
            );

            let reversed_order_source = r#"
have fn id_z(x Z) Z = x
have fn decimal_append_z(x, y Z) Z = 10 * x + y
reduce(1, 2, id_z, decimal_append_z, 0) = reduce(1, 2, fn(k Z) Z {id_z(3 - k)}, decimal_append_z, 0)
"#;
            let mut reversed_order_runtime = Runtime::new();
            reversed_order_runtime
                .new_file_path_new_env_new_name_scope("reduce_rejects_order_reversal");
            let (stmt_results, runtime_error) =
                run_source_code(reversed_order_source, &mut reversed_order_runtime);
            let (run_succeeded, run_output) = render_run_source_code_output(
                &reversed_order_runtime,
                &stmt_results,
                &runtime_error,
                false,
            );
            assert!(
                !run_succeeded,
                "reduce must not treat an arbitrary reordering as an order-preserving translation:\n{}",
                run_output
            );
        },
    );
}
