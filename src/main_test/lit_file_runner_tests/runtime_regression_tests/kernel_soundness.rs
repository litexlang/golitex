use super::*;

#[test]
fn recursive_function_induction_requires_an_integer_valued_measure() {
    run_with_large_stack(
        "recursive_function_induction_requires_an_integer_valued_measure",
        || {
            let invalid_cases = [
                (
                    "dense_real_measure",
                    r#"
have fn dense(x R_pos) N by induc x from 0:
    case x > 0: dense(x / 2) + 1
"#,
                    "the measure must be provably integer-valued",
                ),
                (
                    "fractional_measure",
                    r#"
have fn half_rank(n N_pos) N by induc n / 2 from 0:
    case n > 0: 0
"#,
                    "the measure must be provably integer-valued",
                ),
                (
                    "fractional_lower_bound",
                    r#"
have fn fractional_start(n N_pos) N by induc n from 1 / 2:
    case n > 0: 0
"#,
                    "the lower bound must be provably integer-valued",
                ),
            ];

            for (label, source_code, expected_error) in invalid_cases {
                let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
                assert!(
                    !run_succeeded,
                    "{} should reject a non-integer recursion rank:\n{}",
                    label, run_output
                );
                assert!(
                    run_output.contains(expected_error),
                    "{} should report the integer-valued recursion requirement:\n{}",
                    label,
                    run_output
                );
            }

            let valid_cases = [
                (
                    "natural_measure",
                    r#"
have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: countdown(n - 1) + 1
"#,
                ),
                (
                    "integer_measure_with_real_state",
                    r#"
have fn ranked_state(x R, n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: ranked_state(x, n - 1) + 1
"#,
                ),
                (
                    "derived_integer_measure",
                    r#"
have fn two_arg(a, b Z: a >= 0, b >= 0) N by induc a + b from 0:
    case b = 0: 0
    case b > 0: two_arg(a, b - 1) + 1
"#,
                ),
                (
                    "concrete_domain_same_spelling_as_induction_parameter",
                    r#"
have X set = N
trust forall n N:
    n $in X
have fn countdown(X X) N by induc X from 0:
    case X = 0: 0
    case X > 0: countdown(X - 1) + 1
"#,
                ),
            ];

            for (label, source_code) in valid_cases {
                let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
                assert!(
                    run_succeeded,
                    "{} should accept an integer-valued recursion measure:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn function_equality_symmetry_is_not_logical_negation() {
    run_with_large_stack("function_equality_symmetry_is_not_logical_negation", || {
        let invalid_cases = [
            (
                "fn_eq_fake_excluded_middle",
                r#"
have f, g fn(x R) R
$fn_eq(f, g) or $fn_eq(g, f)
"#,
                "verification failed",
            ),
            (
                "fn_eq_in_fake_excluded_middle",
                r#"
have f, g fn(x R) R
$fn_eq_in(f, g, R) or $fn_eq_in(g, f, R)
"#,
                "verification failed",
            ),
            (
                "fn_eq_by_contra",
                r#"
have f fn(x R) R
have g fn(x R) R
by contra $fn_eq(f, g):
    impossible $fn_eq(g, f)
$fn_eq(f, g)
"#,
                "logical negation is not supported for `$fn_eq(f, g)`",
            ),
            (
                "fn_eq_case_partition",
                r#"
have f, g fn(x R) R
have fn h(x R) R by cases:
    case $fn_eq(f, g): 0
    case $fn_eq(g, f): 1
"#,
                "cases do not cover the declared domain",
            ),
            (
                "fn_eq_eval_case",
                r#"
have f, g fn(x R) R
have fn h(x R) R = 0
have algo for h(x):
    case $fn_eq(f, g): 0
    0
eval h(0)
"#,
                "algo verify: default branch cannot negate case condition",
            ),
        ];

        for (label, source_code, expected_error) in invalid_cases {
            let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
            assert!(
                !run_succeeded,
                "{} should not treat transposed function equality as negation:\n{}",
                label, run_output
            );
            assert!(
                run_output.contains(expected_error),
                "{} should report the unsupported proof route:\n{}",
                label,
                run_output
            );
            assert!(
                !run_output.contains("complementary facts cover all cases"),
                "{} should not cite excluded middle for transposed function equality:\n{}",
                label,
                run_output
            );
        }

        let line_file = (1, std::rc::Rc::<str>::from("fn_eq_typed_negation_helper"));
        let f: Obj = Identifier::new("f".to_string()).into();
        let g: Obj = Identifier::new("g".to_string()).into();
        let fn_eq: AtomicFact = FnEqualFact::new(f.clone(), g.clone(), line_file.clone()).into();
        assert!(fn_eq.logical_negation().is_err());
        assert_eq!(
            fn_eq
                .transposed_binary_order_equivalent()
                .expect("FnEq symmetry should remain available")
                .to_string(),
            FnEqualFact::new(g, f, line_file).to_string()
        );
        assert!(Runtime::negated_domain_fact_for_by_for_skip(&fn_eq.into()).is_none());

        let ordinary_negation = r#"
have x R
x = 0 or x != 0
"#;
        let (run_succeeded, run_output) =
            run_kernel_soundness_source(ordinary_negation, "ordinary_atomic_negation");
        assert!(
            run_succeeded,
            "ordinary atomic facts should retain logical negation:\n{}",
            run_output
        );
        assert!(
            run_output.contains("complementary facts cover all cases"),
            "ordinary excluded middle should retain its proof explanation:\n{}",
            run_output
        );
    });
}

#[test]
fn anonymous_function_alpha_equivalence_keeps_concrete_parameter_sets_rigid() {
    let invalid_cases = [
        (
            "anonymous_function_equality_different_domains",
            r#"
have X, Y set
trust X != Y
fn(X X) R {0} = fn(Y Y) R {0}
"#,
        ),
        (
            "anonymous_function_membership_different_domains",
            r#"
have X, Y set
trust X != Y
fn(X X) R {0} $in fn(Y Y) R
"#,
        ),
        (
            "known_forall_anonymous_function_different_domains",
            r#"
abstract_prop p(f)
have X, Y set
trust X != Y
trust:
    forall z R:
        $p(fn(X X) R {z})
$p(fn(Y Y) R {0})
"#,
        ),
    ];

    for (label, source_code) in invalid_cases {
        let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
        assert!(
            !run_succeeded,
            "alpha-renaming a function binder must not rename its concrete domain:\n{}",
            run_output
        );
    }

    let valid_source = r#"
abstract_prop p(f)
have X set
fn(x X) X {x} = fn(y X) X {y}
trust:
    forall z R:
        $p(fn(x X) R {z})
$p(fn(y X) R {0})
"#;
    let (run_succeeded, run_output) =
        run_kernel_soundness_source(valid_source, "anonymous_function_alpha_equivalence");
    assert!(
        run_succeeded,
        "ordinary alpha-equivalent anonymous functions should remain equal:\n{}",
        run_output
    );
}

#[test]
fn binder_normalization_keeps_concrete_parameter_types_rigid() {
    let invalid_cases = [
        (
            "exist_alpha_normalization_different_concrete_types",
            r#"
have X set = N
have Y set = {}
trust exist X X st {X = X}
exist Y Y st {Y = Y}
"#,
        ),
        (
            "fnset_directional_equality_different_concrete_types",
            r#"
have X, Y, S nonempty_set
trust X != Y
fn(a X, X S: a $in X) R = fn(a Y, Y S: a $in Y) R
"#,
        ),
        (
            "exist_unique_fresh_binders_do_not_capture_outer_forall",
            r#"
abstract_prop p(x, c)
trust:
    forall a, b R:
        $p(a, a)
        $p(b, a)
        =>:
            a = b
claim:
    ? forall x1 R:
        exist x R st {$p(x, x1)}
        =>:
            exist! x R st {$p(x, x1)}
    exist! x R st {$p(x, x1)}
"#,
        ),
        (
            "nested_forall_scopes_keep_distinct_binder_identities",
            r#"
trust:
    forall S nonempty_set:
        exist w S st {w = w, forall! a R => {exist z R st {z = z, forall! b R => {b = b}}}}
exist v N st {v = v, forall! c R => {exist z R st {z = z, forall! d R => {d = c}}}}
"#,
        ),
        (
            "ordinary_induction_does_not_capture_outer_forall_in_start_bound",
            r#"
claim:
    ? forall n N:
        -1 >= 0
    by induc n from n:
        ? n >= 0
        n >= 0
        forall m Z:
            m >= 0
            =>:
                m + 1 >= 0
    -1 >= 0
"#,
        ),
        (
            "strong_induction_does_not_capture_outer_forall_in_start_bound",
            r#"
claim:
    ? forall n N:
        -1 >= 0
    by strong_induc n from n:
        ? n >= 0
        n >= 0
        forall m Z:
            m >= 0
            =>:
                m + 1 >= 0
    -1 >= 0
"#,
        ),
        (
            "finite_set_induction_does_not_capture_outer_forall_carrier",
            r#"
claim:
    ? forall P finite_set:
        P = {0}
        =>:
            {-1} $subset {0}
    by induc P in P:
        ? P $subset {0}
        ? from P = {}:
            {} $subset {0}
        ? induc x, S:
            x $in P
            P = {0}
            x $in {0}
            S $subset {0}
            claim:
                ? forall z union({x}, S):
                    z $in {0}
                z $in {x} or z $in S
                by cases:
                    ? z $in {0}
                    case z $in {x}:
                        z = x
                        z $in {0}
                    case z $in S:
                        z $in {0}
            union({x}, S) $subset {0}
    {-1} $subset {0}
"#,
        ),
        (
            "algorithm_verification_does_not_capture_outer_forall",
            r#"
have fn f(t R) R = 0
claim:
    ? forall x R:
        x = 0
        =>:
            0 = 0
    have algo for f(x):
        case x = x: x
    0 = 0
"#,
        ),
        (
            "algorithm_default_return_is_verified",
            r#"
have fn f(x R) R = 0
have algo for f(x):
    1
"#,
        ),
        (
            "algorithm_mixed_default_return_is_verified_on_complement",
            r#"
have fn f(x R) R = 0
have algo for f(x):
    case x = 0: 0
    1
"#,
        ),
        (
            "forall_alpha_cache_keeps_captured_parameters_rigid",
            r#"
abstract_prop p(x, c)
have c, d R
trust:
    forall x R:
        $p(x, c)
forall y R:
    $p(y, d)
"#,
        ),
        (
            "forall_alpha_cache_keeps_outer_forall_parameters_rigid",
            r#"
abstract_prop p(x, S)
abstract_prop q(x)
claim:
    ? forall Qset nonempty_set, R0 set, a Qset:
        $q(a)
    trust:
        forall n Qset:
            $p(n, Qset)
    trust forall z Qset:
        forall m Qset:
            $p(m, R0)
        =>:
            $q(z)
    $q(a)
"#,
        ),
    ];

    for (label, source_code) in invalid_cases {
        let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
        assert!(
            !run_succeeded,
            "binder normalization must not rewrite captured concrete parameters:\n{}",
            run_output
        );
    }

    let valid_cases = [
        (
            "exist_alpha_normalization_same_concrete_type",
            r#"
have X set = N
trust exist a X st {a = a}
exist b X st {b = b}
"#,
        ),
        (
            "fnset_alpha_equality_same_concrete_type",
            r#"
have X nonempty_set
fn(a X) R = fn(b X) R
"#,
        ),
        (
            "have_fn_store_same_spelling_concrete_domain",
            r#"
have X set = N
have fn f(X X) R by cases:
    case X = X: 0
"#,
        ),
        (
            "known_forall_exist_alpha_key_handles_inline_dependent_forall",
            r#"
trust:
    forall S set:
        exist x S st {forall! x x => {x = x}}
exist y N st {forall! y y => {y = y}}
"#,
        ),
        (
            "have_fn_keeps_captured_outer_induction_parameter_rigid",
            r#"
by induc P:
    ? P = P
    ? from P = {}:
        {} = {}
    ? induc x, S:
        S = S
        have fn f(S S) R by cases:
            case S = S: 0
        union({x}, S) = union({x}, S)
"#,
        ),
        (
            "have_fn_parameter_type_keeps_captured_outer_forall_rigid",
            r#"
claim:
    ? forall X set, a X:
        a = a
    have fn f(X X) R by cases:
        case X = X: 0
    f(a) = 0
    a = a
"#,
        ),
        (
            "algorithm_default_return_matches_declared_function",
            r#"
have fn f(x R) R = 0
have algo for f(x):
    0
"#,
        ),
        (
            "algorithm_mixed_default_matches_on_complement",
            r#"
have fn f(x R) R = 0
have algo for f(x):
    case x = 0: 0
    0
"#,
        ),
        (
            "not_exist_conversion_freshens_cross_kind_binder",
            r#"
claim:
    ? forall X nonempty_set:
        X = {0}
        =>:
            0 = 0
    trust not exist X X st {X != 0}
    claim:
        ? forall y X:
            y = 0
        y = 0
    0 = 0
"#,
        ),
        (
            "not_forall_conversion_uses_fresh_exist_binder",
            r#"
abstract_prop p(x)
trust not forall x R:
    $p(x)
obtain y from exist x R st {not $p(x)}
not $p(y)
"#,
        ),
        (
            "have_fn_by_exist_freshens_same_named_witness",
            r#"
have fn f by exist!:
    ? forall x R:
        exist! x {0} st {x = x}
    trust exist! x {0} st {x = x}
forall t R:
    f(t) = 0
"#,
        ),
        (
            "strong_induction_uses_alpha_equivalent_fresh_hypothesis",
            r#"
abstract_prop p(a)

claim:
    ? forall n Z:
        $p(0)
        forall m Z:
            m >= 0
            forall z Z:
                z >= 0
                z <= m
                =>:
                    $p(z)
            =>:
                $p(m + 1)
        n >= 0
        =>:
            $p(n)
    by strong_induc n from 0:
        ? $p(n)
        ? from n = 0:
            $p(0)
        ? strong_induc:
            $p(n + 1)
"#,
        ),
        (
            "forall_alpha_cache_ignores_equivalent_parameter_grouping",
            r#"
abstract_prop p(x, y)
abstract_prop q(z)
trust:
    forall x, y R:
        $p(x, y)
trust forall z R:
    forall u R, v R:
        $p(u, v)
    =>:
        $q(z)
$q(0)
"#,
        ),
        (
            "forall_alpha_cache_preserves_dependent_telescope_when_flattening_groups",
            r#"
abstract_prop p(S, x, y)
abstract_prop q(z)
trust:
    forall S set, x, y S:
        $p(S, x, y)
trust forall z R:
    forall T set, u T, v T:
        $p(T, u, v)
    =>:
        $q(z)
$q(0)
"#,
        ),
        (
            "forall_alpha_cache_accepts_same_outer_forall_parameter",
            r#"
abstract_prop p(x, S)
abstract_prop q(x)
claim:
    ? forall Qset nonempty_set, a Qset:
        $q(a)
    trust:
        forall n Qset:
            $p(n, Qset)
    trust forall z Qset:
        forall m Qset:
            $p(m, Qset)
        =>:
            $q(z)
    $q(a)
"#,
        ),
    ];

    for (label, source_code) in valid_cases {
        let (run_succeeded, run_output) = run_kernel_soundness_source(source_code, label);
        assert!(
            run_succeeded,
            "typed binder normalization should preserve the valid program:\n{}",
            run_output
        );
    }
}

#[test]
fn forall_alpha_cache_preserves_proof_trust() {
    let trusted_source = r#"
abstract_prop p(x)
trust:
    forall x R:
        $p(x)
thm alpha_from_trust:
    ? forall y R:
        $p(y)
    forall z R:
        $p(z)
"#;
    let mut trusted_runtime = Runtime::new();
    trusted_runtime
        .new_file_path_new_env_new_name_scope("forall_alpha_cache_preserves_proof_trust");
    let (trusted_results, trusted_error) = run_source_code(trusted_source, &mut trusted_runtime);
    let (trusted_succeeded, trusted_output) =
        render_run_source_code_output(&trusted_runtime, &trusted_results, &trusted_error, false);
    assert!(
        trusted_succeeded,
        "trusted alpha-equivalent forall should verify:\n{}",
        trusted_output
    );
    assert!(
        !trusted_runtime
            .get_thm_trust_summary_by_name("alpha_from_trust")
            .is_empty(),
        "alpha-equivalent forall cache hits must retain indirect trust"
    );

    let clean_source = r#"
forall x R:
    x = x
thm clean_alpha:
    ? forall y R:
        y = y
    forall z R:
        z = z
"#;
    let mut clean_runtime = Runtime::new();
    clean_runtime.new_file_path_new_env_new_name_scope("forall_alpha_cache_stays_clean");
    let (clean_results, clean_error) = run_source_code(clean_source, &mut clean_runtime);
    let (clean_succeeded, clean_output) =
        render_run_source_code_output(&clean_runtime, &clean_results, &clean_error, false);
    assert!(
        clean_succeeded,
        "clean alpha-equivalent forall should verify:\n{}",
        clean_output
    );
    assert!(
        clean_runtime
            .get_thm_trust_summary_by_name("clean_alpha")
            .is_empty(),
        "a clean alpha-equivalent forall cache hit must remain clean"
    );
}

#[test]
fn c11_eventuality_rejects_substitution_of_captured_set_parameter() {
    let source_code = r#"
prop contains_natural_tail_from_unsound(a N, S power_set(N)):
    forall n N:
        n >= a
        =>:
            n $in S

prop contains_natural_tail_unsound(S power_set(N)):
    exist a N st {$contains_natural_tail_from_unsound(a, S)}

prop eventually_on_N_unsound(S power_set(N)):
    $contains_natural_tail_unsound(S)

thm unsound_eventually_changes_set:
    ? forall Qset, R0 power_set(N):
        $eventually_on_N_unsound(Qset)
        =>:
            $eventually_on_N_unsound(R0)
    obtain b from exist b0 N st {$contains_natural_tail_from_unsound(b0, Qset)}
    witness exist k N st {$contains_natural_tail_from_unsound(k, R0)} from b:
        forall n N:
            n >= b
            =>:
                n $in Qset
                n $in R0
        by def $contains_natural_tail_from_unsound(b, R0)
    by def $contains_natural_tail_unsound(R0)
    by def $eventually_on_N_unsound(R0)
"#;

    let (run_succeeded, run_output) =
        run_kernel_soundness_source(source_code, "c11_eventuality_capture_regression");
    assert!(
        !run_succeeded,
        "an eventuality fact about Qset must not prove the same fact about unrelated R0:\n{}",
        run_output
    );
    assert!(
        run_output.contains("~1n $in ~1R0"),
        "the original false proof should fail at the changed captured set:\n{}",
        run_output
    );
}

#[test]
fn generated_subset_binder_does_not_capture_outer_forall_parameter() {
    let source_code = r#"
forall x1 R:
    {0} $subset {x1}
"#;

    let (run_succeeded, run_output) =
        run_kernel_soundness_source(source_code, "generated_subset_binder_capture_regression");
    assert!(
        !run_succeeded,
        "the false claim {{0}} subset {{x1}} must not become true by reusing outer x1 as the generated membership binder:\n{}",
        run_output
    );
}

fn run_kernel_soundness_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
