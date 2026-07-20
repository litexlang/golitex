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
                "eval: case condition cannot be logically negated",
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

fn run_kernel_soundness_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
