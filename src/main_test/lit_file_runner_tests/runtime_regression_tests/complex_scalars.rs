use super::*;

#[test]
fn native_complex_ast_keywords_do_not_use_builtin_symbol_ids() {
    let last_existing = builtin_symbol_ref(BIJECTIVE).expect("existing builtin ID should remain");
    assert_eq!(last_existing.id().value(), (1_u64 << 62) + 47);

    for name in [C, I, RE, IMG, C_ABS] {
        assert!(is_keyword(name), "{name} should remain hard reserved");
        assert!(
            !is_builtin_identifier_name(name),
            "{name} should not use the builtin Identifier path"
        );
        assert!(
            builtin_symbol_ref(name).is_none(),
            "{name} should not allocate a builtin SymbolId"
        );
    }
}

#[test]
fn native_complex_scalar_contract_is_checkable() {
    run_with_large_stack("native_complex_scalar_contract_is_checkable", || {
        let source_code = r#"
i $in C
i * i = -1
i ^ 2 = -1
i ^ 4 = 1
i ^ (-1) = -i
re(i) = 0
img(i) = 1
C_abs(i) = 1

+ $in fn(a, b C) C
- $in fn(a, b C) C
* $in fn(a, b C) C
/ $in fn(a, b C: b != 0) C
^ $in fn(z C, n N) C
^ $in fn(z C, k Z: z != 0) C

forall r R:
    re(r) = r
    img(r) = 0
    C_abs(r) = abs(r)

forall a, b R:
    re(a + b * i) = a
    img(a + b * i) = b

forall z, w C:
    re(z + w) = re(z) + re(w)
    img(z + w) = img(z) + img(w)
    re(z - w) = re(z) - re(w)
    img(z - w) = img(z) - img(w)
    re(z * w) = re(z) * re(w) - img(z) * img(w)
    img(z * w) = re(z) * img(w) + img(z) * re(w)

forall z C, n N:
    re(z ^ (n + 1)) = re(z ^ n) * re(z) - img(z ^ n) * img(z)
    img(z ^ (n + 1)) = re(z ^ n) * img(z) + img(z ^ n) * re(z)

forall z, w C:
    z = w
    =>:
        re(z) = re(w)
        img(z) = img(w)

forall z C:
    re(z) $in R
    img(z) $in R
    C_abs(z) $in R
    z = re(z) + img(z) * i
    C_abs(z) = sqrt(re(z) ^ 2 + img(z) ^ 2)
    C_abs(z) >= 0

forall z, w C:
    re(z) = re(w)
    img(z) = img(w)
    =>:
        z = w

forall z, w C:
    re(z + i) = re(w + i)
    img(z + i) = img(w + i)
    =>:
        z + i = w + i

forall z C:
    z = 0
    =>:
        C_abs(z) = 0

forall z C:
    C_abs(z) = 0
    =>:
        z = 0

forall z, w C:
    C_abs(z * w) = C_abs(z) * C_abs(w)
    C_abs(z + w) <= C_abs(z) + C_abs(w)
    abs(C_abs(z) - C_abs(w)) <= C_abs(z - w)

forall z C:
    z != 0
    =>:
        C_abs(z) > 0
        C_abs(z) != 0

forall z, w C:
    w != 0
    =>:
        C_abs(w) != 0
        re(z / w) = (re(z) * re(w) + img(z) * img(w)) / C_abs(w)^2
        img(z / w) = (img(z) * re(w) - re(z) * img(w)) / C_abs(w)^2

forall z, w C:
    z + w $in C
    z - w $in C
    z * w $in C
    w != 0
    =>:
        z / w $in C

forall z C, r R:
    z + r $in C
    r + z $in C
    z * r $in C
    r * z $in C
    z - r $in C
    r - z $in C

forall z C, n N:
    z ^ n $in C

forall z C, k Z:
    z != 0
    =>:
        z ^ k $in C

forall z C, m, n N:
    z ^ (m + n) = z ^ m * z ^ n
    (z ^ m) ^ n = z ^ (m * n)

forall z C, m, n Z:
    z != 0
    =>:
        z ^ (m + n) = z ^ m * z ^ n

forall z, w C, n N:
    (z * w) ^ n = z ^ n * w ^ n

forall z, w C, k Z:
    z != 0
    w != 0
    =>:
        (z * w) ^ k = z ^ k * w ^ k

sum(1, 2, fn(k Z) C {k + i}) $in C
product(1, 2, fn(k Z) C {k + i}) $in C
finite_set_sum({1, 2}, fn(k Z) C {k + i}) $in C
finite_set_product({1, 2}, fn(k Z) C {k + i}) $in C

forall n N+:
    sum(1, n, fn(k N+: k <= n) C {i}) $in C

finite_set_sum({}, fn(k Z) C {k + i}) = 0
finite_set_product({}, fn(k Z) C {k + i}) = 1

have S finite_set
finite_set_sum(S, fn(k S) C {i}) $in C
finite_set_product(S, fn(k S) C {i}) $in C

sum(1, 2, fn(k Z) Z {k}) $in Z
sum(1, 2, fn(k Z) Q {k / 2}) $in Q
sum(1, 2, fn(k Z) R {k / 2}) $in R
sum(1, 2, fn(k N) N {k}) $in N
product(1, 2, fn(k Z) Z {k}) $in Z
product(1, 2, fn(k Z) Q {k / 2}) $in Q
product(1, 2, fn(k Z) R {k / 2}) $in R
product(1, 2, fn(k N) N {k}) $in N
finite_set_sum({1, 2}, fn(k Z) Z {k}) $in Z
finite_set_sum({1, 2}, fn(k Z) Q {k / 2}) $in Q
finite_set_sum({1, 2}, fn(k Z) R {k / 2}) $in R
finite_set_sum({1, 2}, fn(k N) N {k}) $in N
finite_set_product({1, 2}, fn(k Z) Z {k}) $in Z
finite_set_product({1, 2}, fn(k Z) Q {k / 2}) $in Q
finite_set_product({1, 2}, fn(k Z) R {k / 2}) $in R
finite_set_product({1, 2}, fn(k N) N {k}) $in N
"#;

        let (run_succeeded, run_output) =
            run_complex_source(source_code, "native_complex_scalar_contract_is_checkable");

        assert!(
            run_succeeded,
            "native complex scalar contract failed:\n{}",
            run_output
        );
    });
}

#[test]
fn native_complex_congruence_composes_with_structural_beta_reduction() {
    run_with_large_stack(
        "native_complex_congruence_composes_with_structural_beta_reduction",
        || {
            let source_code = r#"
forall z, w C:
    z = w
    =>:
        re(z) = re(w)
        img(z) = img(w)
        C_abs(z) = C_abs(w)
        1 + C_abs(z) = 1 + C_abs(w)

forall z, w C:
    z = w
    =>:
        fn(x C) R {re(x)}(z) = fn(x C) R {re(w)}(z)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "native_complex_congruence_composes_with_structural_beta_reduction",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "complex constructors should use central structural congruence:\n{run_output}"
            );
            assert!(
                run_output
                    .matches("replay-safe structural equality")
                    .count()
                    >= 5,
                "complex congruence should expose structural provenance:\n{run_output}"
            );

            let mut negative_runtime = Runtime::new();
            negative_runtime.new_file_path_new_env_new_name_scope(
                "native_complex_congruence_does_not_invent_argument_equality",
            );
            let (negative_results, negative_error) = run_source_code(
                "forall z, w C:\n    C_abs(z) = C_abs(w)",
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
                "structural congruence must require argument equality:\n{negative_output}"
            );
        },
    );
}

#[test]
fn complex_expressions_do_not_acquire_real_only_properties() {
    run_with_large_stack(
        "complex_expressions_do_not_acquire_real_only_properties",
        || {
            let rejected = [
                ("complex_add_is_not_real", "i + 1 $in R"),
                ("complex_square_is_not_real", "forall z C:\n    z ^ 2 $in R"),
                ("complex_order_is_rejected", "i < 1"),
                ("real_abs_is_rejected", "abs(i) = 1"),
                ("complex_real_exponent_is_rejected", "i ^ (1 / 2) $in C"),
                ("zero_negative_power_is_rejected", "0 ^ (-1) $in C"),
                ("complex_even_power_has_no_sign", "0 <= i ^ 2"),
                ("complex_square_sum_can_cancel", "1 ^ 2 + i ^ 2 != 0"),
                (
                    "complex_aggregate_is_not_real",
                    "sum(1, 2, fn(k Z) C {k + i}) $in R",
                ),
                (
                    "finite_sum_rejects_false_integer_codomain",
                    "finite_set_sum({1, 2}, fn(k Z) Z {1 / 2}) $in Z",
                ),
                (
                    "finite_product_rejects_false_integer_codomain",
                    "finite_set_product({1, 2}, fn(k Z) Z {1 / 2}) $in Z",
                ),
                (
                    "symbolic_finite_sum_rejects_false_integer_codomain",
                    "have S finite_set\nfinite_set_sum(S, fn(k S) Z {1 / 2}) $in Z",
                ),
                (
                    "symbolic_finite_product_rejects_false_integer_codomain",
                    "have S finite_set\nfinite_set_product(S, fn(k S) Z {1 / 2}) $in Z",
                ),
                (
                    "empty_finite_sum_rejects_false_integer_codomain",
                    "finite_set_sum({}, fn(k Z) Z {i}) = 0",
                ),
                (
                    "empty_finite_product_rejects_false_integer_codomain",
                    "finite_set_product({}, fn(k Z) Z {i}) = 1",
                ),
                (
                    "symbolic_interval_must_fit_iterand_domain",
                    "forall m, n Z:\n    m <= n\n    =>:\n        sum(m, n, fn(k N) Z {k}) $in Z",
                ),
                (
                    "symbolic_interval_must_satisfy_iterand_condition",
                    "forall m, n Z:\n    m <= n\n    =>:\n        sum(m, n, fn(k Z: k = 0) Z {k}) $in Z",
                ),
            ];

            for (case_name, source_code) in rejected {
                let (run_succeeded, run_output) = run_complex_source(source_code, case_name);
                assert!(
                    !run_succeeded,
                    "{case_name} should be rejected:\n{run_output}"
                );
            }
        },
    );
}

#[test]
fn complex_extensionality_handles_composite_scalars() {
    run_with_large_stack("complex_extensionality_handles_composite_scalars", || {
        let source_code = r#"
forall z, w C:
    re(z + i) = re(w + i)
    img(z + i) = img(w + i)
    =>:
        z + i $in C
        w + i $in C
        z + i = w + i
"#;
        let (run_succeeded, run_output) = run_complex_source(
            source_code,
            "complex_extensionality_handles_composite_scalars",
        );
        assert!(
            run_succeeded,
            "composite complex objects should support coordinate extensionality:\n{run_output}"
        );
    });
}

#[test]
fn complex_extensionality_does_not_intercept_set_equality() {
    run_with_large_stack(
        "complex_extensionality_does_not_intercept_set_equality",
        || {
            let source_code = r#"
thm intersect_with_singleton:
    ? forall s set, a set:
        a $in s
        =>:
            intersect(s, {a}) = {a}
    by extension:
        ? intersect(s, {a}) = {a}
        forall z intersect(s, {a}):
            z $in s
            z $in {a}
            z = a
        forall z {a}:
            z = a
            a $in s
            z $in s
            z $in {a}
"#;
            let (run_succeeded, run_output) = run_complex_source(
                source_code,
                "complex_extensionality_does_not_intercept_set_equality",
            );
            assert!(
                run_succeeded,
                "ordinary set extensionality should remain checkable:\n{run_output}"
            );
            assert!(
                !run_output.contains("complex extensionality by re and img"),
                "ordinary set equalities must not be attributed to complex extensionality:\n{run_output}"
            );
        },
    );
}

#[test]
fn native_complex_names_are_hard_reserved_in_binding_positions() {
    run_with_large_stack(
        "native_complex_names_are_hard_reserved_in_binding_positions",
        || {
            for name in [C, I, RE, IMG, C_ABS] {
                let cases = [
                    ("declaration", format!("have {name} R")),
                    ("forall binder", format!("forall {name} R:\n    1 = 1")),
                    ("function parameter", format!("have fn f({name} R) R = 0")),
                    (
                        "indexed binder",
                        format!("have n N+ = 1\nhave tuple t for {name} <= n, t[{name}] = 0"),
                    ),
                    ("struct field", format!("struct Bad:\n    {name} R")),
                ];

                for (position, source_code) in cases {
                    let label = format!("reserved_{name}_{position}");
                    let (run_succeeded, run_output) =
                        run_complex_source(source_code.as_str(), label.as_str());
                    assert!(
                        !run_succeeded,
                        "{name} should be reserved in {position} position:\n{run_output}"
                    );
                    assert!(
                        run_output.contains(name),
                        "error should identify reserved name {name} in {position} position:\n{run_output}"
                    );
                }
            }

            let accepted = r#"
have c R = 1
have i1 R = 2
have real R = 3
have imag R = 4
have C_value R = 5
have image R = 6
have C_abs_value R = 7

c + i1 + real + imag + C_value + image + C_abs_value = 28
"#;
            let (run_succeeded, run_output) =
                run_complex_source(accepted, "longer_complex_like_names_remain_available");
            assert!(
                run_succeeded,
                "longer identifiers containing reserved spellings should work:\n{run_output}"
            );
        },
    );
}

#[test]
fn complex_latex_uses_native_notation() {
    let output = to_latex_from_source(
        "forall z C:\n    re(z) + img(z) * i = C_abs(z)",
        "complex_latex_uses_native_notation",
    )
    .expect("native complex syntax should convert to LaTeX");

    assert!(output.contains(r"\mathbb{C}"));
    assert!(output.contains(r"\operatorname{re}"));
    assert!(output.contains(r"\operatorname{img}"));
    assert!(output.contains(r"\mathrm{i}"));
    assert!(output.contains(r"\left|"));
}

#[test]
fn complex_python_and_evaluator_paths_fail_explicitly() {
    let python_error = to_python_from_source(
        "have fn f(z C) C = z + i",
        "complex_python_extractor_is_unsupported",
    )
    .expect_err("Python extraction must reject native complex definitions")
    .trace_message();
    assert!(
        python_error.contains("does not support native complex"),
        "{python_error}"
    );

    let (run_succeeded, run_output) =
        run_complex_source("eval i", "native_complex_evaluator_is_symbolic");
    assert!(
        !run_succeeded,
        "eval i should be unsupported:\n{run_output}"
    );
    assert!(
        run_output.contains("native complex values are symbolic"),
        "{run_output}"
    );
}

fn run_complex_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
