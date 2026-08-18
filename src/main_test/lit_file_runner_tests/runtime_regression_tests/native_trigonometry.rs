use super::*;

#[test]
fn native_trigonometric_objects_have_reserved_syntax_and_stable_kinds() {
    for name in [SIN, COS, TAN, COT] {
        assert!(is_keyword(name), "{name} should be hard reserved");
        assert!(
            !is_builtin_identifier_name(name),
            "{name} should not use the builtin Identifier path"
        );
        assert!(
            builtin_symbol_ref(name).is_none(),
            "{name} should not allocate a builtin SymbolId"
        );
    }

    let zero: Obj = Number::new("0".to_string()).into();
    assert_eq!(Obj::from(Sin::new(zero.clone())).kind_id(), 76);
    assert_eq!(Obj::from(Cos::new(zero.clone())).kind_id(), 77);
    assert_eq!(Obj::from(Tan::new(zero.clone())).kind_id(), 78);
    assert_eq!(Obj::from(Cot::new(zero)).kind_id(), 79);
}

#[test]
fn native_trigonometric_core_and_derived_contract_is_checkable() {
    run_with_large_stack(
        "native_trigonometric_core_and_derived_contract_is_checkable",
        || {
            let source_code = r#"
sin(0) = 0
cos(0) = 1
sin(pi / 2) = 1
cos(pi / 2) = 0
sin(pi) = 0
cos(pi) = -1
sin(2 * pi) = 0
cos(2 * pi) = 1
tan(0) = 0
cot(pi / 2) = 0

forall x R:
    sin(x) $in R
    cos(x) $in R
    sin(x) $in C
    cos(x) $in C
    sin(x) ^ 2 + cos(x) ^ 2 = 1
    sin(-x) = -sin(x)
    cos(-x) = cos(x)
    sin(2 * x) = 2 * sin(x) * cos(x)
    cos(2 * x) = cos(x) ^ 2 - sin(x) ^ 2
    cos(2 * x) = 1 - 2 * sin(x) ^ 2
    sin(x + 2 * pi) = sin(x)
    cos(x + 2 * pi) = cos(x)
    sin(x + pi) = -sin(x)
    cos(x + pi) = -cos(x)
    sin(pi / 2 - x) = cos(x)
    cos(pi / 2 - x) = sin(x)
    -1 <= sin(x) <= 1
    -1 <= cos(x) <= 1
    abs(sin(x)) <= 1
    abs(cos(x)) <= 1

forall x, y R:
    sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)
    cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)
    sin(x - y) = sin(x) * cos(y) - cos(x) * sin(y)
    cos(x - y) = cos(x) * cos(y) + sin(x) * sin(y)

forall x, y R:
    x = y
    =>:
        sin(x) = sin(y)
        cos(x) = cos(y)

forall x, y R:
    x = y
    cos(x) != 0
    cos(y) != 0
    =>:
        tan(x) = tan(y)

forall x, y R:
    x = y
    sin(x) != 0
    sin(y) != 0
    =>:
        cot(x) = cot(y)

forall x R:
    cos(x) != 0
    =>:
        tan(x) $in R
        tan(x) $in C
        tan(x) = sin(x) / cos(x)
        tan(-x) = -tan(x)
        cos(x + pi) != 0
        tan(x + pi) = tan(x)

forall x R:
    sin(x) != 0
    =>:
        cot(x) $in R
        cot(x) $in C
        cot(x) = cos(x) / sin(x)
        cot(-x) = -cot(x)
        sin(x + pi) != 0
        cot(x + pi) = cot(x)

forall x R:
    cos(x) != 0
    sin(x) != 0
    =>:
        tan(x) * cot(x) = 1
        tan(x) = 1 / cot(x)
        cot(x) = 1 / tan(x)
        1 + tan(x) ^ 2 = 1 / cos(x) ^ 2
        1 + cot(x) ^ 2 = 1 / sin(x) ^ 2
"#;

            let (run_succeeded, run_output) =
                run_trigonometric_source(source_code, "native_trigonometric_contract");
            assert!(
                run_succeeded,
                "native trigonometric contract failed:\n{run_output}"
            );
        },
    );
}

#[test]
fn native_tan_and_cot_nonzero_require_nonzero_sine_and_cosine() {
    let positive_source = r#"
forall x R:
    sin(x) != 0
    cos(x) != 0
    =>:
        tan(x) != 0
        cot(x) != 0
"#;
    let (run_succeeded, run_output) =
        run_trigonometric_source(positive_source, "native_tan_cot_nonzero");
    assert!(
        run_succeeded,
        "nonzero sine and cosine should prove nonzero tangent and cotangent:\n{run_output}"
    );
    assert!(run_output.contains("non-zero transfer through canonical expansion"));

    for (label, source_code) in [
        (
            "tan_nonzero_without_nonzero_sine",
            "forall x R:\n    cos(x) != 0\n    =>:\n        tan(x) != 0",
        ),
        (
            "cot_nonzero_without_nonzero_cosine",
            "forall x R:\n    sin(x) != 0\n    =>:\n        cot(x) != 0",
        ),
    ] {
        let (run_succeeded, run_output) = run_trigonometric_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} must not prove a nonzero quotient without a nonzero numerator:\n{run_output}"
        );
    }
}

#[test]
fn native_tan_and_cot_require_their_denominators() {
    for (label, source_code, expected) in [
        (
            "tan_undefined_at_half_pi",
            "tan(pi / 2) = 0",
            "requires cos(pi / 2) != 0",
        ),
        (
            "cot_undefined_at_zero",
            "cot(0) = 0",
            "requires sin(0) != 0",
        ),
        (
            "generic_tan_needs_a_guard",
            "forall x R:\n    tan(x) = tan(x)",
            "requires cos(x) != 0",
        ),
    ] {
        let (run_succeeded, run_output) = run_trigonometric_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} should fail well-definedness:\n{run_output}"
        );
        assert!(run_output.contains(expected), "{run_output}");
    }
}

#[test]
fn native_trigonometric_interval_order_connections_are_available() {
    let source_code = r#"
3 < pi < 4

forall x R:
    x > 0
    x < pi
    =>:
        sin(x) > 0

forall x R:
    x > -pi / 2
    x < pi / 2
    =>:
        cos(x) > 0

forall a, b R:
    a >= -pi / 2
    b <= pi / 2
    a < b
    =>:
        sin(a) < sin(b)

forall a, b R:
    a >= 0
    b <= pi
    a <= b
    =>:
        cos(a) >= cos(b)

forall x R:
    x > 0
    x < pi / 2
    =>:
        tan(x) > 0
        cot(x) > 0

forall a, b R:
    a > -pi / 2
    a < pi / 2
    b > -pi / 2
    b < pi / 2
    a < b
    =>:
        tan(a) < tan(b)

forall a, b R:
    a > 0
    a < pi
    b > 0
    b < pi
    a <= b
    =>:
        cot(a) >= cot(b)
"#;
    let (run_succeeded, run_output) =
        run_trigonometric_source(source_code, "native_trigonometric_interval_order");
    assert!(run_succeeded, "interval order rules failed:\n{run_output}");

    let (run_succeeded, run_output) = run_trigonometric_source(
        "forall a, b R:\n    a < b\n    =>:\n        sin(a) < sin(b)",
        "sine_is_not_globally_monotone",
    );
    assert!(
        !run_succeeded,
        "global sine monotonicity must fail:\n{run_output}"
    );

    let (run_succeeded, run_output) = run_trigonometric_source(
        "forall a, b R:\n    cos(a) != 0\n    cos(b) != 0\n    a < b\n    =>:\n        tan(a) < tan(b)",
        "tangent_is_not_globally_monotone",
    );
    assert!(
        !run_succeeded,
        "global tangent monotonicity must fail:\n{run_output}"
    );
}

#[test]
fn native_trigonometry_rejects_nonreal_arguments() {
    for (label, source_code) in [("sin_of_i", "sin(i) = 0"), ("cos_of_i", "cos(i) = 0")] {
        let (run_succeeded, run_output) = run_trigonometric_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} should fail real-domain well-definedness:\n{run_output}"
        );
        assert!(run_output.contains("not in r"), "{run_output}");
    }
}

#[test]
fn native_tan_and_cot_derived_angle_formulas_are_checkable() {
    let source_code = r#"
forall x, y R:
    cos(x) != 0
    cos(y) != 0
    cos(x + y) != 0
    1 - tan(x) * tan(y) != 0
    =>:
        tan(x + y) = (tan(x) + tan(y)) / (1 - tan(x) * tan(y))

forall x, y R:
    cos(x) != 0
    cos(y) != 0
    cos(x - y) != 0
    1 + tan(x) * tan(y) != 0
    =>:
        tan(x - y) = (tan(x) - tan(y)) / (1 + tan(x) * tan(y))

forall x R:
    cos(x) != 0
    cos(2 * x) != 0
    1 - tan(x)^2 != 0
    =>:
        tan(2 * x) = 2 * tan(x) / (1 - tan(x)^2)

forall x, y R:
    sin(x) != 0
    sin(y) != 0
    sin(x + y) != 0
    cot(x) + cot(y) != 0
    =>:
        cot(x + y) = (cot(x) * cot(y) - 1) / (cot(x) + cot(y))

forall x, y R:
    sin(x) != 0
    sin(y) != 0
    sin(x - y) != 0
    cot(y) - cot(x) != 0
    =>:
        cot(x - y) = (cot(x) * cot(y) + 1) / (cot(y) - cot(x))

forall x R:
    sin(x) != 0
    cos(x) != 0
    sin(2 * x) != 0
    =>:
        cot(2 * x) = (cot(x)^2 - 1) / (2 * cot(x))
"#;

    let (run_succeeded, run_output) =
        run_trigonometric_source(source_code, "native_tan_cot_angle_formulas");
    assert!(
        run_succeeded,
        "derived tan/cot angle formulas failed:\n{run_output}"
    );
}

#[test]
fn native_trigonometry_does_not_gain_unstated_special_values() {
    for (label, source_code) in [
        ("sin_pi_over_six", "sin(pi / 6) = 1 / 2"),
        ("cos_pi_over_three", "cos(pi / 3) = 1 / 2"),
        (
            "sin_is_not_globally_injective",
            "forall x, y R:\n    sin(x) = sin(y)",
        ),
    ] {
        let (run_succeeded, run_output) = run_trigonometric_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} should remain unknown without an explicit fact:\n{run_output}"
        );
    }
}

#[test]
fn native_trigonometric_names_are_hard_reserved_in_binding_positions() {
    for name in [SIN, COS, TAN, COT] {
        let source_code = format!("have {name} R");
        let (run_succeeded, run_output) =
            run_trigonometric_source(source_code.as_str(), "reserved_trig_name");
        assert!(
            !run_succeeded,
            "{name} should be reserved in declarations:\n{run_output}"
        );
        assert!(run_output.contains(name), "{run_output}");
    }

    let accepted = r#"
have sine_value R = 1
have cosine_value R = 2
have tangent_value R = 3
have cotangent_value R = 4
sine_value + cosine_value + tangent_value + cotangent_value = 10
"#;
    let (run_succeeded, run_output) =
        run_trigonometric_source(accepted, "longer_trig_like_names_remain_available");
    assert!(
        run_succeeded,
        "longer identifiers containing trig spellings should work:\n{run_output}"
    );
}

#[test]
fn native_trigonometry_has_explicit_backend_boundaries() {
    let latex = to_latex_from_source("sin(pi / 2) = 1\ncos(pi) = -1", "native_trigonometry_latex")
        .expect("native trigonometry should convert to LaTeX");
    assert!(latex.contains(r"\sin"), "{latex}");
    assert!(latex.contains(r"\cos"), "{latex}");
    assert!(latex.contains(r"\pi"), "{latex}");

    let python_error = to_python_from_source(
        "have y R = sin(0)",
        "native_trigonometry_python_is_symbolic",
    )
    .expect_err("Python extraction must reject native trigonometric expressions")
    .trace_message();
    assert!(
        python_error.contains("does not support native trigonometric"),
        "{python_error}"
    );

    let (run_succeeded, run_output) =
        run_trigonometric_source("eval sin(0)", "native_trigonometry_eval_is_symbolic");
    assert!(
        !run_succeeded,
        "eval sin(0) should be unsupported:\n{run_output}"
    );
    assert!(
        run_output.contains("native transcendental symbols are symbolic"),
        "{run_output}"
    );
}

fn run_trigonometric_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
