use super::*;

#[test]
fn native_real_constants_do_not_use_builtin_symbol_ids() {
    for name in [E, PI] {
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
}

#[test]
fn native_real_constant_contract_is_checkable() {
    let source_code = r#"
e $in R+
pi $in R+
e $in R
pi $in R
e $in C
pi $in C
0 < e
pi > 0
e > 1
e != 0
pi != 0
e != 1
e + pi $in R
e * pi $in R
1 / e $in R
pi ^ 2 $in R
e = e
pi = pi
"#;

    let (run_succeeded, run_output) =
        run_native_constant_source(source_code, "native_real_constant_contract_is_checkable");
    assert!(
        run_succeeded,
        "native real constant contract failed:\n{run_output}"
    );
}

#[test]
fn native_real_constants_do_not_gain_unstated_values() {
    for (label, source_code) in [
        ("e_is_not_builtin_equal_to_pi", "e = pi"),
        ("e_is_not_builtin_equal_to_two", "e = 2"),
        ("pi_is_not_builtin_equal_to_decimal", "pi = 3.14"),
        ("e_pi_are_not_builtin_distinct", "e != pi"),
    ] {
        let (run_succeeded, run_output) = run_native_constant_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} should remain unknown without an explicit fact:\n{run_output}"
        );
    }
}

#[test]
fn native_real_constant_names_are_hard_reserved_in_binding_positions() {
    for name in [E, PI] {
        let cases = [
            ("declaration", format!("have {name} R")),
            ("forall binder", format!("forall {name} R:\n    1 = 1")),
            ("function parameter", format!("have fn f({name} R) R = 0")),
            (
                "set builder binder",
                format!("have s set = {{{name} R: {name} = 0}}"),
            ),
            ("struct field", format!("struct Bad:\n    {name} R")),
        ];

        for (position, source_code) in cases {
            let label = format!("reserved_{name}_{position}");
            let (run_succeeded, run_output) =
                run_native_constant_source(source_code.as_str(), label.as_str());
            assert!(
                !run_succeeded,
                "{name} should be reserved in {position} position:\n{run_output}"
            );
            assert!(
                run_output.contains(name),
                "error should identify reserved name {name} in {position}:\n{run_output}"
            );
        }
    }

    let accepted = r#"
have e1 R = 1
have euler_e R = 2
have pi1 R = 3
have pi_value R = 4
e1 + euler_e + pi1 + pi_value = 10
"#;
    let (run_succeeded, run_output) =
        run_native_constant_source(accepted, "longer_real_constant_like_names_remain_available");
    assert!(
        run_succeeded,
        "longer identifiers containing e or pi should work:\n{run_output}"
    );
}

#[test]
fn native_real_constants_have_backend_specific_output() {
    let latex = to_latex_from_source("e = e\npi = pi", "native_real_constants_have_latex_output")
        .expect("native real constants should convert to LaTeX");
    assert!(latex.contains(r"\mathrm{e}"), "{latex}");
    assert!(latex.contains(r"\pi"), "{latex}");

    let python = to_python_from_source(
        "have e_copy R = e\nhave pi_copy R = pi",
        "native_real_constants_have_python_output",
    )
    .expect("native real constants should convert to Python");
    assert_eq!(python.matches("import math").count(), 1, "{python}");
    assert!(python.contains("e_copy = math.e"), "{python}");
    assert!(python.contains("pi_copy = math.pi"), "{python}");
}

#[test]
fn native_real_constants_remain_symbolic_in_evaluator() {
    for (label, source_code) in [
        ("eval_e_is_symbolic", "eval e"),
        ("eval_nested_pi_is_symbolic", "eval 1 + pi"),
        (
            "eval_resolved_e_is_symbolic",
            "have e_copy R = e\n\neval e_copy",
        ),
    ] {
        let (run_succeeded, run_output) = run_native_constant_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} should be rejected by evaluator:\n{run_output}"
        );
        assert!(
            run_output.contains("native transcendental symbols are symbolic"),
            "{run_output}"
        );
    }
}

fn run_native_constant_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
