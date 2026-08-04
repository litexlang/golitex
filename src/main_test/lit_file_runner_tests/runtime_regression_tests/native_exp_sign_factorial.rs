use super::*;

#[test]
fn native_exp_sign_factorial_names_ids_and_kinds_are_stable() {
    for name in [EXP, LN, SIGN, FACTORIAL] {
        assert!(is_keyword(name));
        assert!(is_builtin_identifier_name(name));
        assert!(builtin_symbol_ref(name).is_some());
    }
    for (name, offset) in [(EXP, 55), (LN, 56), (SIGN, 57), (FACTORIAL, 58)] {
        assert_eq!(
            builtin_symbol_ref(name)
                .expect("builtin symbol")
                .id()
                .value(),
            (1_u64 << 62) + offset
        );
    }
    let exp: Obj = Exp::new(Number::new("1".to_string()).into()).into();
    let ln: Obj = Ln::new(Number::new("1".to_string()).into()).into();
    let sign: Obj = Sign::new(Number::new("1".to_string()).into()).into();
    let factorial: Obj = Factorial::new(Number::new("1".to_string()).into()).into();
    assert_eq!(exp.kind(), ObjKind::Exp);
    assert_eq!(exp.kind().as_u8(), 86);
    assert_eq!(ln.kind(), ObjKind::Ln);
    assert_eq!(ln.kind().as_u8(), 87);
    assert_eq!(sign.kind(), ObjKind::Sign);
    assert_eq!(sign.kind().as_u8(), 88);
    assert_eq!(factorial.kind(), ObjKind::Factorial);
    assert_eq!(factorial.kind().as_u8(), 89);
}

#[test]
fn native_exp_sign_factorial_compute_and_eval() {
    assert_source_succeeds(
        r#"
exp(0) = 1
ln(1) = 0
sign(-9) = -1
sign(0) = 0
sign(2.5) = 1
factorial(0) = 1
factorial(10) = 3628800
eval exp(0)
eval ln(1)
eval sign(-4.25)
eval factorial(8)
"#,
        "native_exp_sign_factorial_compute_and_eval",
    );
}

#[test]
fn native_exp_sign_factorial_symbolic_contracts_are_available() {
    assert_source_succeeds(
        r#"
forall x R:
    exp(x) $in R+
    exp(x) > 0
    exp(x) = e^x
    ln(exp(x)) = x
    sign(x) $in Z
    -1 <= sign(x)
    sign(x) <= 1
    sign(x) * abs(x) = x

forall x R:
    x > 0
    =>:
        ln(x) $in R
        exp(ln(x)) = x
        ln(x) = log(e, x)

forall a, b R:
    exp(a + b) = exp(a) * exp(b)
    exp(a - b) = exp(a) / exp(b)

forall a, b R:
    a > 0
    b > 0
    =>:
        ln(a * b) = ln(a) + ln(b)

forall x R:
    x > 1
    =>:
        ln(x) > 0

forall x R:
    x > 0
    x < 1
    =>:
        ln(x) < 0

forall n N:
    factorial(n) $in N+
    factorial(n) >= 1
    factorial(n + 1) = (n + 1) * factorial(n)

forall n N:
    n > 0
    =>:
        factorial(n) = n * factorial(n - 1)

forall x R:
    x > 0
    =>:
        sign(x) = 1

forall x R:
    x = 0
    =>:
        sign(x) = 0

forall x R:
    x < 0
    =>:
        sign(x) = -1
"#,
        "native_exp_sign_factorial_symbolic_contracts_are_available",
    );
}

#[test]
fn native_exp_ln_order_is_preserved() {
    assert_source_succeeds(
        r#"
forall a, b R:
    a < b
    =>:
        exp(a) < exp(b)

forall a, b R:
    a <= b
    =>:
        exp(a) <= exp(b)

forall a, b R:
    a > b
    =>:
        exp(a) > exp(b)

forall a, b R:
    a >= b
    =>:
        exp(a) >= exp(b)

forall a, b R+:
    a < b
    =>:
        ln(a) < ln(b)

forall a, b R+:
    a <= b
    =>:
        ln(a) <= ln(b)

forall a, b R+:
    a > b
    =>:
        ln(a) > ln(b)

forall a, b R+:
    a >= b
    =>:
        ln(a) >= ln(b)
"#,
        "native_exp_ln_order_is_preserved",
    );

    for (label, source) in [
        (
            "exp_weak_does_not_imply_strict",
            r#"
forall a, b R:
    a <= b
    =>:
        exp(a) < exp(b)
"#,
        ),
        (
            "ln_weak_does_not_imply_strict",
            r#"
forall a, b R+:
    a <= b
    =>:
        ln(a) < ln(b)
"#,
        ),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_exp_sign_factorial_reject_invalid_domains_and_arities() {
    for (label, source) in [
        ("exp_set", "exp({1}) = 1"),
        ("ln_zero", "ln(0) = 0"),
        ("sign_complex", "sign(i) = 1"),
        ("factorial_negative", "factorial(-1) = 1"),
        ("factorial_fraction", "factorial(1.5) = 1"),
        ("exp_arity", "exp(1, 2) = 1"),
        ("factorial_arity", "factorial() = 1"),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_exp_sign_factorial_names_are_hard_reserved() {
    for name in [EXP, LN, SIGN, FACTORIAL] {
        assert_source_fails(&format!("have {name} R = 1"), &format!("reserved_{name}"));
    }
}

#[test]
fn native_exp_sign_factorial_latex_uses_standard_notation() {
    let latex = to_latex_from_source(
        "exp(0) = 1\nln(1) = 0\nsign(-2) = -1\nfactorial(5) = 120",
        "native_exp_sign_factorial_latex_uses_standard_notation",
    )
    .expect("native functions should convert to LaTeX");
    assert!(latex.contains(r"\exp\left( 0 \right)"), "{latex}");
    assert!(latex.contains(r"\ln\left( 1 \right)"), "{latex}");
    assert!(
        latex.contains(r"\operatorname{sgn}\left( -1 \cdot 2 \right)"),
        "{latex}"
    );
    assert!(latex.contains(r"\left( 5 \right)!"), "{latex}");
}

#[test]
fn native_exp_sign_factorial_python_and_lean_outputs_are_explicit() {
    let python = to_python_from_source(
        r#"
have fn second_batch(x R) R = exp(x) + ln(exp(x)) + sign(x)
have algo for second_batch(x):
    exp(x) + ln(exp(x)) + sign(x)

have factorial_value N = factorial(6)
"#,
        "native_exp_sign_factorial_python_output",
    )
    .expect("native functions should convert to Python");
    assert!(python.contains("math.exp(x)"), "{python}");
    assert!(python.contains("math.log(math.exp(x))"), "{python}");
    assert!(python.contains("(1 if x > 0 else"), "{python}");
    assert!(python.contains("math.factorial(int(6.0))"), "{python}");

    let lean = crate::to_lean::to_lean_from_source(
        "exp(0) = 1\nln(1) = 0\nsign(-2) = -1\nfactorial(5) = 120",
        "native_exp_sign_factorial_lean_output",
    )
    .expect("native functions should convert to Lean");
    assert!(lean.contains("Real.exp"), "{lean}");
    assert!(lean.contains("Real.log"), "{lean}");
    assert!(lean.contains("if "), "{lean}");
    assert!(lean.contains("Nat.factorial"), "{lean}");
}

fn assert_source_succeeds(source: &str, label: &str) {
    let (succeeded, output) = run_source(source, label);
    assert!(succeeded, "{label} failed:\n{output}");
}

fn assert_source_fails(source: &str, label: &str) {
    let (succeeded, output) = run_source(source, label);
    assert!(!succeeded, "{label} unexpectedly succeeded:\n{output}");
}

fn run_source(source: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (results, error) = run_source_code(source, &mut runtime);
    render_run_source_code_output(&runtime, &results, &error, false)
}
