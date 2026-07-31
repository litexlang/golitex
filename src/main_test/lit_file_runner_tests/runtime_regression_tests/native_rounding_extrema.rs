use super::*;

#[test]
fn native_rounding_extrema_names_ids_and_kinds_are_stable() {
    for name in [LCM, FLOOR, CEIL, MIN, MAX] {
        assert!(is_keyword(name));
        assert!(is_builtin_identifier_name(name));
        assert!(builtin_symbol_ref(name).is_some());
    }
    for (name, offset) in [(LCM, 50), (FLOOR, 51), (CEIL, 52), (MIN, 53), (MAX, 54)] {
        assert_eq!(
            builtin_symbol_ref(name)
                .expect("builtin symbol")
                .id()
                .value(),
            (1_u64 << 62) + offset
        );
    }
    let floor: Obj = Floor::new(Number::new("1.5".to_string()).into()).into();
    let ceil: Obj = Ceil::new(Number::new("1.5".to_string()).into()).into();
    let min: Obj = Min::new(
        Number::new("1".to_string()).into(),
        Number::new("2".to_string()).into(),
    )
    .into();
    let max: Obj = Max::new(
        Number::new("1".to_string()).into(),
        Number::new("2".to_string()).into(),
    )
    .into();
    let lcm: Obj = Lcm::new(
        Number::new("6".to_string()).into(),
        Number::new("4".to_string()).into(),
    )
    .into();
    assert_eq!(floor.kind(), ObjKind::Floor);
    assert_eq!(floor.kind().as_u8(), 82);
    assert_eq!(ceil.kind(), ObjKind::Ceil);
    assert_eq!(ceil.kind().as_u8(), 83);
    assert_eq!(min.kind(), ObjKind::Min);
    assert_eq!(min.kind().as_u8(), 84);
    assert_eq!(max.kind(), ObjKind::Max);
    assert_eq!(max.kind().as_u8(), 85);
    assert_eq!(lcm.kind(), ObjKind::Lcm);
    assert_eq!(lcm.kind().as_u8(), 81);
}

#[test]
fn native_rounding_extrema_compute_and_eval() {
    assert_source_succeeds(
        r#"
floor(3.75) = 3
floor(-3.75) = -4
ceil(3.25) = 4
ceil(-3.25) = -3
min(7, -2) = -2
max(7, -2) = 7
lcm(12, -18) = 36
lcm(0, 0) = 0
have fn apply_integer_map(f fn(t R) Z, x R) Z = f(x)
apply_integer_map(fn(y R) Z {floor(y)}, 3.75) = 3
eval floor(-8.125)
eval ceil(8.125)
eval min(4, -9)
eval max(4, -9)
eval lcm(21, 6)
"#,
        "native_rounding_extrema_compute_and_eval",
    );
}

#[test]
fn native_rounding_extrema_symbolic_contracts_are_available() {
    assert_source_succeeds(
        r#"
forall x R:
    floor(x) $in Z
    ceil(x) $in Z
    floor(x) <= x
    x < floor(x) + 1
    ceil(x) - 1 < x
    x <= ceil(x)

forall n Z:
    floor(n) = n
    ceil(n) = n

forall a, b R:
    min(a, b) <= a
    min(a, b) <= b
    a <= max(a, b)
    b <= max(a, b)

forall a, b R:
    a <= b
    =>:
        min(a, b) = a
        max(a, b) = b

forall a, b Z:
    lcm(a, b) $in N

forall a, b Z:
    a != 0 or b != 0
    =>:
        lcm(a, b) * gcd(a, b) = abs(a * b)
"#,
        "native_rounding_extrema_symbolic_contracts_are_available",
    );
}

#[test]
fn native_rounding_extrema_reject_invalid_domains_and_arities() {
    for (label, source) in [
        ("floor_set", "floor({1}) = 1"),
        ("min_set", "min({1}, {2}) = {1}"),
        ("lcm_real", "lcm(1.5, 3) = 3"),
        ("floor_arity", "floor(1, 2) = 1"),
        ("max_arity", "max(1) = 1"),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_rounding_extrema_names_are_hard_reserved() {
    for name in [LCM, FLOOR, CEIL, MIN, MAX] {
        assert_source_fails(&format!("have {name} Z = 1"), &format!("reserved_{name}"));
    }
}

#[test]
fn native_rounding_extrema_latex_uses_standard_notation() {
    let latex = to_latex_from_source(
        "floor(3.5) = 3\nceil(3.5) = 4\nmin(2, 3) = 2\nmax(2, 3) = 3\nlcm(6, 4) = 12",
        "native_rounding_extrema_latex_uses_standard_notation",
    )
    .expect("native rounding/extrema should convert to LaTeX");
    assert!(latex.contains(r"\left\lfloor 3.5 \right\rfloor"), "{latex}");
    assert!(latex.contains(r"\left\lceil 3.5 \right\rceil"), "{latex}");
    assert!(latex.contains(r"\min\left( 2, 3 \right)"), "{latex}");
    assert!(latex.contains(r"\max\left( 2, 3 \right)"), "{latex}");
    assert!(
        latex.contains(r"\operatorname{lcm}\left( 6, 4 \right)"),
        "{latex}"
    );
}

#[test]
fn native_rounding_extrema_python_and_lean_outputs_are_explicit() {
    let python = to_python_from_source(
        r#"
have fn round_total(x R) R = floor(x) + ceil(x) + min(x, 0) + max(x, 0)
have algo for round_total(x):
    floor(x) + ceil(x) + min(x, 0) + max(x, 0)

have common_multiple N = lcm(6, 4)
"#,
        "native_rounding_extrema_python_output",
    )
    .expect("native rounding/extrema should convert to Python");
    assert!(python.contains("math.floor(x)"), "{python}");
    assert!(python.contains("math.ceil(x)"), "{python}");
    assert!(python.contains("min(x, 0.0)"), "{python}");
    assert!(python.contains("max(x, 0.0)"), "{python}");
    assert!(python.contains("math.lcm(int(6.0), int(4.0))"), "{python}");

    let lean = crate::to_lean::to_lean_from_source(
        "floor(3.5) = 3\nceil(3.5) = 4\nmin(2, 3) = 2\nmax(2, 3) = 3\nlcm(6, 4) = 12",
        "native_rounding_extrema_lean_output",
    )
    .expect("native rounding/extrema should convert to Lean");
    assert!(lean.contains("Int.floor"), "{lean}");
    assert!(lean.contains("Int.ceil"), "{lean}");
    assert!(lean.contains("(min "), "{lean}");
    assert!(lean.contains("(max "), "{lean}");
    assert!(lean.contains("Nat.lcm"), "{lean}");
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
