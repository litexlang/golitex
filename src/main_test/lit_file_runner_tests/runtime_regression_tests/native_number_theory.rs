use super::*;

#[test]
fn native_number_theory_names_and_ids_are_stable() {
    assert!(is_keyword(GCD));
    assert!(is_keyword(PRIME));
    assert!(is_builtin_identifier_name(GCD));
    assert!(is_builtin_predicate(PRIME));
    assert_eq!(
        builtin_symbol_ref(GCD)
            .expect("gcd builtin symbol")
            .id()
            .value(),
        (1_u64 << 62) + 48
    );
    assert_eq!(
        builtin_symbol_ref(PRIME)
            .expect("prime builtin symbol")
            .id()
            .value(),
        (1_u64 << 62) + 49
    );
    let gcd: Obj = Gcd::new(
        Number::new("6".to_string()).into(),
        Number::new("4".to_string()).into(),
    )
    .into();
    assert_eq!(gcd.kind(), ObjKind::Gcd);
    assert_eq!(gcd.kind().as_u8(), 80);
}

#[test]
fn native_gcd_computes_without_eval_and_supports_eval() {
    assert_source_succeeds(
        r#"
gcd(54, -24) = 6
gcd(0, -24) = 24
gcd(54, -24) + gcd(10, 15) = 11
gcd(1234567890123456789012345678900, 2469135780246913578024691357800) = 1234567890123456789012345678900
eval gcd(54, -24)
"#,
        "native_gcd_computes_without_eval_and_supports_eval",
    );
}

#[test]
fn native_gcd_symbolic_contract_is_available() {
    assert_source_succeeds(
        r#"
forall a, b Z:
    a != 0 or b != 0
    =>:
        gcd(a, b) $in N_pos

forall a, b Z:
    a != 0 or b != 0
    =>:
        a % gcd(a, b) = 0
        b % gcd(a, b) = 0

forall a, b Z, d N_pos:
    a != 0 or b != 0
    a % d = 0
    b % d = 0
    =>:
        d <= gcd(a, b)
"#,
        "native_gcd_symbolic_contract_is_available",
    );
}

#[test]
fn native_gcd_rejects_all_zero_and_missing_domain_evidence() {
    for (label, source) in [
        ("gcd_all_zero", "gcd(0, 0) = 0"),
        (
            "gcd_symbolic_without_nonzero",
            "forall a, b Z:\n    gcd(a, b) $in N_pos",
        ),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_prime_computation_definition_and_boundary_are_exact() {
    assert_source_succeeds(
        r#"
$prime(2)
$prime(97)
not $prime(1)
not $prime(4)
not $prime(341)
not $prime(561)
$prime(18446744073709551557)
not $prime(18446744073709551615)
by def $prime(97)

claim:
    ? forall p N_pos:
        2 <= p
        forall d range(2, p):
            p % d != 0
        =>:
            $prime(p)
    by def $prime(p)

forall p N_pos:
    $prime(p)
    =>:
        2 <= p
"#,
        "native_prime_computation_definition_and_boundary_are_exact",
    );
}

#[test]
fn native_prime_rejects_zero_and_does_not_guess_beyond_u64() {
    assert_source_fails("$prime(0)", "native_prime_rejects_zero");
    assert_source_fails(
        "$prime(18446744073709551616)",
        "native_prime_does_not_guess_large_positive",
    );
    assert_source_fails(
        "not $prime(18446744073709551616)",
        "native_prime_does_not_guess_large_negative",
    );
}

#[test]
fn native_number_theory_names_are_hard_reserved_but_uppercase_prime_is_available() {
    for name in [GCD, PRIME] {
        for (position, source) in [
            ("declaration", format!("have {name} Z = 1")),
            ("forall binder", format!("forall {name} Z:\n    1 = 1")),
            ("function parameter", format!("have fn f({name} Z) Z = 0")),
            (
                "set builder binder",
                format!("have s set = {{{name} Z: {name} = 0}}"),
            ),
            ("struct field", format!("struct Bad:\n    {name} Z")),
        ] {
            assert_source_fails(&source, &format!("reserved_{name}_{position}"));
        }
    }
    assert_source_succeeds(
        "have Prime Z = 1\nPrime = 1",
        "uppercase_prime_remains_available",
    );
}

#[test]
fn native_number_theory_latex_is_mathematical() {
    let latex = to_latex_from_source(
        "gcd(54, 24) = 6\n$prime(97)",
        "native_number_theory_latex_is_mathematical",
    )
    .expect("native number theory should convert to LaTeX");
    assert!(latex.contains(r"\gcd\left( 54, 24 \right)"), "{latex}");
    assert!(latex.contains(r"\operatorname{prime}"), "{latex}");
}

#[test]
fn native_number_theory_python_boundary_is_structural() {
    let ordinary_function = to_python_from_source(
        r#"
have fn euclidean_gcd(x R) R = x

forall x R:
    euclidean_gcd(x) = x
"#,
        "native_number_theory_python_boundary_is_structural",
    )
    .expect("an ordinary function whose name ends in gcd should remain extractable");
    assert!(
        ordinary_function.contains("No Python-extractable Litex definitions"),
        "{ordinary_function}"
    );

    let gcd_error = to_python_from_source(
        "gcd(54, 24) = 6",
        "native_gcd_python_boundary_is_structural",
    )
    .expect_err("the native gcd object is not supported by the Python extractor")
    .trace_message();
    assert!(
        gcd_error.contains("does not support native gcd"),
        "{gcd_error}"
    );

    let prime_error =
        to_python_from_source("$prime(97)", "native_prime_python_boundary_is_structural")
            .expect_err("the builtin prime predicate is not supported by the Python extractor")
            .trace_message();
    assert!(
        prime_error.contains("does not support builtin prime"),
        "{prime_error}"
    );
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
