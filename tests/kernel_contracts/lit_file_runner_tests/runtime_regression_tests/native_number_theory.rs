use super::*;

#[test]
fn native_number_theory_names_and_ids_are_stable() {
    assert!(is_keyword(GCD));
    assert!(is_keyword(QUOT));
    assert!(is_keyword(PRIME));
    assert!(is_keyword(COPRIME));
    assert!(is_keyword(DVD));
    assert!(is_builtin_identifier_name(GCD));
    assert!(is_builtin_identifier_name(QUOT));
    assert!(is_builtin_predicate(PRIME));
    assert!(is_builtin_predicate(COPRIME));
    assert!(is_builtin_predicate(DVD));
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
    assert_eq!(
        builtin_symbol_ref(COPRIME)
            .expect("coprime builtin symbol")
            .id()
            .value(),
        (1_u64 << 62) + 60
    );
    assert_eq!(
        builtin_symbol_ref(DVD)
            .expect("dvd builtin symbol")
            .id()
            .value(),
        (1_u64 << 62) + 61
    );
    assert_eq!(
        builtin_symbol_ref(QUOT)
            .expect("quot builtin symbol")
            .id()
            .value(),
        (1_u64 << 62) + 62
    );
    let gcd: Obj = Gcd::new(
        Number::new("6".to_string()).into(),
        Number::new("4".to_string()).into(),
    )
    .into();
    assert_eq!(gcd.kind(), ObjKind::Gcd);
    assert_eq!(gcd.kind().as_u8(), 80);
    let quot: Obj = Quot::new(
        Number::new("-7".to_string()).into(),
        Number::new("3".to_string()).into(),
    )
    .into();
    assert_eq!(quot.kind(), ObjKind::Quot);
    assert_eq!(quot.kind().as_u8(), 92);
}

#[test]
fn native_quot_computes_and_exposes_the_euclidean_contract() {
    assert_source_succeeds(
        r#"
quot(7, 3) = 2
quot(-7, 3) = -3
quot(-6, 3) = -2
quot(1234567890123456789012345678900, 10) = 123456789012345678901234567890
eval quot(-7, 3)

forall a Z, d N+:
    quot(a, d) $in Z
    a = d * quot(a, d) + a % d
"#,
        "native_quot_computes_and_exposes_the_euclidean_contract",
    );
}

#[test]
fn native_quot_rejects_wrong_arity_and_arguments_outside_z_times_n_pos() {
    for (label, source) in [
        ("native_quot_wrong_arity", "quot(7) = 7"),
        ("native_quot_zero_divisor", "quot(7, 0) = 0"),
        ("native_quot_negative_divisor", "quot(7, -3) = -2"),
        ("native_quot_noninteger_dividend", "quot(7.5, 3) = 2"),
        (
            "native_quot_symbolic_nonpositive_domain",
            "forall a Z, d Z*:\n    quot(a, d) $in Z",
        ),
    ] {
        assert_source_fails(source, label);
    }
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
        gcd(a, b) $in N+

forall a, b Z:
    a != 0 or b != 0
    =>:
        a % gcd(a, b) = 0
        b % gcd(a, b) = 0

forall a, b Z, d N+:
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
            "forall a, b Z:\n    gcd(a, b) $in N+",
        ),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_prime_computation_definition_and_boundary_are_exact() {
    assert_source_succeeds(
        r#"
not $prime(0)
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
    ? forall p N+:
        2 <= p
        forall d range(2, p):
            p % d != 0
        =>:
            $prime(p)
    by def $prime(p)

forall p N:
    $prime(p)
    =>:
        2 <= p
"#,
        "native_prime_computation_definition_and_boundary_are_exact",
    );
}

#[test]
fn native_prime_rejects_non_natural_carriers_and_does_not_guess_beyond_u64() {
    assert_source_fails("$prime(0)", "native_prime_zero_is_false");
    assert_source_fails("$prime(1)", "native_prime_one_is_false");
    assert_source_fails(
        "forall z Z:\n    $prime(z)\n    =>:\n        z = z",
        "native_prime_rejects_arbitrary_integer",
    );
    assert_source_fails(
        "forall x R:\n    not $prime(x)\n    =>:\n        x = x",
        "native_prime_rejects_arbitrary_real",
    );
    assert_source_fails("$prime(-2)", "native_prime_rejects_negative_integer");
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
fn native_coprime_computation_definition_and_zero_boundary_are_exact() {
    assert_source_succeeds(
        r#"
$coprime(14, 25)
$coprime(0, 1)
$coprime(1, 0)
not $coprime(14, 21)
not $coprime(0, 0)
$coprime(1234567890123456789012345678901, 10)
by def $coprime(14, 25)

claim:
    ? forall a, b N:
        a != 0 or b != 0
        gcd(a, b) = 1
        =>:
            $coprime(a, b)
    by def $coprime(a, b)

claim:
    ? forall a, b N:
        a != 0 or b != 0
        gcd(a, b) = 1
        =>:
            $coprime(a, b)
    by def:
        ? $coprime(a, b)

forall a, b N:
    $coprime(a, b)
    =>:
        a != 0 or b != 0
        gcd(a, b) = 1
"#,
        "native_coprime_computation_definition_and_zero_boundary_are_exact",
    );
}

#[test]
fn native_coprime_rejects_false_claims_arity_and_non_natural_carriers() {
    for (label, source) in [
        ("native_coprime_zero_zero_is_false", "$coprime(0, 0)"),
        (
            "native_coprime_noncoprime_pair_is_false",
            "$coprime(14, 21)",
        ),
        (
            "native_coprime_coprime_pair_is_not_false",
            "not $coprime(14, 25)",
        ),
        ("native_coprime_wrong_arity", "$coprime(14)"),
        (
            "native_coprime_rejects_arbitrary_integers",
            "forall a, b Z:\n    $coprime(a, b)\n    =>:\n        a = a",
        ),
        (
            "native_coprime_rejects_arbitrary_reals",
            "forall a, b R:\n    not $coprime(a, b)\n    =>:\n        a = a",
        ),
        (
            "native_coprime_rejects_negative_integer",
            "$coprime(-14, 25)",
        ),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_dvd_definition_and_symbolic_expansion_are_exact() {
    assert_source_succeeds(
        r#"
$dvd(12, 3)
by def $dvd(12, 3)

forall x Z, y Z*:
    x % y = 0
    =>:
        $dvd(x, y)

forall x Z, y Z*:
    $dvd(x, y)
    =>:
        x % y = 0
        exist a Z st {x = a * y}
"#,
        "native_dvd_definition_and_symbolic_expansion_are_exact",
    );
}

#[test]
fn native_dvd_rejects_false_claims_zero_divisors_arity_and_non_integer_carriers() {
    for (label, source) in [
        ("native_dvd_false_literal", "$dvd(7, 3)"),
        ("native_dvd_zero_divisor", "$dvd(0, 0)"),
        ("native_dvd_wrong_arity", "$dvd(12)"),
        (
            "native_dvd_rejects_arbitrary_reals",
            "forall x, y R:\n    $dvd(x, y)\n    =>:\n        x = x",
        ),
    ] {
        assert_source_fails(source, label);
    }
}

#[test]
fn native_number_theory_symbolic_builtin_targets_can_be_deferred_to_their_proofs() {
    assert_source_succeeds(
        r#"
thm deferred_symbolic_coprime:
    ? forall a, b N:
        $coprime(a, b)
    trust $coprime(a, b)

thm deferred_symbolic_prime:
    ? forall n N:
        $prime(n)
    trust $prime(n)
"#,
        "native_number_theory_symbolic_builtin_targets_can_be_deferred_to_their_proofs",
    );
}

#[test]
fn native_number_theory_names_are_hard_reserved_but_uppercase_names_are_available() {
    for name in [QUOT, GCD, PRIME, COPRIME, DVD] {
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
        "have Quot Z = 0\nhave Prime Z = 1\nhave Coprime Z = 2\nhave Dvd Z = 3\nQuot = 0\nPrime = 1\nCoprime = 2\nDvd = 3",
        "uppercase_number_theory_names_remain_available",
    );
}

#[test]
fn native_number_theory_latex_is_mathematical() {
    let latex = to_latex_from_source(
        "quot(-7, 3) = -3\ngcd(54, 24) = 6\n$prime(97)\n$coprime(14, 25)\nnot $coprime(14, 21)",
        "native_number_theory_latex_is_mathematical",
    )
    .expect("native number theory should convert to LaTeX");
    assert!(
        latex.contains(r"\operatorname{quot}\left( -1 \cdot 7, 3 \right)"),
        "{latex}"
    );
    assert!(latex.contains(r"\gcd\left( 54, 24 \right)"), "{latex}");
    assert!(latex.contains(r"\operatorname{prime}"), "{latex}");
    assert!(latex.contains(r"\operatorname{coprime}"), "{latex}");
    assert!(latex.contains(r"\neg \operatorname{coprime}"), "{latex}");
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

    let quot_error = to_python_from_source(
        "quot(-7, 3) = -3",
        "native_quot_python_boundary_is_structural",
    )
    .expect_err("the native quot object is not supported by the Python extractor")
    .trace_message();
    assert!(
        quot_error.contains("does not support native quot"),
        "{quot_error}"
    );

    let prime_error =
        to_python_from_source("$prime(97)", "native_prime_python_boundary_is_structural")
            .expect_err("the builtin prime predicate is not supported by the Python extractor")
            .trace_message();
    assert!(
        prime_error.contains("does not support builtin prime"),
        "{prime_error}"
    );

    let coprime_error = to_python_from_source(
        "$coprime(14, 25)",
        "native_coprime_python_boundary_is_structural",
    )
    .expect_err("the builtin coprime predicate is not supported by the Python extractor")
    .trace_message();
    assert!(
        coprime_error.contains("does not support builtin coprime"),
        "{coprime_error}"
    );

    let dvd_error =
        to_python_from_source("$dvd(12, 3)", "native_dvd_python_boundary_is_structural")
            .expect_err("the builtin dvd predicate is not supported by the Python extractor")
            .trace_message();
    assert!(
        dvd_error.contains("does not support builtin dvd"),
        "{dvd_error}"
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
