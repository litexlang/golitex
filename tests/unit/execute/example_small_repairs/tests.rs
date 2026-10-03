use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(code: &str, expected: bool) -> (String, String) {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = rt.run_litex_code(code).unwrap();
    let normal = crate::json_output::emit_run_normal(&run, &rt, "example small repairs", None);
    let detailed = crate::json_output::emit_run_detailed(&run, &rt, "example small repairs", None);
    assert!(run.session_error.is_none(), "{code}\n{detailed}");
    assert_eq!(run.success, expected, "{code}\n{detailed}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    (normal, detailed)
}
#[test]
fn example_small_positive_integer_requires_both_certificates() {
    let (normal, detailed) = check("forall k Z:\n    k > 0\n    =>:\n        k $in N+", true);
    for key in ["PositiveIntegerInNPos", "integer_proof", "positive_proof"] {
        assert!(detailed.contains(key));
    }
    assert!(normal.contains("Universal"));
    for code in [
        "forall k Z:\n    k $in N+",
        "forall k R:\n    k > 0\n    =>:\n        k $in N+",
        "0 $in N+",
        "-1 $in N+",
        "0.5 $in N+",
    ] {
        check(code, false);
    }
    check("forall k Z:\n    k > 1\n    =>:\n        k - 1 $in Z\n        k - 1 > 0\n        k - 1 $in N+",true);
    // The local forall proof must not publish its parameter or assumption.
    check(
        "forall k Z:\n    k > 0\n    =>:\n        k $in N+\nhave k Z\nk $in N+",
        false,
    );
}
#[test]
fn example_small_scalar_rules_keep_domains_and_nonzero_premises() {
    for code in [
        "forall a, b R:\n    a - b != 0\n    =>:\n        a != b",
        "forall a, b R:\n    a + b != 0\n    =>:\n        a != -b",
        "forall x R:\n    abs(x) = 0\n    =>:\n        x = 0",
        "forall x R:\n    floor(-x) = -ceil(x)",
        "forall x R, n Z:\n    floor(n + x) = n + floor(x)",
        "forall a, b R:\n    max(min(b, a), a) = a",
        "forall a Z:\n    0 = lcm(0, a)",
        "forall z C:\n    z != 0\n    =>:\n        C_abs(z) != 0",
    ] {
        check(code, true);
    }
    for code in [
        "forall a, b R:\n    a != b",
        "forall a, b R:\n    a + b = 0\n    =>:\n        a != -b",
        "forall x R:\n    abs(x) = 1\n    =>:\n        x = 0",
        "forall x R, n R:\n    floor(x + n) = floor(x) + n",
        "forall x R:\n    ceil(-x) = -ceil(x)",
        "forall z C:\n    C_abs(z) != 0",
        "lcm(0, 0) = 1",
    ] {
        check(code, false);
    }
}
#[test]
fn example_small_definition_publication_preserves_disjunction_and_direction() {
    check("forall a, b N:\n    $coprime(a, b)\n    =>:\n        a != 0 or b != 0\n        gcd(a, b) = 1",true);
    check(
        "forall a, b N:\n    $coprime(a, b)\n    =>:\n        a != 0",
        false,
    );
    check("gcd(0, 0) = 0", false);
    check("$dvd(6, 3)", true);
    check("$dvd(3, 6)", false);
    check("$dvd(0, 0)", false);
    check(
        "forall p N, d range(2, p):\n    $prime(p)\n    =>:\n        2 <= p\n        p % d != 0",
        true,
    );
    check("forall p N:\n    $prime(p)\n    =>:\n        p = 0", false);
    check("forall A, B set, f fn(x A) B:\n    $bijective(A, B, f)\n    =>:\n        $injective(A, B, f)\n        $surjective(A, B, f)",true);
    check("forall A, B set, f fn(x A) B:\n    $injective(A, B, f)\n    =>:\n        $surjective(A, B, f)",false);
}
#[test]
fn example_small_ranges_and_finite_surjections_keep_exact_boundaries() {
    for code in ["range(2, 5) = {x Z: 2 <= x < 5}","closed_range(2, 5) = {x Z: 2 <= x <= 5}",
        "range(3, 3) = {x Z: 3 <= x < 3}","closed_range(5, 2) = {x Z: 5 <= x <= 2}",
        "forall A finite_set, B set, f fn(x A) B:\n    $surjective(A, B, f)\n    =>:\n        $is_finite_set(B)"] {check(code,true);}
    for code in ["range(2, 5) = {x Z: 2 <= x <= 5}","closed_range(2, 5) = {x Z: 2 <= x < 5}",
        "range(2, 5) = {x R: 2 <= x < 5}","range(2, 5) = {x Z: 2 <= x < 5, x != 3}",
        "forall A finite_set, B set, f fn(x A) B:\n    $is_finite_set(B)",
        "forall A set, B set, f fn(x A) B:\n    $surjective(A, B, f)\n    =>:\n        $is_finite_set(B)"] {check(code,false);}
}
#[test]
fn example_small_finite_eval_keeps_exact_values_and_stores_no_equality() {
    for (code, value) in [
        ("eval finite_set_size({1, 2, 3})", "3"),
        ("eval tuple_dim((1, 2, 3))", "3"),
        ("eval (1, 2, 3)[2]", "2"),
        ("eval finite_set_max({1 / 3, 2 / 3})", "2 / 3"),
        ("eval finite_set_min({1 / 3, 2 / 3})", "1 / 3"),
        ("eval finite_set_size({})", "0"),
    ] {
        let (normal, _) = check(code, true);
        assert!(normal.contains(&format!("\"evaluated_object\": \"{value}\"")));
        assert!(normal.contains("\"stores\": []"));
    }
    for code in [
        "eval finite_set_max({})",
        "eval finite_set_min({i})",
        "eval (1, 2)[0]",
        "eval (1, 2)[3]",
        "eval finite_set_size({1, 1.0})",
    ] {
        check(code, false);
    }
}
#[test]
fn example_small_cases_and_fact_wd_report_nested_reason_in_both_profiles() {
    for (code,phase) in [
        ("have fn bad(x R: 0 <= x <= 1 or 1 <= x <= 2) N by cases:\n    case 0 <= x <= 1: 0\n    case 1 <= x <= 2: 1","disjoint"),
        ("have fn bad(x R: 0 <= x < 1 or 1 <= x < 2) N by cases:\n    case 0 <= x < 1: 0\n    case 1 < x < 2: 1","coverage"),
        ("have fn bad(x R: 0 <= x < 1 or 1 <= x < 2) N by cases:\n    case 0 <= x < 1: 1 / 0\n    case 1 <= x < 2: 1","case_body_well_defined"),
        ("have fn bad(x R: 0 <= x < 1 or 1 <= x < 2) N by cases:\n    case 0 <= x < 1: -1\n    case 1 <= x < 2: 1","case_body_in_return_set"),
    ] {let (normal,detailed)=check(code,false);assert!(normal.contains(phase),"{normal}");assert!(detailed.contains(phase));
        if phase.starts_with("case_body") || phase=="disjoint" {assert!(normal.contains("\"case_index\": 1"));}}
    let (normal, detailed) = check(
        "let family = fn(k {1, 2}) power_set(N) {{1}}\nfamily(3) = {1}",
        false,
    );
    for output in [normal, detailed] {
        assert!(output.contains("3 $in {1, 2}"), "{output}");
    }
}

#[test]
fn example_small_integer_arithmetic_closure_keeps_operand_types() {
    for code in ["forall a, b Z:\n    -a $in Z\n    abs(a) $in Z\n    a + b $in Z\n    a - b $in Z\n    a * b $in Z", "forall a Z:\n    a $in N+\n    =>:\n        a - 1 $in Z"] {check(code,true);}
    for code in [
        "forall a R:\n    -a $in Z",
        "forall a, b Z:\n    b != 0\n    =>:\n        a / b $in Z",
        "forall a Z, b R:\n    a + b $in Z",
    ] {
        check(code, false);
    }
}

#[test]
fn example_small_literal_function_application_keeps_declared_carrier() {
    for code in [
        "forall x, y Z:\n    fn(a, b Z) Z {a + b}(x, y) $in Z",
        "forall x, y R:\n    fn(a, b R) R {a + b}(x, y) $in R",
    ] {
        check(code, true);
    }
    for code in [
        "fn(a, b Z) Z {a + b}(0.5, 1) $in Z",
        "forall x, y R:\n    fn(a, b R) R {a + b}(x, y) $in Z",
        "fn(a, b Z) Z {a + b}(1) $in Z",
        "fn(a R) Z {a}(0.5) $in Z",
    ] {
        check(code, false);
    }
}
