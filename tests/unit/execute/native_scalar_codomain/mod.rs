//! Native codomains must work through ordinary WD and preserve domain failures.
use crate::execute::ExecStmtResult;
use crate::json_output::{project_stmt_detailed, project_stmt_normal, stringify_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn exec(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    let mut last = None;
    for stmt in stmts {
        if let Some(previous) = &last {
            assert!(!ExecStmtResult::is_failed(previous), "setup failed: {code}");
        }
        last = Some(runtime.exec_stmt(&stmt).expect("exec_stmt"));
    }
    last.expect("at least one statement")
}

fn assert_accepts(code: &str) {
    let mut rt = runtime(OutputLanguage::English);
    let result = exec(&mut rt, code);
    assert!(
        !result.is_failed(),
        "{code}\n{}",
        stringify_normal(&project_stmt_normal(&result, &rt)),
    );
}

fn has_field(value: &JsonValue, key: &str, expected: &str) -> bool {
    match value {
        JsonValue::Object(map) => {
            map.get(key).and_then(|v| v.as_str().ok()) == Some(expected)
                || map
                    .keys_in_order()
                    .iter()
                    .any(|k| has_field(map.get(k).unwrap(), key, expected))
        }
        JsonValue::Array(values) => values.iter().any(|v| has_field(v, key, expected)),
        _ => false,
    }
}

#[test]
fn native_scalar_codomain_symbolic_memberships_and_supertypes() {
    let cases = [
        ("have a R", "sign(a)", vec!["Z", "Q", "R", "C"]),
        (
            "have a Z*\nhave b Z",
            "gcd(a, b)",
            vec!["N+", "N", "Z", "Q", "R", "Z*", "Q+", "R+", "Q*", "R*", "C"],
        ),
        (
            "have a Z\nhave b Z",
            "lcm(a, b)",
            vec!["N", "Z", "Q", "R", "C"],
        ),
        ("have x R", "exp(x)", vec!["R+", "R", "R*", "C"]),
        (
            "have n N",
            "n!",
            vec!["N+", "N", "Z", "Q", "R", "Z*", "Q+", "R+", "Q*", "R*", "C"],
        ),
    ];
    for (setup, obj, sets) in cases {
        for set in sets {
            // Fresh runtime: a previous stronger membership cannot mask a gap.
            assert_accepts(&format!("{setup}\n{obj} $in {set}"));
        }
    }
}

#[test]
fn native_scalar_codomain_nested_wd_needs_no_stored_carrier() {
    for code in [
        "have a R\nsign(0 - a) = 0 - sign(a)",
        "have a R\nsign(a) * abs(a) = a",
        "have a R\nabs(a) = sign(a) * a",
        "have a R\nhave b R\nsign(a * b) = sign(a) * sign(b)",
        "have a Z*\nhave b Z*\nlcm(a, b) * gcd(a, b) = abs(a * b)",
        "have a Z*\nhave b Z\na % gcd(a, b) = 0",
        "have x R\nln(exp(x)) = x",
        "have n N\n(n + 1)! = (n + 1) * n!",
        "have n N\nfactorial(n) $in N+",
        "have x R\ngcd(sign(x), 1) $in N+",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_checked_membership_supplies_nonzero_inference() {
    // Division requires a separate != 0 obligation. The existing store/infer
    // path obtains it from a checked positive carrier; no trusted fact needed.
    for code in [
        "have a R\nexp(a) $in R+\n1 / exp(a) $in R",
        "have a Z*\nhave b Z\ngcd(a, b) $in N+\n1 / gcd(a, b) $in R",
        "have n N\nn! $in N+\n1 / n! $in R",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_zero_and_signed_inputs() {
    for code in [
        "sign(0) $in Z",
        "sign(-1) $in Z",
        "gcd(0, -2) $in N+",
        "gcd(-2, 0) $in N+",
        "have a Z*\ngcd(0, a) $in N+",
        "have a Z\nlcm(a, 0) $in N",
        "lcm(0, 0) $in N",
        "exp(0) $in R+",
        "exp(-1) $in R+",
        "0! $in N+",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_rejects_invalid_domains_and_narrowing() {
    for code in [
        "sign(i) $in C",
        "have a C\nsign(a) $in Z",
        "gcd(0, 0) $in N+",
        "gcd(0, 0) $in C",
        "gcd(1.5, 1) $in N+",
        "have a Z\nhave b Z\ngcd(a, b) $in N+",
        "lcm(1.5, 1) $in N",
        "exp(i) $in C",
        "have n Z\nn! $in N+",
        "factorial(-1) $in N+",
        "factorial(1.5) $in N+",
        "sign(0) $in N+",
        "sign(-1) $in N",
        "have a R\nsign(a) $in N+",
        "lcm(0, 0) $in N+",
        "have a Z\nhave b Z\nlcm(a, b) $in N+",
        "have x R\nexp(x) $in Z",
        "have n N\nn! $in Z-",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, code);
        assert!(result.is_failed(), "unexpected acceptance: {code}");
    }
}

#[test]
fn native_scalar_codomain_normal_and_detailed_keep_native_carrier() {
    for (setup, goal, carrier) in [
        ("have a R", "sign(a) $in C", "Z"),
        ("have a Z*\nhave b Z", "gcd(a, b) $in N+", "N+"),
        ("have a Z\nhave b Z", "lcm(a, b) $in R", "N"),
        ("have x R", "exp(x) $in R+", "R+"),
        ("have n N", "n! $in N", "N+"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, &format!("{setup}\n{goal}"));
        assert!(!result.is_failed(), "{goal}");
        let normal = project_stmt_normal(&result, &rt);
        assert!(has_field(&normal, "rule_name", "Native Scalar Codomain"));
        assert!(has_field(&normal, "message", &format!(
            "after input-domain WD, the native result belongs to {carrier} and its standard-set supertypes"
        )));
        let detailed = project_stmt_detailed(&result, &rt);
        assert!(has_field(&detailed, "rule", "NativeScalarCodomain"));
        assert!(has_field(&detailed, "codomain", carrier));
    }
    let mut rt = runtime(OutputLanguage::Chinese);
    let result = exec(&mut rt, "have a R\nsign(a) $in R");
    let normal = stringify_normal(&project_stmt_normal(&result, &rt));
    assert!(normal.contains("原生标量返回类型"));
    assert!(normal.contains("属于 Z"));
}
