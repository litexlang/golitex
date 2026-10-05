use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn check(source: &str, expected: bool) -> String {
    let mut rt = runtime(OutputLanguage::English);
    let result = rt.run_litex_code(source).unwrap();
    let detailed = emit_run_detailed(&result, &rt, "eval", None);
    assert!(result.session_error.is_none(), "{source}\n{detailed}");
    assert_eq!(result.success, expected, "{source}\n{detailed}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    detailed
}
fn find_rule(value: &JsonValue, rule: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(map) => {
            if map.get("rule").and_then(|v| v.as_str().ok()) == Some(rule) {
                return Some(value.clone());
            }
            for (_, child) in map.iter() {
                if let Some(found) = find_rule(child, rule) {
                    return Some(found);
                }
            }
        }
        JsonValue::Array(array) => {
            for child in array {
                if let Some(found) = find_rule(child, rule) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}
fn evidence(json: &str, rule: &str) -> JsonValue {
    find_rule(&JsonValue::parse(json).unwrap(), rule)
        .unwrap_or_else(|| panic!("missing {rule}: {json}"))
}

#[test]
fn cosine_double_angle_three_cold_forms_keep_matched_evidence() {
    for (rhs, form) in [
        ("cos(x)^2-sin(x)^2", "cosine_square_minus_sine_square"),
        ("1-2*sin(x)^2", "one_minus_twice_sine_square"),
        ("2*cos(x)^2-1", "twice_cosine_square_minus_one"),
    ] {
        let json = check(&format!("forall x R:\n    cos(2*x)={rhs}\n"), true);
        let node = evidence(&json, "CosDoubleAngle");
        let object = node.as_object().unwrap();
        assert_eq!(object.get("form").unwrap().as_str().unwrap(), form);
        assert_eq!(object.get("angle").unwrap().as_str().unwrap(), "x");
    }
    for code in [
        "forall x R:\n    cos(x+x)=cos(x)*cos(x)-sin(x)*sin(x)",
        "forall x R:\n    2*cos(x)^2-1=cos(x*2)",
        "forall x,y R:\n    cos(2*(x+y))=1-2*sin(x+y)^2",
    ] {
        evidence(&check(code, true), "CosDoubleAngle");
    }
}

const REFLECTIONS: [(&str, &str); 4] = [
    ("sin(pi-x)=sin(x)", "SinPiReflection"),
    ("cos(pi-x)=-cos(x)", "CosPiReflection"),
    ("sin(pi/2-x)=cos(x)", "SinHalfPiReflection"),
    ("cos(pi/2-x)=sin(x)", "CosHalfPiReflection"),
];

#[test]
fn reflections_are_cold_structural_leaves_with_checked_real_wd() {
    for (goal, rule) in REFLECTIONS {
        let json = check(&format!("forall x R:\n    {goal}"), true);
        let node = evidence(&json, rule);
        assert_eq!(
            node.as_object()
                .unwrap()
                .get("angle")
                .unwrap()
                .as_str()
                .unwrap(),
            "x"
        );
    }
    for (goal, rule) in [
        ("sin(x)=sin((-x)+pi)", "SinPiReflection"),
        ("0-cos(x)=cos(pi+(-x))", "CosPiReflection"),
        ("cos(x)=sin((-x)+0.5*pi)", "SinHalfPiReflection"),
        ("sin(x)=cos(pi*(1/2)+(-x))", "CosHalfPiReflection"),
        ("sin(pi-(x+1))=sin(x+1)", "SinPiReflection"),
        ("cos(pi-(x+1))=-cos(x+1)", "CosPiReflection"),
        ("sin(pi/2-(x+1))=cos(x+1)", "SinHalfPiReflection"),
        ("cos(pi/2-(x+1))=sin(x+1)", "CosHalfPiReflection"),
    ] {
        evidence(&check(&format!("forall x R:\n    {goal}"), true), rule);
    }
}

#[test]
fn wrong_coefficients_signs_angles_and_arguments_remain_rejected() {
    for goal in [
        "cos(2*x)=cos(x)^2+sin(x)^2",
        "cos(2*x)=1+2*sin(x)^2",
        "cos(2*x)=2*cos(x)^2+1",
        "cos(3*x)=1-2*sin(x)^2",
        "cos(2*x)=-cos(x)^2-sin(x)^2",
        "sin(pi-x)=-sin(x)",
        "cos(pi-x)=cos(x)",
        "sin(pi/2-x)=-cos(x)",
        "cos(pi/2-x)=-sin(x)",
        "sin(pi/3-x)=sin(x)",
        "cos(pi/3-x)=-cos(x)",
        "sin(pi/3-x)=cos(x)",
        "cos(pi/3-x)=sin(x)",
        "sin(x-pi)=sin(x)",
        "cos(x-pi/2)=-sin(x)",
        "sin(pi-x)=sin(x+1)",
        "cos(pi/2-x)=sin(x+1)",
    ] {
        check(&format!("forall x R:\n    {goal}"), false);
    }
    check("forall x,y R:\n    cos(2*x)=1-2*sin(y)^2", false);
    check("forall x,k R:\n    sin(k*pi-x)=sin(x)", false);
}

#[test]
fn parent_wd_keeps_real_function_arguments_and_partial_calls() {
    for (goal, _) in REFLECTIONS {
        check(&format!("forall x C:\n    {goal}"), false);
    }
    check("forall x C:\n    cos(2*x)=1-2*sin(x)^2", false);
    check(
        "have f fn(x R)C\nforall x R:\n    sin(pi-f(x))=sin(f(x))",
        false,
    );
    check("forall x R:\n    cos(2*(1/x))=1-2*sin(1/x)^2", false);
    check(
        "forall x R:\n    x!=0\n    =>:\n        cos(2*(1/x))=1-2*sin(1/x)^2",
        true,
    );
    for carrier in ["Q", "Z", "R+"] {
        check(&format!("forall x {carrier}:\n    sin(pi-x)=sin(x)"), true);
    }
}

#[test]
fn accepted_equalities_store_and_failed_goal_preserves_the_session() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code("have x R").unwrap().success);
    let result = rt.run_litex_code("cos(2*x)=1-2*sin(x)^2").unwrap();
    assert!(result.success);
    evidence(
        &emit_run_detailed(&result, &rt, "session", None),
        "CosDoubleAngle",
    );
    let rejected = rt.run_litex_code("cos(2*x)=1+2*sin(x)^2").unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    assert_eq!(rt.execution_environments_stack.len(), 1);
    let reused = rt.run_litex_code("1-2*sin(x)^2=cos(2*x)").unwrap();
    assert!(reused.success && reused.session_error.is_none());
    let json = emit_run_detailed(&reused, &rt, "session", None);
    assert!(json.contains("cite_fact_id"), "{json}");
    assert!(rt.run_litex_code("1=1").unwrap().success);
}

#[test]
fn each_new_rule_has_normal_explanations_in_all_ten_languages() {
    for language in OutputLanguage::ALL {
        for goal in [
            "cos(2*x)=cos(x)^2-sin(x)^2",
            "sin(pi-x)=sin(x)",
            "cos(pi-x)=-cos(x)",
            "sin(pi/2-x)=cos(x)",
            "cos(pi/2-x)=sin(x)",
        ] {
            let mut rt = runtime(language);
            assert!(rt.run_litex_code("have x R").unwrap().success);
            let result = rt.run_litex_code(goal).unwrap();
            assert!(result.success && result.session_error.is_none());
            let normal = emit_run_normal(&result, &rt, "eval", None);
            assert!(normal.contains(goal), "{language:?}\n{normal}");
        }
    }
}

#[test]
fn five_complete_durable_tracers_verify() {
    for source in [
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/cos_double_angle.lit"),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/sin_pi_reflection.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/cos_pi_reflection.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/sin_half_pi_reflection.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/cos_half_pi_reflection.lit"
        ),
    ] {
        check(source, true);
    }
}

#[test]
fn adjacent_shift_and_sum_rules_keep_their_existing_routes() {
    for (goal, rule) in [
        ("sin(x+pi/2)=cos(x)", "SinHalfPiShift"),
        ("cos(x+pi/2)=-sin(x)", "CosHalfPiShift"),
        ("sin(2*x)=2*sin(x)*cos(x)", "SinDoubleAngle"),
        ("sin(x-1)=sin(x)*cos(1)-cos(x)*sin(1)", "SinDifference"),
        ("cos(x-1)=cos(x)*cos(1)+sin(x)*sin(1)", "CosDifference"),
    ] {
        evidence(&check(&format!("forall x R:\n    {goal}"), true), rule);
    }
}
