use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::knowledge_base::{JsonObject, JsonValue};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn fact(rt: &mut Runtime, text: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(text, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(fact) = statements.remove(0) else {
        panic!("{text}")
    };
    assert!(statements.is_empty());
    fact
}

#[test]
fn maintained_field_and_exact_scalar_examples_pass() {
    for code in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_strategy/field_arithmetic_carrier_closure.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/closed_exact_scalar_membership.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/even_power_real_carrier.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/closed_complex_not_equal.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/closed_complex_real_order.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/real_arithmetic_operand_carriers.lit"
        )),
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{:?}", run.session_error);
        assert!(run.success, "{code}");
    }
}

#[test]
fn field_closure_retains_the_requested_carrier_and_division_domain() {
    for code in [
        "forall a R:\n    3*a+2 $in Q\n",
        "forall a, b Q:\n    (3*a+2)/b $in Q\n",
        "forall a Q:\n    (3*a+2)/0 $in Q\n",
        "sqrt(2)+1 $in Q",
        "forall a Q:\n    (a+1)/(a-a) $in Q\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "incorrect admission: {code}");
    }
}

#[test]
fn complex_wd_cannot_be_used_as_a_real_result_certificate() {
    for code in [
        "forall a C:\n    a+1 $in R\n",
        "forall a C:\n    a-1 $in R\n",
        "forall a C:\n    -a $in R\n",
        "forall a C:\n    2*a $in R\n",
        "forall a C:\n    a/2 $in R\n",
        "forall a C:\n    a^1 $in R\n",
        "(i+1)*2 $in R",
        "i^3 $in R",
        "have fn bad(a C) R = a+1",
        "forall x R:\n    x^(1/2) $in R\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "unsound real output: {code}");
    }
}

#[test]
fn exact_coordinates_enforce_integer_sign_nonzero_and_wd_boundaries() {
    for code in [
        "(i*i)/2 $in Z",
        "i^2 $in N",
        "i-i $in N+",
        "i^4 $in Q-",
        "i-i $in C*",
        "(i-i)/0 $in Q",
        "0^(-1) $in Q",
        "abs(i) $in R",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(
            !run.success,
            "incorrect exact scalar/domain admission: {code}"
        );
    }
    for code in ["(i*i)/2 $in Q-", "i $in C*", "i^2 $in R-", "C_abs(i) $in R"] {
        assert!(runtime().run_litex_code(code).unwrap().success, "{code}");
    }
}

#[test]
fn even_power_order_and_closed_complex_inequality_preserve_soundness() {
    for code in [
        "0 <= i^2",
        "0 < i^2",
        "0 <= i*i",
        "0 < i*i",
        "i^2 $in N",
        "i^2 $in N+",
        "i > 0",
        "1+i <= 0",
        "(1+i)*(1-i) != 2",
        "i^2 != -1",
        "i-i != 0",
        "(1+i)/(i-i) $in Q",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "unsound admission: {code}");
    }
    for code in [
        "0 <= i^4",
        "0 < i^4",
        "i^2 < 0",
        "1+i != 0",
        "(1+i)/(1+i) $in Q",
    ] {
        assert!(runtime().run_litex_code(code).unwrap().success, "{code}");
    }
}

#[test]
fn detailed_even_power_and_complex_inequality_record_checked_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have x R\n0 <= x^2\n").unwrap();
    assert!(run.success);
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt);
    let proof = find(&detail, "rule", "EvenPowNonnegative").unwrap();
    let child = proof.get("base_in_real_proof").unwrap();
    assert!(
        find(child, "fact", "x $in R").is_some(),
        "{}",
        detail.stringify()
    );

    let run = rt.run_litex_code("1+i != 0").unwrap();
    assert!(run.success);
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let target = find(&detail, "fact", "1 + i != 0").unwrap();
    let proof = find(
        target.get("searched_proof").unwrap(),
        "type",
        "by_closed_calculation",
    )
    .unwrap();
    let Some(JsonValue::Object(values)) = proof.get("values") else {
        panic!("exact values")
    };
    for (key, value) in [
        ("left_real", "1"),
        ("left_imaginary", "1"),
        ("right_real", "0"),
        ("right_imaginary", "0"),
    ] {
        assert_eq!(values.get(key), Some(&JsonValue::String(value.into())));
    }
}

#[test]
fn constructor_descent_keeps_the_central_leaf_ceiling() {
    for (level, expected) in [
        (VerifyStateLevel::Direct, false),
        (VerifyStateLevel::KnownSpecialProperty, false),
        (VerifyStateLevel::BuiltinRule, false),
        (VerifyStateLevel::Strategy, true),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code("have a Q").unwrap().success);
        let target = fact(&mut rt, "3*a+2 $in Q");
        assert_eq!(
            !rt.verify_fact(&target, VerifyState::new(level))
                .unwrap()
                .is_failed(),
            expected,
            "{level:?}"
        );
    }
}

#[test]
fn nested_field_constructors_have_no_search_depth_reset() {
    let mut expression = "a".to_string();
    for _ in 0..2 {
        expression = format!("(({expression}) * 3 + 2) / 5");
    }
    let code = format!("forall a Q:\n    {expression} $in Q\n");
    assert!(runtime().run_litex_code(&code).unwrap().success);
}

fn find<'a>(value: &'a JsonValue, key: &str, name: &str) -> Option<&'a JsonObject> {
    match value {
        JsonValue::Object(object) => {
            if matches!(object.get(key), Some(JsonValue::String(s)) if s == name) {
                return Some(object);
            }
            object.iter().find_map(|(_, child)| find(child, key, name))
        }
        JsonValue::Array(children) => children.iter().find_map(|child| find(child, key, name)),
        _ => None,
    }
}

#[test]
fn detailed_field_tree_and_exact_coordinates_are_real_proof_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have a Q\n(3*a+2)/5 $in Q\n").unwrap();
    assert!(run.success);
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt);
    let proof = find(&detail, "strategy", "FieldArithmeticCarrierClosure")
        .unwrap_or_else(|| panic!("{}", detail.stringify()));
    assert_eq!(proof.get("carrier"), Some(&JsonValue::String("Q".into())));
    let Some(JsonValue::Array(facts)) = proof.get("requirement_facts") else {
        panic!("facts")
    };
    let expected = ["3 $in Q", "a $in Q", "2 $in Q", "5 $in Q", "5 != 0"];
    assert_eq!(
        facts,
        &expected
            .iter()
            .map(|s| JsonValue::String(s.to_string()))
            .collect::<Vec<_>>()
    );
    let Some(JsonValue::Array(children)) = proof.get("proof_of_requirement_facts") else {
        panic!("children")
    };
    assert_eq!(children.len(), expected.len());
    let Some(JsonValue::Object(tree)) = proof.get("constructor_tree") else {
        panic!("tree")
    };
    assert_eq!(
        tree.get("constructor"),
        Some(&JsonValue::String("div".into()))
    );
    assert_eq!(
        tree.get("nonzero_requirement_index"),
        Some(&JsonValue::Number(4.0))
    );
    let tree = tree.get("left").unwrap();
    assert!(find(tree, "constructor", "add").is_some());
    assert!(find(tree, "constructor", "mul").is_some());
    for child in children {
        assert!(child.stringify().contains("\"success\""));
    }

    let run = rt.run_litex_code("i^2 $in Z").unwrap();
    assert!(run.success);
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let target = find(&detail, "fact", "i ^ 2 $in Z").unwrap();
    let proof = find(
        target.get("searched_proof").unwrap(),
        "type",
        "by_closed_calculation",
    )
    .unwrap();
    let Some(JsonValue::Object(value)) = proof.get("value") else {
        panic!("exact value")
    };
    assert_eq!(value.get("real"), Some(&JsonValue::String("-1".into())));
    assert_eq!(value.get("imaginary"), Some(&JsonValue::String("0".into())));
}
