use crate::prelude::*;

const ABS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/equal/by_builtin_rule/abs_product_closed_coefficient.lit"
));
const SUM: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_strategy/add_double_upper_bound.lit"
));

#[test]
fn closed_abs_factors_and_common_sum_bounds_verify_through_public_execution() {
    for code in [ABS, SUM] {
        check(&mut runtime(), code, true);
    }
}

#[test]
fn closed_abs_factors_reject_wrong_signs_values_symbolic_coefficients_and_undefined_inputs() {
    for code in [
        "forall x R:\n    abs(-2*x)=-2*abs(x)",
        "forall x R:\n    abs(2*x)=3*abs(x)",
        "forall c,x R:\n    abs(c*x)=c*abs(x)",
        "abs(0*(1/0))=0",
        "forall x C:\n    abs(0*x)=0*abs(x)",
    ] {
        let mut rt = runtime();
        check(&mut rt, code, false);
        check(&mut rt, "1+1=2", true);
    }
}

#[test]
fn double_sum_bound_requires_both_bounds_and_preserves_weakness() {
    for code in [
        "forall a,b,M R:\n    a<=M\n    =>:\n        a+b<=2*M",
        "forall a,b,M R:\n    b<=M\n    =>:\n        a+b<=2*M",
        "forall a,b,M R:\n    a<=M\n    b<=M\n    =>:\n        a+b<=M",
        "forall a,b,M R:\n    a<=M\n    b<=M\n    =>:\n        a+b<2*M",
        "forall a,b,M R:\n    M<0\n    a=M\n    b=M\n    =>:\n        a+b<=3*M",
    ] {
        let mut rt = runtime();
        check(&mut rt, code, false);
        check(&mut rt, "1+1=2", true);
    }
}

#[test]
fn double_sum_bound_retains_two_premises_in_detailed_output() {
    let mut rt = runtime();
    let run = check(&mut rt, SUM, true);
    let detailed = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
    let selected = find_strategy(&detailed, "AddDoubleUpperBound")
        .expect("the normalized target selects its own bounded strategy");
    let JsonValue::Object(fields) = selected else {
        panic!("strategy object");
    };
    let Some(JsonValue::Array(children)) = fields.get("proof_of_requirement_facts") else {
        panic!("both bound proofs must be visible");
    };
    assert_eq!(children.len(), 2);
}

#[test]
fn new_strategy_is_explicitly_unsupported_by_lean_until_it_has_a_replay_adapter() {
    let mut rt = runtime();
    let run = check(&mut rt, SUM, true);
    let Err(error) = crate::compile_to_lean::compile_run(&run, rt, "double_upper_bound") else {
        panic!("a new strategy needs a checked replay adapter");
    };
    assert_eq!(error.route, "Atomic/BuiltinStrategy");
    assert!(error.message.contains("Unsupported selected strategy"));
}

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn check(rt: &mut Runtime, code: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(code).expect("public statement execution");
    assert!(
        run.session_error.is_none(),
        "{code}: {:?}",
        run.session_error
    );
    assert_eq!(run.success, expected, "{code}");
    run
}

fn find_strategy<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields.get("strategy").and_then(|v| v.as_str().ok()) == Some(name) {
                return Some(value);
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|key| find_strategy(fields.get(&key).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| find_strategy(v, name)),
        _ => None,
    }
}
