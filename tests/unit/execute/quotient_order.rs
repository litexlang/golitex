use crate::prelude::*;

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

fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let result = rt.run_litex_code(source).unwrap();
    assert!(result.input_error.is_none(), "{source}");
    assert!(result.session_error.is_none(), "{source}");
    assert_eq!(result.success, expected, "{source}");
    result
}

#[test]
fn quotient_order_direct_positive_and_negative_numerators() {
    for source in [
        include_str!(
            "../../../examples/proof_nodes/atomic/by_builtin_strategy/quotient_unit_order.lit"
        ),
        include_str!(
            "../../../examples/proof_nodes/atomic/by_builtin_strategy/quotient_scale_order.lit"
        ),
        "forall a,b R:\n    b>0\n    a<=b\n    =>:\n        a/b<=1",
        "forall a,b R:\n    b>0\n    a>b\n    =>:\n        a/b>1",
        "forall a,b R:\n    b>0\n    a>=b\n    =>:\n        a/b>=1",
        "forall a,b R:\n    a<0\n    b>1\n    =>:\n        a/b>a",
        "forall a,b R:\n    a>=0\n    b>0\n    b<=1\n    =>:\n        a/b>=a",
        "forall a,b R:\n    a<=0\n    b>0\n    b<=1\n    =>:\n        a/b<=a",
        "forall a,b R+:\n    1>b\n    =>:\n        a<a/b",
        "forall a,b R:\n    0>a\n    1<b\n    =>:\n        a<a/b",
    ] {
        check(&mut runtime(), source, true);
    }
}

#[test]
fn quotient_order_rejects_missing_guards_wrong_directions_and_strict_endpoints() {
    for source in [
        "forall a,b R:\n    a<b\n    b!=0\n    =>:\n        a/b<1",
        "forall a,b R:\n    b<0\n    a<b\n    =>:\n        a/b<1",
        "forall x R:\n    x<1\n    x!=0\n    =>:\n        1/x>1",
        "forall a,b R+:\n    a<=b\n    =>:\n        a/b<1",
        "forall a,b R+:\n    a<b\n    =>:\n        a/b>1",
        "forall a,b R:\n    a>=0\n    b>1\n    =>:\n        a/b<a",
        "forall a,b R+:\n    b>=1\n    =>:\n        a/b<a",
        "forall a,b R:\n    b>1\n    =>:\n        a/b<a",
        "forall a,b R:\n    a<0\n    b>1\n    =>:\n        a/b<a",
        "forall a,b R+:\n    b<1\n    =>:\n        a/b<a",
        "1/0<1",
        "0/2<0",
        "2/1<2",
    ] {
        check(&mut runtime(), source, false);
    }
}

#[test]
fn quotient_order_retains_premises_in_detailed_output_and_reading() {
    for (source, name, count) in [
        (
            "forall a,b R:\n    b>0\n    a>b\n    =>:\n        a/b>1",
            "QuotientUnitLess",
            2,
        ),
        (
            "forall a,b R:\n    b>0\n    a>=b\n    =>:\n        a/b>=1",
            "QuotientUnitLessEqual",
            2,
        ),
        (
            "forall a,b R+:\n    b<1\n    =>:\n        a/b>a",
            "QuotientScaleLess",
            3,
        ),
        (
            "forall a,b R:\n    a>=0\n    b>0\n    b<=1\n    =>:\n        a/b>=a",
            "QuotientScaleLessEqual",
            3,
        ),
    ] {
        let mut rt = runtime();
        let run = check(&mut rt, source, true);
        let detailed = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let proof = find_strategy(&detailed, name).expect("selected strategy evidence");
        let fields = proof.as_object().unwrap();
        assert_eq!(
            fields
                .get("requirement_facts")
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            count
        );
        assert_eq!(
            fields
                .get("proof_of_requirement_facts")
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            count
        );
        let json = detailed.stringify_pretty();
        assert!(json.contains(name), "{json}");
        assert!(json.contains("requirement_facts"));
        assert!(json.contains("proof_of_requirement_facts"));
        assert!(json.contains("cite_fact_id"));
        let reading = crate::reading::build_reading(
            &crate::reading::ReadingInput::Source(source.to_owned()),
            true,
            OutputLanguage::English,
        );
        assert!(reading.success);
        let reading_json = reading.document.stringify_pretty();
        assert!(reading_json.contains(name));
    }
}

#[test]
fn quotient_order_preserves_restricted_search_and_scope() {
    let mut rt = runtime();
    check(&mut rt, "have a,b R", true);
    check(
        &mut rt,
        "sketch:\n    forall x,y R+:\n        x>y\n        =>:\n            x/y>1",
        true,
    );
    check(&mut rt, "a/b>1", false);
    let source = "forall x,y R+:\n    x>y\n    =>:\n        x/y>1";
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let state = VerifyState::new(VerifyStateLevel::Direct).without_inference();
    assert!(rt.verify_fact(&fact, state).unwrap().is_failed());
    assert_eq!(before, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, source, true);
}

fn find_strategy(
    value: &crate::knowledge_base::JsonValue,
    name: &str,
) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get("strategy").and_then(|v| v.as_str().ok()) == Some(name) {
                return Some(value.clone());
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|key| find_strategy(fields.get(&key).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|item| find_strategy(item, name)),
        _ => None,
    }
}
