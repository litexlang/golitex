use crate::prelude::*;

const ABS: &str = "forall x R:\n    x!=0\n    =>:\n        abs(x)>0\n";
const SQUARE: &str = "forall x,y R:\n    x>=0\n    y>=0\n    x^2<=y^2\n    =>:\n        x<=y\n";

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt
        .run_litex_code(source)
        .expect("public statement execution");
    assert!(
        run.session_error.is_none(),
        "{source}: {:?}",
        run.session_error
    );
    assert_eq!(run.success, expected, "{source}");
    run
}

fn named_rule(
    value: &crate::knowledge_base::JsonValue,
    name: &str,
) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get("rule").and_then(|value| value.as_str().ok()) == Some(name) {
                return Some(value.clone());
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|key| named_rule(fields.get(&key).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|value| named_rule(value, name)),
        _ => None,
    }
}

#[test]
fn direct_rules_retain_each_checked_premise() {
    for (source, name, fields) in [
        (ABS, "AbsPositiveFromNonzero", &["argument_nonzero"][..]),
        (
            SQUARE,
            "NonnegativeSquareOrderReflection",
            &["left_nonnegative", "right_nonnegative", "squared_order"][..],
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = check(&mut rt, source, true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let rule = named_rule(&detail, name).expect(name);
        for field in fields {
            let evidence = rule
                .as_object()
                .unwrap()
                .get(field)
                .expect(field)
                .stringify_pretty();
            assert!(
                evidence.contains("cite_fact_id"),
                "{name}.{field}: {evidence}"
            );
            assert!(
                evidence.contains("\"success\": true"),
                "{name}.{field}: {evidence}"
            );
        }
    }
}

#[test]
fn reversed_sources_and_compound_arguments_keep_actual_evidence() {
    for source in [
        "forall x,y R:\n    x-y!=0\n    =>:\n        0<abs(x-y)\n",
        "forall x,y R:\n    x>=0\n    y>=0\n    x^2>=y^2\n    =>:\n        x>=y\n",
        "forall x,y R:\n    0<=x\n    0<=y\n    y^2>=x^2\n    =>:\n        x<=y\n",
        "forall x,y R:\n    x>0\n    y>0\n    x^2<=y^2\n    =>:\n        x<=y\n",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = check(&mut rt, source, true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        if source.contains("y^2>=x^2") {
            let rule = named_rule(&detail, "NonnegativeSquareOrderReflection").unwrap();
            let premise = rule
                .as_object()
                .unwrap()
                .get("squared_order")
                .unwrap()
                .stringify_pretty();
            assert!(
                premise.contains("y ^ 2 >= x ^ 2"),
                "actual reverse-written source: {premise}"
            );
        }
    }
}

#[test]
fn false_missing_and_undefined_boundaries_reject() {
    for source in [
        "forall x R:\n    abs(x)>0\n",
        "0<abs(0)\n",
        "forall x,y R:\n    x>=0\n    x^2<=y^2\n    =>:\n        x<=y\n",
        "forall x,y R:\n    y>=0\n    x^2>=y^2\n    =>:\n        x>=y\n",
        "forall x,y R:\n    x>=0\n    y>=0\n    x^2<=y^2\n    =>:\n        x<y\n",
        "forall x,y R:\n    x>=0\n    y>=0\n    x^2<=y^2\n    =>:\n        y<=x\n",
        "have z C\nabs(z)>0\n",
        "abs(1/0)>0\n",
    ] {
        check(&mut runtime(OutputLanguage::English), source, false);
    }
}

#[test]
fn lower_permissions_and_failed_publication_remain_bounded() {
    for source in [ABS, SQUARE] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("forall fact");
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(
                rt.verify_fact(&fact, VerifyState::new(level))
                    .unwrap()
                    .is_failed(),
                "{level:?}: {source}"
            );
        }
        assert!(
            !rt.verify_fact(&fact, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{source}"
        );
    }
    let mut rt = runtime(OutputLanguage::English);
    let before = rt.top_exec_env().facts.facts_by_id.len();
    check(&mut rt, "claim:\n    ? forall x R:\n        x!=0\n        =>:\n            abs(x)>0\n    abs(x)>0\n    0=1\n", false);
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    check(&mut rt, ABS, true);
}

#[test]
fn maintained_rule_examples_are_strict_and_self_contained() {
    for source in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/abs_positive_from_nonzero.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/nonnegative_square_order_reflection.lit"
        )),
    ] {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}

#[test]
fn localized_output_and_unsupported_lean_routes_remain_explicit() {
    for language in OutputLanguage::ALL {
        for source in [ABS, SQUARE] {
            let mut rt = runtime(language);
            let run = check(&mut rt, source, true);
            let normal =
                crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
            assert!(!normal.contains("unsupported"), "{language:?}: {normal}");
        }
    }
    for source in [ABS, SQUARE] {
        let mut rt = runtime(OutputLanguage::English);
        let run = check(&mut rt, source, true);
        assert!(
            crate::compile_to_lean::compile_run(&run, &rt, "abs_square_rule").is_err(),
            "No Lean adapter was added"
        );
    }
}
