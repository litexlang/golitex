use crate::prelude::*;

const POSITIVE: &str =
    "forall a R, p,q C:\n    a>=0\n    q!=0\n    sqrt(a)=p/q\n    =>:\n        p^2=a*q^2\n";

#[test]
fn sqrt_quotient_square_positive_orientations_and_general_scalars() {
    for source in [
        POSITIVE.to_string(),
        POSITIVE.replace("sqrt(a)=p/q", "p/q=sqrt(a)"),
        POSITIVE.replace("p^2=a*q^2", "a*q^2=p^2"),
        POSITIVE.replace("p^2=a*q^2", "p^2=q^2*a"),
        POSITIVE.replace("p^2=a*q^2", "q^2*a=p^2"),
        POSITIVE.replace("p,q C", "p,q R"),
        POSITIVE
            .replace("p,q C", "p Z,q N+")
            .replace("    q!=0\n", ""),
    ] {
        check(&mut runtime(), &source, true);
    }
    check(
        &mut runtime(),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient_square.lit"
        ),
        true,
    );
}

#[test]
fn sqrt_quotient_square_rejects_missing_premises_wrong_targets_and_converse() {
    for source in [
        POSITIVE.replace("    sqrt(a)=p/q\n", ""),
        POSITIVE.replace("    q!=0\n", ""),
        POSITIVE.replace("    a>=0\n", ""),
        POSITIVE.replace("p^2=a*q^2", "p^2=(a+1)*q^2"),
        POSITIVE.replace("p^2=a*q^2", "p^3=a*q^2"),
        POSITIVE.replace("p^2=a*q^2", "p^2=a*q^3"),
        POSITIVE
            .replace("p,q C", "p,q,r C")
            .replace("sqrt(a)=p/q", "sqrt(a)=p/r"),
        "forall a,p,q R:\n    a>=0\n    q!=0\n    p^2=a*q^2\n    =>:\n        sqrt(a)=p/q\n".into(),
        "sqrt(4)=(-2)/1".into(),
        "sqrt(-1)=1/1".into(),
        "sqrt(i)=1/1".into(),
        "sqrt(2)=1/0".into(),
        "forall p,q R:\n    p^2=2*q^2\n".into(),
    ] {
        check(&mut runtime(), &source, false);
    }
}

#[test]
fn sqrt_quotient_square_retains_checked_source_and_locale_output() {
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = check(&mut rt, POSITIVE, true);
        let detailed = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let key = |english| crate::json_output::json_keys::localize_key(english, language);
        let rule = named_rule(&detailed, &key("rule"))
            .unwrap_or_else(|| panic!("{language:?}: {}", detailed.stringify_pretty()));
        let source = rule
            .as_object()
            .unwrap()
            .get(&key("quotient_equation"))
            .unwrap();
        assert_eq!(
            source
                .as_object()
                .unwrap()
                .get(&key("verification_result"))
                .unwrap()
                .as_str()
                .unwrap(),
            "accepted"
        );
        let source = source.stringify_pretty();
        assert!(
            source.contains("sqrt (a)") && source.contains(&key("cite_fact_id")),
            "{source}"
        );
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(!normal.contains("unsupported"), "{language:?}: {normal}");
    }
}

#[test]
fn sqrt_quotient_square_respects_search_ceiling_and_failure_rollback() {
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(POSITIVE, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("forall");
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
    ] {
        assert!(rt
            .verify_fact(&fact, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let bad = POSITIVE.replace("p^2=a*q^2", "p^2=(a+1)*q^2");
    check(&mut rt, &bad, false);
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    check(&mut rt, "0=1", false);
    check(&mut rt, POSITIVE, true);
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

fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
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
    rule_key: &str,
) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get(rule_key).and_then(|v| v.as_str().ok()) == Some("SqrtQuotientSquare") {
                return Some(value.clone());
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|k| named_rule(fields.get(&k).unwrap(), rule_key))
        }
        JsonValue::Array(items) => items.iter().find_map(|item| named_rule(item, rule_key)),
        _ => None,
    }
}
