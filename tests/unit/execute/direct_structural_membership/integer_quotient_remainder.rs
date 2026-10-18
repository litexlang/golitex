use crate::prelude::*;

const PREFIX: &str = "have k Z\nhave a Z = 2*k\na%2 = (2*k)%2 = 0\n";

#[test]
fn integer_quotient_remainder_positive_composition_and_full_irrationality() {
    check(
        &mut runtime(),
        include_str!(
            "../../../../examples/proof_nodes/atomic/direct_integer_quotient_zero_remainder.lit"
        ),
        true,
    );
    for source in [
        "forall a,b Z:\n    b!=0\n    a%b=0\n    =>:\n        (a/b)^2 $in Z\n        a/b + (a/b)^2 $in Z\n",
        "forall a,b Z:\n    b!=0\n    0=a%b\n    =>:\n        -((a/b)^2) $in Z\n",
        "forall a,b Z:\n    b<0\n    b!=0\n    a%b=0\n    =>:\n        (b*(a/b)^2)%b=0\n",
        "forall p Z:\n    p%2=0\n    =>:\n        (2*(p/2)^2)%2=0\n",
    ] {
        check(&mut runtime(), source, true);
    }
}

#[test]
fn integer_quotient_remainder_rejects_missing_false_and_bad_domain_premises() {
    for source in [
        "forall a,b Z:\n    b!=0\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a,b Z:\n    b!=0\n    a%b=1\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a,b Z:\n    a%b=0\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a,b R:\n    b!=0\n    a%b=0\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a,b Z:\n    b!=0\n    a%b=0\n    =>:\n        a/b $in N\n",
        "forall a,b Z:\n    b!=0\n    a%b=0\n    =>:\n        a/b $in N+\n",
        "1/2 $in Z",
        "1/0 $in Z",
        "i $in Z",
        "(2*(1/2))%2=0",
        "not sqrt(4) $in Q",
    ] {
        check(&mut runtime(), source, false);
    }
}

#[test]
fn integer_quotient_remainder_direct_is_read_only_and_scope_bound() {
    let mut rt = runtime();
    check(&mut rt, "have k Z\nhave a Z=2*k", true);
    let goal = parse_fact(&mut rt, "(a/2)^2 $in Z");
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let (_, _closed_env) = rt
        .run_in_local_env_and_take_env(|rt| {
            let run = rt.run_litex_code("a%2=(2*k)%2=0")?;
            assert!(run.success);
            let count = rt.top_exec_env().facts.facts_by_id.len();
            assert!(!rt
                .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))?
                .is_failed());
            assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
            let modulo = parse_fact(rt, "(2*(a/2)^2)%2=0");
            assert!(rt
                .verify_fact(&modulo, VerifyState::new(VerifyStateLevel::Direct))?
                .is_failed());
            assert!(!rt
                .verify_fact(&modulo, VerifyState::top_level())?
                .is_failed());
            Ok(())
        })
        .unwrap();
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    check(&mut rt, "0=1", false);
}

#[test]
fn integer_quotient_remainder_keeps_citations_and_locale_output() {
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
        check(&mut rt, PREFIX, true);
        let run = check(&mut rt, "(a/2)^2 $in Z", true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let key = crate::json_output::json_keys::localize_key("kind", language);
        let node = exact_node(&detail, &key).expect("actual exact integer division certificate");
        let text = node.stringify_pretty();
        assert!(
            text.contains("zero_remainder") && text.contains("enclosing_object_wd"),
            "{text}"
        );
        assert!(
            text.contains(&crate::json_output::json_keys::localize_key(
                "cite_fact_id",
                language
            )),
            "{text}"
        );
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(!normal.contains("unsupported"), "{normal}");
    }
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
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
fn parse_fact(rt: &mut Runtime, source: &str) -> Fact {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    fact
}
fn exact_node(
    value: &crate::knowledge_base::JsonValue,
    key: &str,
) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get(key).and_then(|v| v.as_str().ok()) == Some("exact_integer_div") {
                return Some(value.clone());
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|k| exact_node(fields.get(&k).unwrap(), key))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| exact_node(v, key)),
        _ => None,
    }
}
