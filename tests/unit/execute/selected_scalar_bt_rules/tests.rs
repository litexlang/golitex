use crate::prelude::*;

const SUB: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/subtraction_order_pairs.lit"
));
const ABS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/abs_square_radius.lit"
));
const DIV: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/quotient_scalar_upper_bound.lit"
));
const STRICT_DIV: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/quotient_scalar_strict_upper_bound.lit"
));
const EXACT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/exact_integer_quotient.lit"
));
const NONZERO: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/atomic/by_builtin_rule/abs_nonzero_denominator_consumer.lit"
));

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
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
fn named_rule(
    value: &crate::knowledge_base::JsonValue,
    name: &str,
) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get("rule").and_then(|v| v.as_str().ok()) == Some(name) {
                return Some(value.clone());
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|k| named_rule(fields.get(&k).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| named_rule(v, name)),
        _ => None,
    }
}

#[test]
fn run_examples_selected_scalar_bt_tracers() {
    for source in [SUB, ABS, DIV, STRICT_DIV, EXACT, NONZERO] {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}
#[test]
fn scalar_rules_retain_checked_premise_citations() {
    for (source, name, fields) in [
        (
            SUB,
            "SubtractionOrderPairs",
            &["minuend_order", "subtrahend_order"][..],
        ),
        (
            ABS,
            "AbsSquareRadius",
            &["radius_nonnegative", "squared_order"][..],
        ),
        (
            DIV,
            "QuotientScalarUpperBound",
            &["denominator_positive", "product_bound"][..],
        ),
        (
            STRICT_DIV,
            "QuotientScalarStrictUpperBound",
            &["denominator_positive", "product_bound"][..],
        ),
        (
            EXACT,
            "ExactIntegerQuotient",
            &[
                "numerator_integer",
                "denominator_integer",
                "denominator_nonzero",
                "zero_remainder",
            ][..],
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
                evidence.contains("\"verification_result\": \"accepted\""),
                "{name}.{field}: {evidence}"
            );
        }
    }
}
#[test]
fn reverse_written_sources_compound_operands_and_signed_divisors() {
    for source in [
        "forall a,b,c,d R:\n    b>=a\n    d>=c\n    =>:\n        b-c>=a-d\n",
        "forall x,r R:\n    0<=r\n    r^2>=x^2\n    =>:\n        r>=abs(x)\n",
        "forall a,b,M R:\n    0<b\n    b*M>=a\n    =>:\n        M>=a/b\n",
        "forall a,b,M R:\n    0<b\n    b*M>a\n    =>:\n        M>a/b\n",
        "forall a,b Z:\n    b<0\n    b!=0\n    a%b=0\n    =>:\n        a/b $in Z\n",
        "forall a,b Z:\n    b!=0\n    0=a%b\n    =>:\n        a/b $in Z\n",
        "forall x,r R:\n    r>0\n    x^2<r^2\n    =>:\n        abs(x)<=r\n",
        "forall x,y,r R:\n    r>=0\n    (x-y)^2<=r^2\n    =>:\n        abs(x-y)<=r\n",
        "forall a,b,c,d R:\n    a<b\n    c<d\n    =>:\n        a-d<=b-c\n",
    ] {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}
#[test]
fn missing_false_sign_and_partial_domain_controls_reject() {
    for source in [
        "forall a,b,c,d R:\n    a<=b\n    =>:\n        a-d<=b-c\n",
        "forall a,b,c,d R:\n    c<=d\n    =>:\n        a-d<=b-c\n",
        "forall a,b,c,d R:\n    a<=b\n    c<=d\n    =>:\n        a-d<b-c\n",
        "forall x,r R:\n    x^2<=r^2\n    =>:\n        abs(x)<=r\n",
        "forall x,r R:\n    r>=0\n    x^2<=r^2\n    =>:\n        abs(x)<r\n",
        "abs(1)<=-2\n",
        "forall a,b,M R:\n    b<0\n    a<=M*b\n    =>:\n        a/b<=M\n",
        "forall a,b,M R:\n    b>0\n    a<=M*b\n    =>:\n        a/b<M\n",
        "forall a,b,M R:\n    b>0\n    =>:\n        a/b<=M\n",
        "1/0<=1\n",
        "forall a,b Z:\n    b!=0\n    =>:\n        a/b $in Z\n",
        "forall a,b R:\n    b!=0\n    =>:\n        a/b $in Z\n",
        "1/2 $in Z\n",
        "0/0 $in Z\n",
        "forall a,b Z:\n    b!=0\n    a%b=0\n    =>:\n        a/b $in N\n",
        "forall v R:\n    abs(v)!=0\n",
        "abs(0)!=0\n",
        "have z C\nabs(z)!=0\n",
    ] {
        check(&mut runtime(OutputLanguage::English), source, false);
    }
}
#[test]
fn restricted_permissions_and_failed_statement_isolation() {
    for source in [SUB, ABS, DIV, STRICT_DIV, EXACT] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
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
        assert!(!rt
            .verify_fact(&fact, VerifyState::top_level())
            .unwrap()
            .is_failed());
    }
    let mut rt = runtime(OutputLanguage::English);
    let before = rt.top_exec_env().facts.facts_by_id.len();
    check(&mut rt, "claim:\n    ? forall a,b,c,d R:\n        a<=b\n        c<=d\n        =>:\n            a-d<=b-c\n    a-d<=b-c\n    0=1\n", false);
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    check(&mut rt, SUB, true);
    check(&mut rt, SUB, true);
}
#[test]
fn all_locales_and_explicit_unsupported_lean_routes() {
    for language in OutputLanguage::ALL {
        for source in [SUB, ABS, DIV, STRICT_DIV, EXACT, NONZERO] {
            let mut rt = runtime(language);
            let run = check(&mut rt, source, true);
            let normal =
                crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
            assert!(!normal.contains("unsupported"), "{language:?}: {normal}");
        }
    }
    for source in [SUB, ABS, DIV, STRICT_DIV, EXACT] {
        let mut rt = runtime(OutputLanguage::English);
        let run = check(&mut rt, source, true);
        assert!(
            crate::compile_to_lean::compile_run(&run, rt, "selected_scalar").is_err(),
            "No new Lean adapter"
        );
    }
}
