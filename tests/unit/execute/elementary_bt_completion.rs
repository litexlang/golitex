use crate::prelude::*;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
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

#[test]
fn run_examples_elementary_bt_completion() {
    check(
        &mut runtime(OutputLanguage::English),
        include_str!(
            "../../../examples/proof_nodes/atomic/by_builtin_rule/elementary_bt_completion.lit"
        ),
        true,
    );
}

#[test]
fn elementary_bt_completion_rejects_false_missing_premise_and_invalid_domain_cases() {
    for source in [
        "forall x,y,z R:\n    min(min(x,y),z)=max(x,min(y,z))",
        "min(1,2)+max(1,2)=1+2+1",
        "min(1,2)*max(1,2)=1+2",
        "forall x,y,z R:\n    min(x+z,y+z)=min(x,y)",
        "max(-1,-2)=min(1,2)",
        "forall x R,n Z:\n    n<=x\n    x<=n+1\n    =>:\n        floor(x)=n",
        "forall x R,n Z:\n    n-1<=x\n    x<=n\n    =>:\n        ceil(x)=n",
        "forall x R,n Z:\n    n<=x\n    =>:\n        floor(x)=n",
        "forall x R,n Z:\n    x<n+1\n    =>:\n        floor(x)=n",
        "forall x R,n Z:\n    x<=n\n    =>:\n        ceil(x)=n",
        "forall x R,n Z:\n    n-1<x\n    =>:\n        ceil(x)=n",
        "forall x,n R:\n    n<=x\n    x<n+1\n    =>:\n        floor(x)=n",
        "floor(0.6+0.6)<=floor(0.6)+floor(0.6)",
        "ceil(0.4)+ceil(0.4)<=ceil(0.4+0.4)",
        "gcd(2+3,3)=gcd(2,3)+1",
        "gcd(2*3,2*5)=gcd(3,5)",
        "gcd((-2)*3,(-2)*5)=(-2)*gcd(3,5)",
        "gcd(0,0)=0",
        "forall a,k R,m N+:\n    (a+k*m)%m=a%m",
        "(1+(1/2)*2)%2=1%2",
        "(2+1)%3=2%3",
        "forall d N+,a,b Z:\n    $dvd(a,d)\n    =>:\n        $dvd(a+b,d)",
        "forall d N+,a,b Z:\n    $dvd(b,d)\n    =>:\n        $dvd(a-b,d)",
        "forall d N+,a,k Z:\n    $dvd(k*a,d)",
        "forall d N+,a Z,k R:\n    $dvd(a,d)\n    =>:\n        $dvd(k*a,d)",
        "$dvd((1/2)*2,2)",
        "$dvd(2+2,0)",
        "forall d N+,a,b,u,v Z:\n    $dvd(a,d)\n    =>:\n        $dvd(u*a+v*b,d)",
        "abs(abs(2)-abs(1))<abs(2-1)",
        "forall x,y C:\n    abs(abs(x)-abs(y))<=abs(x-y)",
        "cart({1},union({2},{3}))=intersect(cart({1},{2}),cart({1},{3}))",
        "power_set(union({1},{2}))=union(power_set({1}),power_set({2}))",
    ] {
        check(&mut runtime(OutputLanguage::English), source, false);
    }
}

#[test]
fn elementary_bt_completion_certificates_and_locales() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = check(
            &mut rt,
            include_str!(
                "../../../examples/proof_nodes/atomic/by_builtin_rule/elementary_bt_completion.lit"
            ),
            true,
        );
        let detail =
            crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
        for rule in [
            "MinAssociative",
            "MaxAssociative",
            "MinMaxSum",
            "MinMaxProduct",
            "MinTranslation",
            "MaxNegation",
            "FloorCharacterization",
            "CeilCharacterization",
            "GcdAddArgument",
            "GcdNegation",
            "GcdPositiveScale",
            "RemainderIntegerShift",
            "CartesianUnion",
            "PowerSetIntersection",
            "FloorSumLowerBound",
            "FloorSumUpperBound",
            "CeilSumUpperBound",
            "RealReverseTriangle",
            "DvdAdd",
            "DvdSubtract",
            "DvdScale",
            "DvdLinearCombination",
        ] {
            assert!(detail.contains(rule), "missing {rule}: {detail}");
        }
        for field in [
            "integer",
            "weak_bound",
            "strict_bound",
            "factor_positive",
            "multiplier_integer",
            "first_divisibility",
            "second_divisibility",
            "first_coefficient_integer",
            "second_coefficient_integer",
        ] {
            let localized = crate::json_output::json_keys::localize_key(field, language);
            assert!(detail.contains(&localized), "missing {field}: {detail}");
        }
        assert!(
            detail.contains(&crate::json_output::json_keys::localize_key(
                "cite_fact_id",
                language
            )),
            "{detail}"
        );
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(
            !normal.contains("unreachable") && !normal.contains("unsupported"),
            "{normal}"
        );
    }
}

#[test]
fn elementary_bt_completion_failed_search_is_read_only_and_session_survives() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have x,y R", true);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("abs(abs(x)-abs(y))<abs(x-y)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    let count = rt.top_exec_env().facts.facts_by_id.len();
    assert!(rt
        .verify_fact(&fact, VerifyState::top_level())
        .unwrap()
        .is_failed());
    assert_eq!(count, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, "abs(abs(x)-abs(y))<=abs(x-y)", true);
    check(&mut rt, "x=x", true);
}

#[test]
fn elementary_bt_completion_reading_retains_premise_children() {
    let result = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(
            include_str!(
                "../../../examples/proof_nodes/atomic/by_builtin_rule/elementary_bt_completion.lit"
            )
            .into(),
        ),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let text = result.document.stringify_pretty();
    for value in [
        "FloorCharacterization",
        "strict_bound",
        "DvdLinearCombination",
        "first_divisibility",
        "second_divisibility",
        "RealReverseTriangle",
    ] {
        assert!(text.contains(value), "missing {value}");
    }
    assert_eq!(
        result
            .document
            .as_object()
            .unwrap()
            .get("diagnostics")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        0
    );
}
