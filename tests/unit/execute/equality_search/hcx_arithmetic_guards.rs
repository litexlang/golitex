use crate::prelude::*;

const VALID: [&str; 5] = [
    "forall m Z:\n    (-1)^(2*m+1)=-1\n",
    "forall n N+, k Z:\n    (n*k)%n=0\n",
    "forall a,b R:\n    re(a+b*i)=a\n",
    "forall a,b R:\n    img(a+b*i)=b\n",
    "forall a,b R:\n    C_abs(a+b*i)^2=a^2+b^2\n",
];

#[test]
fn run_examples_hcx_arithmetic_guard_tracers() {
    for source in [
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/product_mod_factor_zero_integer_guard.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/minus_one_odd_natural_power_integer_guard.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/re_of_real_plus_imag_scaled_real_guards.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/img_of_real_plus_imag_scaled_real_guards.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/complex_abs_squared_of_rect_form_real_guards.lit"),
    ] {
        check(&mut runtime(), source, true);
    }
}

#[test]
fn original_contradictions_reject_only_the_false_steps() {
    for (source, expected) in [
        (
            "(-1)^(2*(1/2)+1)=-1\n(-1)^(2*(1/2)+1)=1\n1=-1\n1!=-1",
            vec![false, true, false, true],
        ),
        (
            "(2*(1/2))%2=0\n(2*(1/2))%2=1\n0=1\n0!=1",
            vec![false, true, false, true],
        ),
        (
            "re(i+i)=i\nre(i+i)=0\ni=0\ni!=0",
            vec![false, true, false, true],
        ),
        (
            "img(i+i)=1\nimg(i+i)=2\n1=2\n1!=2",
            vec![false, true, false, true],
        ),
        (
            "C_abs(i+1*i)^2=i^2+1^2\nC_abs(i+1*i)^2=4\ni^2+1^2=0\n4=0\n4!=0",
            vec![false, true, true, false, true],
        ),
    ] {
        let mut rt = runtime();
        let run = check(&mut rt, source, false);
        let actual: Vec<bool> = run
            .statement_results
            .iter()
            .map(|s| !s.is_failed())
            .collect();
        assert_eq!(actual, expected, "{source}");
    }
}

#[test]
fn false_universals_and_missing_coefficient_premises_reject() {
    for source in [
        "forall m R:\n    2*m+1 $in Z\n    =>:\n        (-1)^(2*m+1)=-1\n",
        "forall k R:\n    2*k $in Z\n    =>:\n        (2*k)%2=0\n",
        "forall a,b C:\n    re(a+b*i)=a\n",
        "forall a,b C:\n    img(a+b*i)=b\n",
        "forall a,b C:\n    C_abs(a+b*i)^2=a^2+b^2\n",
        "forall a R,b C:\n    re(a+b*i)=a\n",
        "forall a C,b R:\n    re(a+b*i)=a\n",
        "forall a R,b C:\n    img(a+b*i)=b\n",
        "forall a C,b R:\n    img(a+b*i)=b\n",
        "forall a R,b C:\n    C_abs(a+b*i)^2=a^2+b^2\n",
        "forall a C,b R:\n    C_abs(a+b*i)^2=a^2+b^2\n",
    ] {
        check(&mut runtime(), source, false);
    }
}

#[test]
fn false_operand_orders_and_complex_second_coefficients_reject() {
    for source in [
        "(-1)^((1/2)*2+1)=-1",
        "-1=(-1)^(2*(1/2)+1)",
        "((1/2)*2)%2=0",
        "0=(2*(1/2))%2",
        "re(0+i*i)=0",
        "img(0+i*i)=i",
        "C_abs(0+i*i)^2=0^2+i^2",
        "i=re(i+i)",
        "1=img(i+i)",
        "i^2+1^2=C_abs(i+1*i)^2",
        "(2*1)%0=0",
        "(-1)^(2*(1/3)+1)=-1",
    ] {
        check(&mut runtime(), source, false);
    }
}

#[test]
fn valid_domains_orientations_and_negative_integer_parameters_pass() {
    for source in VALID.into_iter().chain([
        "forall m N:\n    (-1)^(2*m+1)=-1\n",
        "forall m Z:\n    -1=(-1)^(m*2+1)\n",
        "forall n Z,k Z:\n    n!=0\n    =>:\n        (k*n)%n=0\n        0=(n*k)%n\n",
        "forall a,b R:\n    a=re(b*i+a)\n    b=img(i*b+a)\n    b^2+a^2=C_abs(a+i*b)^2\n",
        "(-1)^(2*(-2)+1)=-1",
        "(-3*(-2))%(-3)=0",
    ]) {
        check(&mut runtime(), source, true);
    }
}

#[test]
fn successful_rule_nodes_retain_actual_membership_citations() {
    for (prefix, goal, name, fields) in [
        (
            "have m Z",
            "(-1)^(2*m+1)=-1",
            "MinusOneOddNaturalPower",
            &[("parameter_integer", "m $in Z")][..],
        ),
        (
            "have n N+, k Z",
            "(n*k)%n=0",
            "DvdProductFactor",
            &[("multiplier_integer", "k $in Z")][..],
        ),
        (
            "have a,b R",
            "re(a+b*i)=a",
            "ReOfRealPlusImagScaled",
            &[
                ("real_coefficient_real", "a $in R"),
                ("imaginary_coefficient_real", "b $in R"),
            ][..],
        ),
        (
            "have a,b R",
            "img(a+b*i)=b",
            "ImgOfRealPlusImagScaled",
            &[
                ("real_coefficient_real", "a $in R"),
                ("imaginary_coefficient_real", "b $in R"),
            ][..],
        ),
        (
            "have a,b R",
            "C_abs(a+b*i)^2=a^2+b^2",
            "ComplexAbsSquaredOfRectForm",
            &[
                ("real_coefficient_real", "a $in R"),
                ("imaginary_coefficient_real", "b $in R"),
            ][..],
        ),
    ] {
        let mut rt = runtime();
        check(&mut rt, prefix, true);
        let run = check(&mut rt, goal, true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let rule = named_rule(&detail, name).expect(name);
        for (field, fact) in fields {
            let evidence = rule
                .as_object()
                .unwrap()
                .get(field)
                .expect(field)
                .stringify_pretty();
            assert!(
                evidence.contains("\"verification_result\": \"accepted\""),
                "{name}.{field}: {evidence}"
            );
            assert!(
                evidence.contains(fact) && evidence.contains("cite_fact_id"),
                "{name}.{field}: {evidence}"
            );
        }
    }
}

#[test]
fn restricted_search_does_not_reenable_rules_and_failures_do_not_publish() {
    for source in VALID {
        let mut rt = runtime();
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
            assert!(
                rt.verify_fact(&fact, VerifyState::new(level))
                    .unwrap()
                    .is_failed(),
                "{source}"
            );
        }
        assert!(
            !rt.verify_fact(&fact, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{source}"
        );
    }
    let mut rt = runtime();
    let before = rt.top_exec_env().facts.facts_by_id.len();
    for source in [
        "(2*(1/2))%2=0",
        "re(i+i)=i",
        "img(i+i)=1",
        "C_abs(i+i)^2=0",
        "0=1",
    ] {
        check(&mut rt, source, false);
        assert_eq!(
            rt.top_exec_env().facts.facts_by_id.len(),
            before,
            "{source}"
        );
    }
    check(&mut rt, "(2*(1/2))%2=1", true);
    check(&mut rt, "0=1", false);
}

#[test]
fn normal_locales_and_unsupported_lean_boundary_remain_explicit() {
    for language in OutputLanguage::ALL {
        for source in VALID {
            let mut rt = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            });
            let run = check(&mut rt, source, true);
            let normal =
                crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
            assert!(!normal.contains("unsupported"), "{language:?}: {normal}");
        }
    }
    for source in VALID {
        let mut rt = runtime();
        let run = check(&mut rt, source, true);
        assert!(
            crate::compile_to_lean::compile_run(&run, rt, "hcx_guards").is_err(),
            "No new Lean adapter for {source}"
        );
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
