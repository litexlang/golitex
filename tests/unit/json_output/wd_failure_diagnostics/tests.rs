use crate::prelude::*;

fn field<'a>(value: &'a JsonValue, key: &str, language: OutputLanguage) -> &'a JsonValue {
    value
        .as_object()
        .unwrap()
        .get(&crate::json_output::json_keys::localize_key(key, language))
        .unwrap_or_else(|| panic!("missing {key}: {value:?}"))
}

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language,
    })
}

#[test]
fn audited_failure_categories_and_obligations_survive_both_profiles() {
    let cases: &[(&str, &str)] = &[
        ("have_value_wd", "have badValue R = 1 / 0"),
        ("let_value_wd", "let badAlias = 1 / 0"),
        ("have_membership_control", "have badNatural N = -1"),
        ("have_carrier_wd", "have badMember {1 / 0}"),
        ("have_nonempty_control", "have noMember {}"),
        (
            "witness_value_wd",
            "witness exist w R st {w = w} from 1 / 0",
        ),
        ("by_def_goal_wd", "by def (1 / 0) $in R"),
        (
            "struct_field_wd_two_fields",
            "struct BadField:\n    value {1 / 0}\n    spare R",
        ),
        (
            "struct_law_wd",
            "struct BadLaw:\n    x R\n    y R\n    <=>:\n        1 / x = 1 / x",
        ),
        ("prop_law_wd", "prop BadProp(x R):\n    1 / x = 1 / x"),
        ("fn_body_wd", "have fn badReciprocal(x R) R = 1 / x"),
        (
            "claim_goal_wd_with_body",
            "claim:\n    ? forall x R:\n        1 / x = 1 / x\n    1 = 1",
        ),
        (
            "claim_body_have_wd",
            "claim:\n    ? 1 = 1\n    have innerBad R = 1 / 0",
        ),
        (
            "claim_body_fact_wd",
            "claim:\n    ? 1 = 1\n    1 / 0 = 1 / 0",
        ),
        ("exist_wd_control", "exist x R st {1 / x = 1 / x}"),
        ("or_wd_control", "1 = 1 or 1 / 0 = 1 / 0"),
        ("chain_wd_control", "1 = 1 / 0 = 2"),
        (
            "forall_iff_conclusion_wd",
            "forall x R:\n    =>:\n        x = x\n    <=>:\n        1 / x = 1 / x",
        ),
        ("not_forall_wd", "not forall x R:\n    1 / x = 1 / x"),
        (
            "by_for_goal_wd",
            "by for:\n    ? forall n range(0, 3) => 1 / n = 1 / n\n    n = n",
        ),
        (
            "thm_goal_wd",
            "thm badTheorem:\n    ? forall x R:\n        1 / x = 1 / x",
        ),
        ("eval_wd_control", "eval 1 / 0"),
        (
            "have_exist_wd",
            "have chosen R:\n    1 / chosen = 1 / chosen",
        ),
        (
            "obtain_source_wd",
            "obtain chosen from exist x R st {1 / x = 1 / x}",
        ),
        (
            "have_fn_exist_wd",
            "have fn selectBad by exist!:\n    ? forall x R:\n        exist! y R st {y = 1 / x}",
        ),
        ("witness_set_wd", "witness $is_nonempty_set({1 / 0}) from 1"),
        ("forall_wd_baseline", "forall x R => 1 / x = 1 / x"),
        ("forall_proof_control", "forall x R => x = x + 1"),
        ("have_positive", "have goodValue R = 1 / 2"),
        (
            "forall_guarded_positive",
            "forall x R:\n    x != 0\n    =>:\n        1 / x = 1 / x",
        ),
        (
            "guarded_fn_positive",
            "have fn reciprocal(x R: x != 0) R = 1 / x",
        ),
        ("fn_call_guard_wd", "reciprocal(0) = reciprocal(0)"),
        ("fn_call_type_wd", "reciprocal({1}) = reciprocal({1})"),
        ("tuple_index_wd", "(1, 2)(3) = (1, 2)(3)"),
        ("ln_domain_wd", "ln(0) = ln(0)"),
        ("noncallable_wd", "1(2) = 1(2)"),
        ("nested_child_wd", "1 + 1 / 0 = 1"),
        ("failed_name_reuse_positive", "have badValue R = 2"),
        ("witness_positive", "witness exist w R st {w = w} from 1"),
        ("by_def_positive", "by def {1} $subset {1}"),
        (
            "struct_positive",
            "struct BadField:\n    value R\n    spare R",
        ),
    ];

    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(language);
        for (label, source) in cases {
            let run = rt.run_litex_code(source).unwrap();
            assert!(
                run.session_error.is_none(),
                "{label}: {:?}",
                run.session_error
            );
            let positive = label.ends_with("positive");
            assert_eq!(run.success, positive, "{label}");
            let result = &run.statement_results[0];
            let normal = crate::json_output::project_stmt_normal(result, &rt);
            let detailed = crate::json_output::project_stmt_detailed(result, &rt);
            if positive {
                assert!(
                    detailed
                        .as_object()
                        .unwrap()
                        .get(&crate::json_output::json_keys::localize_key(
                            "diagnostic",
                            language
                        ))
                        .is_none(),
                    "{label}: success must not inherit speculative failure"
                );
                continue;
            }
            let normal_diag = field(
                field(&normal, "why_failed", language),
                "diagnostic",
                language,
            );
            let detailed_diag = field(&detailed, "diagnostic", language);
            assert_eq!(
                normal_diag, detailed_diag,
                "{label}: same actual cause in both profiles"
            );
            let expected = match *label {
                "have_membership_control" => "membership",
                "have_nonempty_control" => "nonempty",
                "forall_proof_control" => "proof_search",
                _ => "well_defined",
            };
            assert_eq!(
                field(normal_diag, "category", language).as_str(),
                Ok(expected),
                "{label}: {normal_diag:?}"
            );
            if matches!(
                *label,
                "forall_wd_baseline"
                    | "forall_iff_conclusion_wd"
                    | "struct_law_wd"
                    | "prop_law_wd"
                    | "fn_body_wd"
                    | "have_fn_exist_wd"
            ) {
                assert_eq!(
                    field(normal_diag, "expression", language).as_str(),
                    Ok("(1 / x)"),
                    "{label}"
                );
                assert_eq!(
                    field(normal_diag, "obligation", language).as_str(),
                    Ok("x != 0"),
                    "{label}"
                );
            }
            if matches!(
                *label,
                "have_value_wd"
                    | "let_value_wd"
                    | "have_carrier_wd"
                    | "witness_value_wd"
                    | "by_def_goal_wd"
                    | "struct_field_wd_two_fields"
                    | "claim_body_have_wd"
                    | "claim_body_fact_wd"
                    | "or_wd_control"
                    | "nested_child_wd"
                    | "witness_set_wd"
            ) {
                assert_eq!(
                    field(normal_diag, "expression", language).as_str(),
                    Ok("(1 / 0)"),
                    "{label}"
                );
                assert_eq!(
                    field(normal_diag, "obligation", language).as_str(),
                    Ok("0 != 0"),
                    "{label}"
                );
            }
            for key in ["stores", "infers"] {
                assert!(
                    field(&normal, key, language).as_array().unwrap().is_empty(),
                    "{label}"
                );
            }
        }
    }
}

#[test]
fn category_is_stable_and_message_and_keys_follow_every_locale() {
    for language in [
        OutputLanguage::English,
        OutputLanguage::Chinese,
        OutputLanguage::ChineseTraditional,
        OutputLanguage::French,
        OutputLanguage::Russian,
        OutputLanguage::Spanish,
        OutputLanguage::Arabic,
        OutputLanguage::Japanese,
        OutputLanguage::Korean,
        OutputLanguage::Vietnamese,
    ] {
        let mut rt = runtime(language);
        for (source, expected) in [
            ("have a R = 1 / 0", "well_defined"),
            ("have a N = -1", "membership"),
            ("have a {}", "nonempty"),
        ] {
            let run = rt.run_litex_code(source).unwrap();
            assert!(!run.success && run.session_error.is_none());
            let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
            let diagnostic = field(
                field(&normal, "why_failed", language),
                "diagnostic",
                language,
            );
            assert_eq!(
                field(diagnostic, "category", language).as_str(),
                Ok(expected)
            );
            assert!(!field(diagnostic, "message", language)
                .as_str()
                .unwrap()
                .is_empty());
            assert_eq!(
                field(field(&normal, "why_failed", language), "message", language),
                field(diagnostic, "message", language)
            );
        }
    }
}

#[test]
fn rejected_definition_rolls_back_and_session_keeps_previous_facts() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code("have saved R = 2").unwrap().success);
    let before = rt
        .execution_environments_stack
        .iter()
        .map(|e| {
            (
                e.facts.facts_by_id.len(),
                e.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect::<Vec<_>>();
    let run = rt.run_litex_code("have retry R = 1 / 0").unwrap();
    assert!(!run.success && run.session_error.is_none());
    for _ in 0..2 {
        crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    }
    let after = rt
        .execution_environments_stack
        .iter()
        .map(|e| {
            (
                e.facts.facts_by_id.len(),
                e.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        before, after,
        "failure and projection must not publish facts or WD cache entries"
    );
    assert!(rt.run_litex_code("have retry R = saved").unwrap().success);
    assert!(rt.run_litex_code("saved = 2").unwrap().success);
}

#[test]
fn witnesses_and_explicit_proofs_keep_the_failure_purpose() {
    for (source, category, obligation) in [
        (
            "witness exist x {1} st {x = 1} from 0",
            "membership",
            "0 $in {1}",
        ),
        (
            "witness $is_nonempty_set({1}) from 0",
            "membership",
            "0 $in {1}",
        ),
        (
            "witness exist x R st {x = 1} from 0",
            "proof_search",
            "0 = 1",
        ),
        ("witness exist x R st {x = x} from 0, 1", "arity", ""),
        (
            "by enumerate finite_set:\n    ? forall x {0, 1} => 1 / x = 1 / x\n    x = x",
            "well_defined",
            "x != 0",
        ),
        (
            "by for:\n    ? forall x range(0, 2) => x = x + 1\n    x = x",
            "proof_search",
            "0 = (0 + 1)",
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            !run.success && run.session_error.is_none(),
            "{source}: {:?}",
            run.session_error
        );
        let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
        let diagnostic = field(
            field(&normal, "why_failed", OutputLanguage::English),
            "diagnostic",
            OutputLanguage::English,
        );
        assert_eq!(
            diagnostic,
            field(&detailed, "diagnostic", OutputLanguage::English),
            "{source}"
        );
        assert_eq!(
            field(diagnostic, "category", OutputLanguage::English).as_str(),
            Ok(category),
            "{source}"
        );
        if !obligation.is_empty() {
            assert_eq!(
                field(diagnostic, "obligation", OutputLanguage::English).as_str(),
                Ok(obligation),
                "{source}"
            );
        }
    }
}

#[test]
fn summary_keeps_or_branch_and_proof_body_locations_in_the_evidence() {
    let language = OutputLanguage::English;
    let mut rt = runtime(language);
    let run = rt.run_litex_code("1 = 1 or 1 / 0 = 1 / 0").unwrap();
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let branch = field(field(&detailed, "verify", language), "failure", language);
    assert_eq!(field(branch, "phase", language).as_str(), Ok("branch"));
    assert_eq!(field(branch, "index", language), &JsonValue::Number(1.0));
    let run = rt
        .run_litex_code("claim:\n    ? 1 = 1\n    1 = 1\n    have a R = 1 / 0")
        .unwrap();
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let failure = field(&detailed, "failure", language);
    assert_eq!(field(failure, "phase", language).as_str(), Ok("proof_body"));
    assert_eq!(
        field(failure, "step_index", language),
        &JsonValue::Number(1.0)
    );
    assert_eq!(
        field(
            field(&detailed, "diagnostic", language),
            "obligation",
            language
        )
        .as_str(),
        Ok("0 != 0")
    );
}

#[test]
fn explicit_definition_failure_is_not_mistaken_for_missing_definition_or_wd() {
    let language = OutputLanguage::English;
    let mut rt = runtime(language);
    let run = rt.run_litex_code("by def {1} $subset {2}").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let diagnostic = field(
        field(&normal, "why_failed", language),
        "diagnostic",
        language,
    );
    assert_eq!(diagnostic, field(&detailed, "diagnostic", language));
    assert_eq!(
        field(diagnostic, "category", language).as_str(),
        Ok("proof_search")
    );
    assert_eq!(
        field(field(&detailed, "failure", language), "phase", language).as_str(),
        Ok("definition_requirement")
    );
    assert!(field(diagnostic, "obligation", language)
        .as_str()
        .unwrap()
        .contains("{2}"));
    assert!(rt.run_litex_code("by def {1} $subset {1}").unwrap().success);
}
