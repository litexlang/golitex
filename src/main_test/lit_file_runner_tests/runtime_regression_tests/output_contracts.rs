use super::*;

#[test]
fn hidden_file_path_output_omits_source_fields() {
    let source_code = "x = 1";
    let path = "/private/tmp/litex-hidden-source-test.lit";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(path);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"source\""));
    assert!(!run_output.contains(path));
    assert!(run_output.contains("\"line\": 1"));
}

#[test]
fn normal_output_omits_empty_arrays_and_empty_strings() {
    let source_code = "do_nothing\nhave a R\nhave a R";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("normal_output_omits_empty_fields");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"store_facts\": []"));
    assert!(!run_output.contains("\"inside_results\": []"));
    assert!(!run_output.contains("\"message\": \"\""));
}

#[test]
fn detail_output_keeps_empty_arrays_and_empty_strings() {
    let source_code = "do_nothing\nhave a R\nhave a R";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("detail_output_keeps_empty_fields");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"store_facts\": []"));
    assert!(!run_output.contains("\"inside_results\": []"));
    assert!(!run_output.contains("\"message\": \"\""));
}

#[test]
fn run_summary_counts_direct_unproved_interfaces() {
    run_with_large_stack("run_summary_counts_direct_unproved_interfaces", || {
        let source_code = r#"
1 = 1
trust 1 = 0
trust have x R
abstract_prop summary_prop(x)
prop summary_concrete_prop(x R):
    x = x
axiom summary_axiom:
    ? forall y R:
        y = y
thm summary_theorem:
    ? forall y R:
        y = y
    y = y
claim:
    ? 1 = 1
    1 = 1
witness exist z R st {z = 1} from 1:
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("run_summary_counts");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let summary = RunSummary::from_run(&stmt_results, &runtime_error);
        let summary_output =
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error);

        assert!(
            runtime_error.is_none(),
            "summary fixture failed:\n{}",
            summary_output
        );
        assert_eq!(summary.direct_trust, 1);
        assert_eq!(summary.trusted_object_assumptions, 1);
        assert_eq!(summary.prop_definitions, 1);
        assert_eq!(summary.abstract_prop_definitions, 1);
        assert_eq!(summary.theorem_statements, 1);
        assert_eq!(summary.abstract_interfaces, 1);
        assert_eq!(summary.axioms, 1);
        assert!(summary_output.contains("\"output_type\": \"run summary\""));
        assert!(summary_output.contains("\"proof_method_counts\""));
        assert!(summary_output.contains("\"claim\""));
        assert!(!summary_output.contains("\"claim fact proof\""));
        assert!(!summary_output.contains("\"claim forall proof\""));
        assert!(summary_output.contains("\"witness\": 1"));
        assert!(!summary_output.contains("\"by_method_counts\""));
        assert!(!summary_output.contains("\"witness_counts\""));
        assert!(!summary_output.contains("\"existence\": 1"));
        assert!(!summary_output.contains("\"total\": 1"));
        assert!(summary_output.contains("\"main_environment\""));
        assert!(summary_output.contains("\"overview_counts\""));
        assert!(summary_output.contains("\"objects\""));
        assert!(summary_output.contains("\"props\""));
        assert!(summary_output.contains("\"environment_field_counts\""));
        assert!(summary_output.contains("\"map_keys\""));
        assert!(summary_output.contains("\"stored_items\""));
        assert!(summary_output.contains("\"known_fact_counts\""));
        assert!(summary_output.contains("\"known_facts\""));
        assert!(summary_output.contains("\"trust_summary\""));
        assert!(summary_output.contains("\"unproved_dependency_counts\""));
        assert!(!summary_output.contains("\"category_counts\""));
        assert!(!summary_output.contains("\"field_key_counts\""));
        assert!(!summary_output.contains("\"field_item_counts\""));
        assert!(!summary_output.contains("\"fact_origin_counts\""));
        assert!(!summary_output.contains("\"cache_fact_trust_dependency_counts\""));
        assert!(!summary_output.contains("\"theorem_trust_dependency_counts\""));
        assert!(!summary_output.contains("\"statement_type_counts\""));
        assert!(!summary_output.contains("\"output_type_counts\""));
        assert!(!summary_output.contains("\"stored_fact_reason_counts\""));
        assert!(!summary_output.contains("\"unique_equality_facts\""));
        assert!(!summary_output.contains("\"statements\""));
    });
}

#[test]
fn normal_output_projects_proof_level_inside_results() {
    run_with_large_stack("normal_output_projects_proof_level_inside_results", || {
        let source_code = r#"
sketch:
    1 = 1

claim:
    ? 1 = 1
    1 = 1

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

witness exist x R st {x = 1} from 1:
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("normal_output_folds_proof_trace");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "normal proof-trace fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof sketch\""));
        assert!(run_output.contains("\"type\": \"proved claim\""));
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert!(run_output.contains("\"type\": \"existence witness\""));
        assert_no_legacy_acceptance_field(&run_output, "normal");
        assert!(
            run_output.contains("\"inside_results\": ["),
            "normal output should retain one readable internal-statement tree:\n{}",
            run_output
        );
        assert!(run_output.contains("\"why_verified\": {"));
        assert!(!run_output.contains("\"phases\": {"));
        assert!(!run_output.contains("\"proof_steps\": ["));
    });
}

#[test]
fn output_styles_project_one_full_execution_trace() {
    let source_code = r#"
sketch:
    forall y R, z N:
        $is_set(y)
        $is_set(z)
    $is_set(1)
"#;
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("output_styles_project_full_trace");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);

    assert!(runtime_error.is_none());
    assert!(stmt_results[0].execution_trace().is_some());

    let (_, normal_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(normal_output.contains("\"inside_results\": ["));
    assert!(normal_output.contains("Every object is a set."));
    assert!(normal_output.contains("\"why_verified\": {"));
    assert!(!normal_output.contains("\"phases\": {"));
    assert!(!normal_output.contains("\"effects\": ["));

    runtime.set_output_style(OutputStyle::Compact);
    let (_, compact_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(compact_output.contains("\"type\": \"proof sketch\""));
    assert!(!compact_output.contains("\"inside_results\": ["));
    assert!(!compact_output.contains("\"why_verified\": {"));

    runtime.set_output_style(OutputStyle::Detailed);
    let (_, detailed_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(detailed_output.contains("\"inside_results\": ["));
    assert!(detailed_output.contains("\"phases\": {"));
    assert!(detailed_output.contains("\"affect_environment\": {"));
    assert!(detailed_output.contains("\"effects\": ["));
}

#[test]
fn normal_theorem_output_exposes_structured_proof_route() {
    run_with_large_stack(
        "normal_theorem_output_exposes_structured_proof_route",
        || {
            let source_code = r#"
thm theorem_trace_self_eq:
    ? forall x R:
        x = x
    x = x
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("normal_theorem_output_proof_route");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "normal theorem proof-route fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"theorem proof\""));
            assert!(run_output.contains("\"theorem_trace_self_eq\""));
            assert!(run_output.contains("\"parameters\": ["));
            assert!(run_output.contains("\"x\""));
            assert!(run_output.contains("\"assumptions\": ["));
            assert!(run_output.contains("\"conclusions\": ["));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal theorem output should expose its readable internal route:\n{}",
                run_output
            );
            assert!(!run_output.contains("\"proof_steps\": ["));
        },
    );
}

#[test]
fn detail_output_expands_proof_level_inside_results() {
    run_with_large_stack("detail_output_expands_proof_level_inside_results", || {
        let source_code = r#"
sketch:
    1 = 1

claim:
    ? 1 = 1
    1 = 1

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

witness exist x R st {x = 1} from 1:
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("detail_output_expands_proof_trace");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "detail proof-trace fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof sketch\""));
        assert!(run_output.contains("\"type\": \"proved claim\""));
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert!(run_output.contains("\"type\": \"existence witness\""));
        assert!(
            run_output.matches("\"inside_results\": [").count() >= 3,
            "detail output should expand available raw recursive inside_results:\n{}",
            run_output
        );
    });
}

#[test]
fn by_induc_output_uses_same_trace_for_normal_and_detail() {
    let source_code = r#"
abstract_prop p(a)
trust $p(0)
trust forall m Z:
    m >= 0
    $p(m)
    =>:
        $p(m + 1)
by induc n from 0:
    ? $p(n)

    ? from n = 0:
        $p(0)

    ? induc:
        $p(n + 1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("by_induc_normal_trace");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "normal by induc fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"proof by induction\""));
    assert!(
        run_output.contains("\"inside_results\": ["),
        "normal by induc output should retain its readable internal route:\n{}",
        run_output
    );

    let mut detail_runtime = Runtime::new_with_builtin_code();
    detail_runtime.new_file_path_new_env_new_name_scope("by_induc_detail_trace");
    detail_runtime.detail_output = true;
    let (detail_stmt_results, detail_runtime_error) =
        run_source_code(source_code, &mut detail_runtime);
    let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
        &detail_runtime,
        &detail_stmt_results,
        &detail_runtime_error,
        false,
    );

    assert!(
        detail_run_succeeded,
        "detail by induc fixture failed:\n{}",
        detail_run_output
    );
    assert!(detail_run_output.contains("\"type\": \"proof by induction\""));
    assert!(detail_run_output.contains("\"inside_results\": ["));
    assert!(detail_run_output.contains("\"statement\": \"$p(0)\""));
    assert!(
        detail_run_output.matches("\"type\": \"prop fact\"").count() >= 4,
        "detail by induc output should expand base/step proof and obligation checks:\n{}",
        detail_run_output
    );
    assert!(detail_run_output.contains("+ 1)"));
}

#[test]
fn witness_detail_output_keeps_proof_and_obligation_trace() {
    let source_code = r#"
witness exist x R st {x = 1} from 1:
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("witness_detail_output_keeps_trace");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "witness detail fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"existence witness\""));
    assert!(
        run_output.matches("\"statement\": \"1 = 1\"").count() >= 2,
        "witness detail output should include the proof step and the instantiated obligation:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"inside_results\": ["),
        "witness detail output should expand its proof trace:\n{}",
        run_output
    );
}

#[test]
fn witness_exist_unique_rejects_missing_uniqueness_proof() {
    let source_code = r#"
claim:
    ? exist! x R st {x = x}
    witness exist! x R st {x = x} from 0:
        0 = 0
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("witness_exist_unique_requires_uniqueness");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "witness exist! without uniqueness proof should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("witness exist!: failed to verify uniqueness obligation"),
        "the missing uniqueness obligation should be explicit:\n{}",
        run_output
    );
}

#[test]
fn witness_exist_unique_accepts_explicit_uniqueness_proof() {
    let source_code = r#"
claim:
    ? exist! x R st {x = 0}
    witness exist! x R st {x = 0} from 0:
        0 = 0
        claim:
            ? forall u, v R:
                u = 0
                v = 0
                =>:
                    u = v
            u = 0
            0 = v
            u = v
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("witness_exist_unique_with_uniqueness");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "witness exist! with a uniqueness proof should succeed:\n{}",
        run_output
    );
}

#[test]
fn builtin_citation_source_uses_safe_builtin_label() {
    let source_code = "have a, b R\na < b or a = b or a > b";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("builtin_citation_source");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "builtin citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"source_kind\": \"builtin\""));
    assert!(run_output.contains("\"source\": \"builtin_code\""));
    assert!(!run_output.contains("\"path\""));
}

#[test]
fn runner_success_returns_trace() {
    let (ok, output) = run_runner_for_code("1 + 1 = 2", "-runner-test", true);

    assert!(ok, "runner success run failed:\n{}", output);
    assert!(output.contains("\"runner\": \"litex-runner\""));
    assert!(output.contains("\"result\": \"success\""));
    assert!(output.contains("\"trace\""));
}

#[test]
fn runner_failure_returns_trace() {
    let (ok, output) = run_runner_for_code("1 = 0", "-runner-test", true);

    assert!(!ok, "runner unknown run should fail:\n{}", output);
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains("\\\"error_type\\\": \\\"VerifyError\\\""));
    assert!(output.contains("\\\"error_type\\\": \\\"UnknownError\\\""));
}

#[test]
fn runner_target_error_returns_message() {
    let (ok, output) = run_runner_for_file("does_not_exist.lit", true);

    assert!(!ok, "runner target error should fail:\n{}", output);
    assert!(output.contains("\"kind\": \"target_error\""));
    assert!(output.contains("could not read entry file"));
}

#[test]
fn runner_accepts_trust_as_normal_execution() {
    let (ok, output) = run_runner_for_code("trust 1 = 0", "-runner-test", true);

    assert!(ok, "runner should not reject trust statements:\n{}", output);
    assert!(output.contains("\"result\": \"success\""));
}

#[test]
fn runner_accepts_trust_have_as_normal_execution() {
    run_with_large_stack("runner_accepts_trust_have_as_normal_execution", || {
        let (ok, output) = run_runner_for_code("trust have x R", "-runner-test", true);

        assert!(
            ok,
            "runner should not reject trust have statements:\n{}",
            output
        );
        assert!(output.contains("\"result\": \"success\""));
    });
}

#[test]
fn zh_output_localizes_unproved_trust_labels() {
    let source_code = "abstract_prop tmp_rel(m, n)\ntrust exist! m, n R st {$tmp_rel(m, n)}\n";
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("zh_output_localizes_unproved_trust_labels");
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(run_succeeded, "Chinese output run failed:\n{}", run_output);
    assert!(run_output.contains("\"结果\": \"成功\""));
    assert!(run_output.contains("\"类型\": \"未经证明的假设\""));
    assert!(run_output.contains("\"语句\": \"trust exist! m, n R st {$tmp_rel("));
    assert!(!run_output.contains("\"result\": \"success\""));
}

#[test]
fn zh_output_localizes_citation_evidence_but_keeps_litex_statement() {
    let source_code = "prop is_one_tmp(t R):\n    t = 1\n\n$is_one_tmp(1)\n";
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "zh_output_localizes_citation_evidence_but_keeps_litex_statement",
    );
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "Chinese citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"验证依据\""));
    assert!(run_output.contains("\"类型\": \"引用 prop 定义\""));
    assert!(run_output.contains("\"被引用语句\": \"prop is_one_tmp(t R):\\n"));
    assert!(run_output.contains("\"语句\": \"$is_one_tmp(1)\""));
}

#[test]
fn zh_forall_output_uses_short_conclusions_and_compact_citation() {
    let source_code = r#"
prop can_be_divided_by_8(x Z):
    exist d Z st {x = 8 * d}

prop can_be_divided_by_2(x Z):
    exist d Z st {x = 2 * d}

claim:
    ? forall x Z:
        $can_be_divided_by_8(x)
        =>:
            $can_be_divided_by_2(x)
    obtain d from exist d Z st {x = 8 * d}
    witness exist e Z st {x = 2 * e} from 4 * d:
        x = 8 * d
        8 * d = 2 * (4 * d)

have d Z
have x Z = 8 * d
witness exist k Z st {x = 8 * k} from d:
    x = 8 * d
$can_be_divided_by_8(x)
$can_be_divided_by_2(x)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "zh_forall_output_uses_short_conclusions_and_compact_citation",
    );
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "Chinese forall output run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"结论\": ["));
    assert!(run_output.contains("\"类型\": \"引用 forall 事实\""));
    assert!(run_output.contains("\"被引用语句\": \"forall x Z:\\n    $can_be_divided_by_8(x)\\n    =>:\\n        $can_be_divided_by_2(x)\""));
    assert!(run_output.contains("\"验证依据\""));
    assert!(!run_output.contains("\"带验证的结论\""));
    assert!(!run_output.contains("\"原因\": \"推导事实\""));
    assert!(!run_output.contains("\"实例化\""));
    assert!(!run_output.contains("\"要求\""));
}

#[test]
fn zh_runner_localizes_wrapper_and_trace() {
    let (ok, output) = run_runner_for_code_with_language(
        "trust 1 = 1",
        "-runner-test",
        true,
        OutputLanguage::SimplifiedChinese,
    );

    assert!(ok, "Chinese runner should succeed:\n{}", output);
    assert!(output.contains("\"运行器\": \"litex-runner\""));
    assert!(output.contains("\"结果\": \"成功\""));
    assert!(output.contains("\"运行轨迹\""));
    assert!(output.contains("\\\"类型\\\": \\\"未经证明的假设\\\""));
}

#[test]
fn output_language_parses_supported_cli_codes() {
    let cases = vec![
        ("en", OutputLanguage::English),
        ("zh", OutputLanguage::SimplifiedChinese),
        ("zh-Hans", OutputLanguage::TraditionalChinese),
        ("ja", OutputLanguage::Japanese),
        ("ko", OutputLanguage::Korean),
        ("es", OutputLanguage::Spanish),
        ("fr", OutputLanguage::French),
        ("de", OutputLanguage::German),
        ("pt", OutputLanguage::Portuguese),
        ("ru", OutputLanguage::Russian),
        ("ar", OutputLanguage::Arabic),
        ("hi", OutputLanguage::Hindi),
        ("vi", OutputLanguage::Vietnamese),
        ("id", OutputLanguage::Indonesian),
    ];

    for (code, expected) in cases {
        assert_eq!(OutputLanguage::from_cli_lang(code), Ok(expected));
    }

    let err = OutputLanguage::from_cli_lang("xx").expect_err("xx should be unsupported");
    assert!(err.contains("en, zh, zh-Hans, ja, ko, es, fr, de, pt, ru, ar, hi, vi, id"));
}

#[test]
fn non_english_languages_localize_unproved_trust_labels() {
    let cases = vec![
        (
            OutputLanguage::SimplifiedChinese,
            "结果",
            "成功",
            "类型",
            "未经证明的假设",
            "语句",
            "事实",
            "原因",
            "未经证明的假设",
        ),
        (
            OutputLanguage::TraditionalChinese,
            "結果",
            "成功",
            "類型",
            "未經證明的假設",
            "語句",
            "事實",
            "原因",
            "未經證明的假設",
        ),
        (
            OutputLanguage::Japanese,
            "結果",
            "成功",
            "種類",
            "証明されていない仮定",
            "文",
            "事実",
            "理由",
            "証明されていない仮定",
        ),
        (
            OutputLanguage::Korean,
            "결과",
            "성공",
            "유형",
            "증명되지 않은 가정",
            "문장",
            "사실",
            "이유",
            "증명되지 않은 가정",
        ),
        (
            OutputLanguage::Spanish,
            "resultado",
            "éxito",
            "tipo",
            "suposición no demostrada",
            "enunciado",
            "hecho",
            "razón",
            "suposición no demostrada",
        ),
        (
            OutputLanguage::French,
            "résultat",
            "succès",
            "type",
            "hypothèse non prouvée",
            "énoncé",
            "fait",
            "raison",
            "hypothèse non prouvée",
        ),
        (
            OutputLanguage::German,
            "Ergebnis",
            "Erfolg",
            "Typ",
            "unbewiesene Annahme",
            "Anweisung",
            "Fakt",
            "Grund",
            "unbewiesene Annahme",
        ),
        (
            OutputLanguage::Portuguese,
            "resultado",
            "sucesso",
            "tipo",
            "suposição não provada",
            "declaração",
            "fato",
            "razão",
            "suposição não provada",
        ),
        (
            OutputLanguage::Russian,
            "результат",
            "успех",
            "тип",
            "недоказанное предположение",
            "утверждение",
            "факт",
            "причина",
            "недоказанное предположение",
        ),
        (
            OutputLanguage::Arabic,
            "النتيجة",
            "نجاح",
            "النوع",
            "افتراض غير مبرهن",
            "العبارة",
            "الحقيقة",
            "السبب",
            "افتراض غير مبرهن",
        ),
        (
            OutputLanguage::Hindi,
            "परिणाम",
            "सफलता",
            "प्रकार",
            "अप्रमाणित मान्यता",
            "कथन",
            "तथ्य",
            "कारण",
            "अप्रमाणित मान्यता",
        ),
        (
            OutputLanguage::Vietnamese,
            "kết_quả",
            "thành công",
            "kiểu",
            "giả thiết chưa chứng minh",
            "mệnh_đề",
            "sự_kiện",
            "lý_do",
            "giả thiết chưa chứng minh",
        ),
        (
            OutputLanguage::Indonesian,
            "hasil",
            "sukses",
            "tipe",
            "asumsi belum terbukti",
            "pernyataan",
            "fakta",
            "alasan",
            "asumsi belum terbukti",
        ),
    ];

    for (
        language,
        result_key,
        success_text,
        type_key,
        type_text,
        statement_key,
        _fact_key,
        _reason_key,
        _reason_text,
    ) in cases
    {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "non_english_languages_localize_unproved_trust_labels",
        );
        runtime.output_language = language;

        let (stmt_results, runtime_error) = run_source_code("trust 1 = 1", &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "localized output run failed:\n{}",
            run_output
        );
        assert!(run_output.contains(&format!("\"{}\": \"{}\"", result_key, success_text)));
        assert!(run_output.contains(&format!("\"{}\": \"{}\"", type_key, type_text)));
        assert!(run_output.contains(&format!("\"{}\": \"trust 1 = 1\"", statement_key)));
        assert!(!run_output.contains("\"result\": \"success\""));
    }
}

#[test]
fn non_english_runner_localizes_wrapper_keys() {
    let cases = vec![
        (
            OutputLanguage::SimplifiedChinese,
            "运行器",
            "结果",
            "成功",
            "是否成功",
            "运行目标",
            "运行轨迹",
        ),
        (
            OutputLanguage::TraditionalChinese,
            "執行器",
            "結果",
            "成功",
            "是否成功",
            "目標",
            "執行追蹤",
        ),
        (
            OutputLanguage::Japanese,
            "ランナー",
            "結果",
            "成功",
            "成功",
            "対象",
            "実行トレース",
        ),
        (
            OutputLanguage::Korean,
            "러너",
            "결과",
            "성공",
            "성공 여부",
            "대상",
            "실행 추적",
        ),
        (
            OutputLanguage::Spanish,
            "ejecutor",
            "resultado",
            "éxito",
            "correcto",
            "objetivo",
            "traza",
        ),
        (
            OutputLanguage::French,
            "exécuteur",
            "résultat",
            "succès",
            "réussi",
            "cible",
            "trace",
        ),
        (
            OutputLanguage::German,
            "Runner",
            "Ergebnis",
            "Erfolg",
            "erfolgreich",
            "Ziel",
            "Ablaufspur",
        ),
        (
            OutputLanguage::Portuguese,
            "executor",
            "resultado",
            "sucesso",
            "bem_sucedido",
            "alvo",
            "rastreamento",
        ),
        (
            OutputLanguage::Russian,
            "запускатель",
            "результат",
            "успех",
            "успешно",
            "цель",
            "трасса",
        ),
        (
            OutputLanguage::Arabic,
            "المشغل",
            "النتيجة",
            "نجاح",
            "ناجح",
            "الهدف",
            "الأثر",
        ),
        (
            OutputLanguage::Hindi,
            "रनर",
            "परिणाम",
            "सफलता",
            "सफल",
            "लक्ष्य",
            "चलन_चिह्न",
        ),
        (
            OutputLanguage::Vietnamese,
            "trình_chạy",
            "kết_quả",
            "thành công",
            "đúng",
            "mục_tiêu",
            "vết_chạy",
        ),
        (
            OutputLanguage::Indonesian,
            "runner",
            "hasil",
            "sukses",
            "berhasil",
            "target",
            "jejak",
        ),
    ];

    for (language, runner_key, result_key, success_text, ok_key, target_key, trace_key) in cases {
        let (ok, output) =
            run_runner_for_code_with_language("trust 1 = 1", "-runner-test", true, language);

        assert!(ok, "localized runner should succeed:\n{}", output);
        assert!(output.contains(&format!("\"{}\": \"litex-runner\"", runner_key)));
        assert!(output.contains(&format!("\"{}\": \"{}\"", result_key, success_text)));
        assert!(output.contains(&format!("\"{}\": true", ok_key)));
        assert!(output.contains(&format!("\"{}\"", target_key)));
        assert!(output.contains(&format!("\"{}\"", trace_key)));
        assert!(!output.contains("\"result\": \"success\""));
    }
}

#[test]
fn axiom_declares_named_theorem_like_forall_fact() {
    let source_code = r#"
abstract_prop axiom_prop(x)

axiom axiom_prop_all:
    ? forall x R:
        $axiom_prop(x)

$axiom_prop(2)
by thm axiom_prop_all(3)
$axiom_prop(3)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("axiom_declares_named_theorem_like_forall_fact");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "axiom should store a theorem-like forall fact:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"axiom\""),
        "axiom output should identify the declaration as an axiom:\n{}",
        run_output
    );
}

#[test]
fn axiom_rejects_proof_body() {
    let source_code = r#"
abstract_prop axiom_body_prop(x)

axiom bad_axiom:
    ? forall x R:
        $axiom_body_prop(x)
    trust $axiom_body_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("axiom_rejects_proof_body");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "axiom should reject body statements after its goal block:\n{}",
        run_output
    );
    assert!(
        run_output.contains("expects exactly one `? forall ...` goal block"),
        "axiom proof-body rejection should explain the shape:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_rejects_user_trust() {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_user_trust");
    runtime.strict_mode = true;

    let (stmt_results, runtime_error) = run_source_code("trust 1 = 0", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "strict mode should reject user trust statements:\n{}",
        run_output
    );
    assert!(
        run_output.contains(TrustStmt::strict_mode_rejection_message()),
        "strict mode should report the trust boundary:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_rejects_user_trust_have() {
    run_with_large_stack("strict_mode_rejects_user_trust_have", || {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_user_trust_have");
        runtime.strict_mode = true;

        let (stmt_results, runtime_error) = run_source_code("trust have x R", &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "strict mode should reject user trust have statements:\n{}",
            run_output
        );
        assert!(
            run_output.contains(TrustHaveStmt::strict_mode_rejection_message()),
            "strict mode should report the trust have boundary:\n{}",
            run_output
        );
    });
}

#[test]
fn strict_mode_rejects_user_axiom() {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_user_axiom");
    runtime.strict_mode = true;

    let source_code = r#"
axiom strict_axiom:
    ? forall:
        1 = 1
"#;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "strict mode should reject user axiom statements:\n{}",
        run_output
    );
    assert!(
        run_output.contains(DefThmStmt::strict_mode_rejection_message()),
        "strict mode should report the axiom boundary:\n{}",
        run_output
    );
}

#[test]
fn strict_runner_rejects_user_trust() {
    let (ok, output) = run_runner_for_code_strict("trust 1 = 0", "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject trust statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(TrustStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_runner_rejects_user_axiom() {
    let source_code = r#"
axiom strict_axiom:
    ? forall:
        1 = 1
"#;
    let (ok, output) = run_runner_for_code_strict(source_code, "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject axiom statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(DefThmStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_runner_rejects_user_trust_have() {
    run_with_large_stack("strict_runner_rejects_user_trust_have", || {
        let (ok, output) = run_runner_for_code_strict("trust have x R", "-runner-test", true);

        assert!(
            !ok,
            "strict runner should reject trust have statements:\n{}",
            output
        );
        assert!(output.contains("\"result\": \"error\""));
        assert!(output.contains(TrustHaveStmt::strict_mode_rejection_message()));
    });
}

#[test]
fn citation_verified_by_type_reflects_cited_stmt_kind() {
    let source_code = r#"
abstract_prop p(x)
trust forall x R:
    $p(x)
$p(2)
trust have a R:
    a = 1
a = 1
prop q(x R):
    x = 1
$q(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("citation_verified_by_type_reflects_cited_stmt_kind");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "citation_verified_by_type_reflects_cited_stmt_kind failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"cite forall fact\""));
    assert!(!run_output.contains("\"instantiation\""));
    assert!(!run_output.contains("\"requirements\""));
    assert!(!run_output.contains("\"statement\": \"2 $in R\""));
    assert!(run_output.contains("\"type\": \"cite equality fact\""));
    assert!(run_output.contains("\"type\": \"cite prop def\""));
}

#[test]
fn factual_verification_uses_stable_object_shape() {
    let source_code = r#"
1 = 1
forall x R:
    x = x
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("factual_verified_by_stable_shape");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "factual_verified_by_stable_shape failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"verification\": {\n    \"type\": \"builtin rule\""),
        "builtin fact should render verification as an object:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"summary\": \"conclusions verified under forall assumptions\""),
        "forall fact should not render a separate top-level verification summary:\n{}",
        run_output
    );
    assert!(run_output.contains("\"parameters\": ["));
    assert!(run_output.contains("\"assumptions\": ["));
    assert!(
        !run_output.contains("\"verified_by\""),
        "public output should use verification instead of verified_by:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"conclusions\": ["),
        "forall proof should keep one verification entry per then fact:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"verification\": {"),
        "forall proof conclusions should carry their own verification objects:\n{}",
        run_output
    );
}

#[test]
fn atomic_fact_verification_output_omits_method_and_reports_route_types() {
    let source_code = r#"
1 = 1

abstract_prop known_p(x)
trust $known_p(1)
$known_p(1)

abstract_prop forall_p(x)
trust:
    forall x R:
        x = 1
        =>:
            $forall_p(x)
$forall_p(1)

prop def_p(x R):
    x = 1
$def_p(1)

prop sym_p(x set, y set):
    x = y
by symmetric_prop:
    ? forall x, y set:
        $sym_p(x, y)
        =>:
            $sym_p(y, x)
    x = y
    y = x
have A set
have B set
trust $sym_p(A, B)
$sym_p(B, A)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "atomic_fact_verification_output_omits_method_and_reports_route_types",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "atomic verification route fixture failed:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"method\""),
        "verification output should not include redundant method field:\n{}",
        run_output
    );
    for route_type in [
        "builtin rule",
        "cite equality fact",
        "cite prop fact",
        "cite forall fact",
    ] {
        assert!(
            run_output.contains(&format!("\"type\": \"{}\"", route_type)),
            "missing atomic verification route type `{}`:\n{}",
            route_type,
            run_output
        );
    }
}

#[test]
fn builtin_rule_subgoals_are_nested_under_chain_step() {
    let source_code = r#"
forall x R_pos:
    x^3 = 8
    =>:
        3 = log(2, 8) = log(2, x^3) = 3 * log(2, x)
        log(2, x) = 1
        x = 2^1 = 2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("builtin_rule_subgoals_are_nested");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "builtin subgoal fixture failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"x = 2 ^ 1 = 2\""),
        "chain conclusion should use the public statement key:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"fact\": \"x = 2 ^ 1\""),
        "outer chain steps should include the proved chain segment:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"subgoals\": ["),
        "builtin-rule premises should be nested as subgoals:\n{}",
        run_output
    );
    assert_eq!(
        run_output.matches("\"subgoals\": [").count(),
        2,
        "normal output should show only nontrivial builtin-rule proof premises:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"2 ^ 3 = 8\""),
        "log(a,b)=c should expose the a^c=b proof premise:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"1 = log (2, x)\""),
        "the log premise should be a nested subgoal statement:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"fact\": \"1 = log (2, x)\""),
        "builtin-rule premises should not be flattened into outer chain steps:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"verified_by\""),
        "public output should use verification consistently:\n{}",
        run_output
    );
}

#[test]
fn detail_output_moves_store_facts_into_environment_effects() {
    run_with_large_stack(
        "detail_output_moves_store_facts_into_environment_effects_large_stack",
        detail_output_moves_store_facts_into_environment_effects_impl,
    );
}

fn detail_output_moves_store_facts_into_environment_effects_impl() {
    let source_code = r#"
1 = 1
claim:
    ? 2 = 2
    2 = 2
trust:
    3 = 3
trust have a R:
    a = a
prop q(x R):
    x = 1
$q(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "detail_output_moves_store_facts_into_environment_effects",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "normal output fixture failed:\n{}",
        run_output
    );
    assert!(!run_output.contains("\"infer_facts\""));
    assert!(!run_output.contains("\"effects\""));
    assert!(!run_output.contains("\"store_facts\""));
    assert!(!run_output.contains("\"trust\""));

    let mut detail_runtime = Runtime::new_with_builtin_code();
    detail_runtime.detail_output = true;
    detail_runtime.new_file_path_new_env_new_name_scope(
        "detail_output_moves_store_facts_into_environment_effects_detail",
    );
    let (detail_results, detail_error) = run_source_code(source_code, &mut detail_runtime);
    let (detail_succeeded, detail_output) =
        render_run_source_code_output(&detail_runtime, &detail_results, &detail_error, false);
    assert!(
        detail_succeeded,
        "detail output fixture failed:\n{}",
        detail_output
    );
    assert!(!detail_output.contains("\"store_facts\""));
    assert!(detail_output.contains("\"phases\": {"));
    assert!(detail_output.contains("\"affect_environment\": {"));
    assert!(detail_output.contains("\"effects\": ["));
    assert!(
        detail_output.contains(format!("\"reason\": \"{}\"", ClaimStmt::store_reason()).as_str())
    );
    assert!(
        detail_output.contains(format!("\"reason\": \"{}\"", TrustStmt::store_reason()).as_str())
    );
    assert!(detail_output
        .contains(format!("\"reason\": \"{}\"", TrustHaveStmt::store_reason()).as_str()));
    assert!(detail_output.contains(format!("\"reason\": \"{}\"", Fact::store_reason()).as_str()));
}

#[test]
fn detail_output_exposes_statement_execution_phases() {
    run_with_large_stack(
        "detail_output_exposes_statement_execution_phases_large_stack",
        detail_output_exposes_statement_execution_phases_impl,
    );
}

fn detail_output_exposes_statement_execution_phases_impl() {
    let source_code = r#"
have a R = 1
forall b R:
    b = 2
    =>:
        b^2 = 4
"#;
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = true;
    runtime
        .new_file_path_new_env_new_name_scope("detail_output_exposes_statement_execution_phases");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "execution phase fixture failed:\n{}",
        run_output
    );
    assert_eq!(run_output.matches("\"phases\": {").count(), 2);
    assert!(run_output.contains("\"verify_well_definedness\": {"));
    assert!(run_output.contains("\"verify_process\": {"));
    assert!(run_output.contains("\"affect_environment\": {"));
    assert!(run_output.contains("\"kind\": \"parameter_binding\""));
    assert!(run_output.contains("\"statement\": \"1 $in R\""));
    assert!(run_output.contains("\"rule\": \"calculation\""));
    assert!(run_output.contains("\"kind\": \"declare_object\""));
    assert!(run_output.contains("\"kind\": \"store_fact\""));
    assert!(!run_output.contains("\"store_facts\""));
}

#[test]
fn detail_output_marks_failed_phase_and_does_not_claim_environment_effects() {
    run_with_large_stack(
        "detail_output_marks_failed_phase_and_does_not_claim_environment_effects_large_stack",
        detail_output_marks_failed_phase_and_does_not_claim_environment_effects_impl,
    );
}

fn detail_output_marks_failed_phase_and_does_not_claim_environment_effects_impl() {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = true;
    runtime.new_file_path_new_env_new_name_scope(
        "detail_output_marks_failed_phase_and_does_not_claim_environment_effects",
    );
    let (stmt_results, runtime_error) = run_source_code("have a N = -1", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "invalid object definition should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"verify_process\": {\n      \"status\": \"error\""));
    assert!(run_output.contains("\"affect_environment\": {\n      \"status\": \"not_run\""));
    assert!(!run_output.contains("\"effects\": ["));
}

#[test]
fn object_definition_output_exposes_checks_and_defined_facts() {
    run_with_large_stack(
        "object_definition_output_exposes_checks_and_defined_facts_large_stack",
        || {
            let source_code = r#"
have a R
have b R = a
have S set
trust exist x R st {x = x}
obtain c from exist x R st {x = x}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.detail_output = true;
            runtime.new_file_path_new_env_new_name_scope(
                "object_definition_output_exposes_checks_and_defined_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "object definition output fixture failed:\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(
                &run_output,
                HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
            );
            assert!(run_output.contains("\"a $in R\""));
            assert!(run_output.contains("\"b $in R\""));
            assert!(run_output.contains("\"b = a\""));
            assert!(run_output.contains("\"$is_set(S)\""));
            assert!(run_output.contains("\"c $in R\""));
            assert!(run_output.contains("\"c = c\""));
            assert!(run_output.contains(
                format!(
                    "\"reason\": \"{}\"",
                    HaveObjInNonemptySetOrParamTypeStmt::store_reason()
                )
                .as_str()
            ));
            assert!(run_output
                .contains(format!("\"reason\": \"{}\"", HaveByExistStmt::store_reason()).as_str()));
            assert!(!run_output.contains("\"equal_to\""));
        },
    );
}

#[test]
fn forall_parameter_assumption_output_is_local_assumption() {
    let source_code = r#"
forall n N:
    n $in N
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_parameter_assumption_output");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "forall parameter assumption fixture failed:\n{}",
        run_output
    );
    assert!(!run_output.contains("\"type\": \"forall proof\""));
    assert!(run_output.contains("\"n $in N\""));
    assert!(run_output.contains("\"conclusions\": ["));
    assert!(run_output.contains("\"statement\": \"n $in N\""));
    assert!(run_output.contains("\"type\": \"local assumption\""));
    assert!(run_output
        .contains(format!("\"source\": \"{}\"", ParamDefWithType::store_reason()).as_str()));
    assert!(!run_output.contains("\"cite_source\""));
    assert!(!run_output.contains("\"verify_what\""));
    assert!(!run_output.contains("forall local check"));
}

#[test]
fn forall_output_exposes_parameters_and_assumption_store_facts() {
    run_with_large_stack(
        "forall_output_exposes_parameters_and_assumption_store_facts",
        || {
            let source_code = r#"
abstract_prop p(a, b, c)
forall a, b, c, d, e, f R:
    $p(a, b, c)
    a = d
    b = e
    c = f
    =>:
        $p(d, e, f)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "forall_output_exposes_assumption_store_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "forall assumption store-fact output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"parameters\": ["));
            assert!(run_output.contains("\"a\""));
            assert!(run_output.contains("\"f\""));
            assert!(run_output.contains("\"assumptions\": ["));
            assert!(run_output.contains("\"fact\": \"a $in R\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ParamDefWithType::store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"$p(a, b, c)\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ForallFact::premise_store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"a = d\""));
            assert!(run_output.contains("\"fact\": \"b = e\""));
            assert!(run_output.contains("\"fact\": \"c = f\""));
            assert_eq!(run_output.matches("\"fact\": \"a $in R\"").count(), 1);
        },
    );
}

#[test]
fn claim_forall_output_explains_parameters_proof_steps_and_conclusions() {
    run_with_large_stack(
        "claim_forall_output_explains_parameters_proof_steps_and_conclusions",
        || {
            let source_code = r#"
claim:
    ? forall x R:
        x = 1
        =>:
            x = 1
    x = x
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("claim_forall_output_explains_proof");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "claim forall output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proved claim\""));
            assert!(run_output.contains("\"type\": \"claim forall proof\""));
            assert!(run_output.contains("\"parameters\": ["));
            assert!(run_output.contains("\"x\""));
            assert!(run_output.contains("\"assumptions\": ["));
            assert!(run_output.contains("\"fact\": \"x $in R\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ParamDefWithType::store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"x = 1\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ForallFact::premise_store_reason()).as_str()
            ));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"statement\": \"x = x\""));
            assert!(run_output.contains("\"conclusions\": ["));
            assert!(run_output.contains("\"statement\": \"x = 1\""));
            assert!(run_output.contains("\"type\": \"local assumption\""));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal claim output should retain its readable internal route:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn claim_fact_output_explains_proof_steps_and_final_goal() {
    run_with_large_stack(
        "claim_fact_output_explains_proof_steps_and_final_goal",
        || {
            let source_code = r#"
claim 1 = 1:
    1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("claim_fact_output_explains_goal");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "claim fact output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proved claim\""));
            assert!(run_output.contains("\"type\": \"claim proof\""));
            assert!(run_output.contains("\"prove_goal\": \"1 = 1\""));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"conclusion\": {"));
            assert!(run_output.contains("\"type\": \"cite equality fact\""));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal claim output should retain its readable internal route:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn output_contract_covers_composite_facts_and_control_statements() {
    run_with_large_stack(
        "output_contract_covers_composite_facts_and_control_statements",
        || {
            let source_code = r#"
1 = 1 and 2 = 2
1 = 1 = 1

claim:
    ? forall:
        1 = 1
    1 = 1

thm one_eq_one:
    ? forall:
        1 = 1
    1 = 1

by thm one_eq_one()

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "output_contract_covers_composite_facts_and_control_statements",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "output contract fixture failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"summary\": \"each conjunct verified in order\""),
                "and facts should keep a short composite proof summary:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"summary\": \"each chain step verified in order\""),
                "chain facts should keep a short composite proof summary:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"type\": \"chain fact\""),
                "normal output should not repeat the composite fact type inside verification:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"main_rule\": \"chain decomposition\""),
                "normal output should hide chain structural-rule debug metadata:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"role\": \"chain step\""),
                "normal output should hide chain step roles:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"step_indices\": ["),
                "normal folded output should not expose step indices:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"main_rule\": \"and decomposition\""),
                "normal output should hide and structural-rule debug metadata:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"role\": \"conjunct\""),
                "normal output should hide conjunct step roles:\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(&run_output, "successful");
            assert!(
                run_output.contains("\"type\": \"proved claim\""),
                "claim/thm statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by theorem\""),
                "by thm statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by cases\""),
                "by cases statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"unknown_result\""),
                "successful output should not use failure-only unknown_result:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_cases_normal_output_lists_readable_internal_results() {
    run_with_large_stack(
        "by_cases_normal_output_lists_readable_internal_results",
        || {
            let source_code = r#"
by cases:
    ? 1 = 1
    ? 2 = 2
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_cases_normal_output_lists_readable_internal_results",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "by cases multi-goal fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proof by cases\""));
            assert!(run_output.contains("\"type\": \"by cases proof\""));
            assert!(run_output.contains("\"inside_results\": ["));
            assert!(run_output.contains("\"why_verified\": {"));
            assert!(!run_output.contains("\"phases\": {"));
            assert!(!run_output.contains("\"case_coverage\": {"));
            assert_no_legacy_acceptance_field(&run_output, "by cases");
            assert!(run_output.contains("\"1 = 1\""));
            assert!(run_output.contains("\"2 = 2\""));
        },
    );
}

#[test]
fn by_cases_detail_output_expands_case_inside_results() {
    run_with_large_stack("by_cases_detail_output_expands_case_inside_results", || {
        let source_code = r#"
by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("by_cases_detail_output_expands_cases");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "by cases detail fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert_no_legacy_acceptance_field(&run_output, "detail");
        assert!(run_output.contains("\"1 = 1\""));
    });
}

#[test]
fn by_contra_output_explains_reverse_assumption_proof_and_impossible_checks() {
    run_with_large_stack(
        "by_contra_output_explains_reverse_assumption_proof_and_impossible_checks",
        || {
            let source_code = r#"
by contra 1 = 1:
    do_nothing
    impossible 1 != 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("by_contra_output_explains_steps");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "by contra output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proof by contradiction\""));
            assert!(run_output.contains("\"type\": \"by contra proof\""));
            assert!(run_output.contains("\"prove_goal\": \"1 = 1\""));
            assert!(run_output.contains("\"reverse_assumption\": {"));
            assert!(run_output.contains("\"fact\": \"1 != 1\""));
            assert!(run_output.contains("\"reason\": \"by contra assumption\""));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"statement\": \"do_nothing\""));
            assert!(run_output.contains("\"impossible\": {"));
            assert!(run_output.contains("\"role\": \"impossible fact\""));
            assert!(run_output.contains("\"statement\": \"1 != 1\""));
            assert!(run_output.contains("\"role\": \"reversed impossible fact\""));
            assert!(run_output.contains("\"statement\": \"1 = 1\""));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal by contra output should retain its readable internal route:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_iteration_range_extension_and_theorem_outputs_explain_processes() {
    run_with_large_stack(
        "by_iteration_range_extension_and_theorem_outputs_explain_processes",
        || {
            let source_code = r#"
thm local_one_eq_one:
    ? forall:
        1 = 1
    1 = 1

by thm local_one_eq_one()

by enumerate finite_set:
    ? forall a {1, 2}:
        a < 3
    do_nothing

by for:
    ? forall n range(0, 3):
        n < 3
    do_nothing

claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    by enumerate range: x $in range(1, 3)

claim:
    ? forall y closed_range(1, 2):
        y = 1 or y = 2
    by closed_range as cases: y $in 1...2

by extension {1} = {1}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_iteration_range_extension_and_theorem_outputs_explain_processes",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(run_succeeded, "by output fixture failed:\n{}", run_output);
            assert!(run_output.contains("\"type\": \"by thm proof\""));
            assert!(run_output.contains("\"parameter_type_check\": {"));
            assert!(run_output.contains("\"stored_then_facts\": ["));
            assert!(run_output.contains("\"type\": \"by enumerate finite_set proof\""));
            assert!(run_output.contains("\"assignment\": {"));
            assert!(run_output.contains("\"reason\": \"enumerated assignment\""));
            assert!(run_output.contains("\"type\": \"by for proof\""));
            assert!(run_output.contains("\"iteration_mode\": \"ranges\""));
            assert!(run_output.contains("\"reason\": \"for assignment\""));
            assert!(run_output.contains("\"type\": \"by enumerate range proof\""));
            assert!(run_output.contains("\"generated_cases\":"));
            assert!(run_output.contains("\"type\": \"by closed_range as cases proof\""));
            assert!(run_output.contains("\"type\": \"by extension proof\""));
            assert!(run_output.contains("\"subset_checks\": ["));
            assert!(run_output.contains("\"reason\": \"set extensionality\""));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal output should retain its readable internal route:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_induc_prop_bridge_and_trusted_outputs_explain_processes() {
    run_with_large_stack(
        "by_induc_prop_bridge_and_trusted_outputs_explain_processes",
        || {
            let source_code = r#"
abstract_prop local_induc_p(a)
trust $local_induc_p(0)
trust forall m Z:
    m >= 0
    $local_induc_p(m)
    =>:
        $local_induc_p(m + 1)
by induc n from 0:
    ? $local_induc_p(n)

    ? from n = 0:
        $local_induc_p(0)

    ? induc:
        $local_induc_p(n + 1)

prop local_same_obj(x set, y set):
    x = y

by reflexive_prop:
    ? forall x set:
        $local_same_obj(x, x)
    x = x

by symmetric_prop:
    ? forall x, y set:
        $local_same_obj(x, y)
        =>:
            $local_same_obj(y, x)
    x = y
    y = x

have local_family set
by axiom_of_choice: set local_family:
    trust forall A local_family:
        $is_nonempty_set(A)

have local_ordered_set set
abstract_prop local_leq(x, y)
by zorn_lemma: set local_ordered_set, prop local_leq:
    trust $is_nonempty_set(local_ordered_set)
    trust:
        forall x local_ordered_set:
            $local_leq(x, x)
        forall x, y, z local_ordered_set:
            $local_leq(x, y)
            $local_leq(y, z)
            =>:
                $local_leq(x, z)
        forall x, y local_ordered_set:
            $local_leq(x, y)
            $local_leq(y, x)
            =>:
                x = y
        forall C power_set(local_ordered_set):
            forall x, y C:
                $local_leq(x, y) or $local_leq(y, x)
            =>:
                exist u local_ordered_set st {forall! x C => {$local_leq(x, u)}}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_induc_prop_bridge_and_trusted_outputs_explain_processes",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "structured by output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"by induc proof\""));
            assert!(run_output.contains("\"base_case\": {"));
            assert!(run_output.contains("\"step_case\": {"));
            assert!(run_output.contains("\"reason\": \"induction hypothesis\""));
            assert!(run_output.contains("\"type\": \"by prop registration proof\""));
            assert!(run_output.contains("\"registration\": \"reflexive\""));
            assert!(run_output.contains("\"registration\": \"symmetric\""));
            assert!(run_output.contains("\"type\": \"by axiom_of_choice proof\""));
            assert!(run_output.contains("\"label\": \"members_nonempty\""));
            assert!(run_output.contains("\"type\": \"proved in proof steps\""));
            assert!(run_output.contains("\"type\": \"by zorn_lemma proof\""));
            assert!(run_output.contains("\"label\": \"chain_upper_bound\""));
            assert!(run_output.contains("\"trusted_conclusion\":"));
            assert!(
                run_output.contains("\"inside_results\": ["),
                "normal output should retain its readable internal route:\n{}",
                run_output
            );
        },
    );
}

#[test]
pub(super) fn unknown_fact_failure_has_structured_output_fields() {
    let source_code = "1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("unknown_fact_failure_structured_output");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "unknown fact fixture should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"failed_goal\": \"1 = 2\""),
        "unknown fact should expose failed_goal:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"unknown_result\": {\n      \"type\": \"atomic fact unknown\""),
        "unknown atomic fact should expose fact-specific unknown_result:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"goal\": \"1 = 2\""),
        "unknown atomic fact should expose its goal:\n{}",
        run_output
    );
}

#[test]
pub(super) fn detail_output_keeps_composite_fact_step_metadata() {
    let source_code = r#"
1 = 1 and 2 = 2
1 = 1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("detail_output_keeps_composite_fact_step_metadata");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "detail composite fact fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"and fact\""));
    assert!(run_output.contains("\"type\": \"chain fact\""));
    assert!(run_output.contains("\"main_rule\": \"and decomposition\""));
    assert!(run_output.contains("\"main_rule\": \"chain decomposition\""));
    assert!(run_output.contains("\"role\": \"conjunct\""));
    assert!(run_output.contains("\"role\": \"chain step\""));
    assert!(run_output.contains("\"step_index\": 1"));
    assert!(run_output.contains("\"step_count\": 2"));
}

#[test]
fn and_fact_unknown_reports_failed_part() {
    let source_code = "1 = 1 and 1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("and_fact_unknown_reports_failed_part");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "and fact fixture should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"and fact unknown\""),
        "and fact unknown should be fact-specific:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"failed_part\": {"),
        "and fact unknown should expose the failed part:\n{}",
        run_output
    );
    assert!(run_output.contains("\"stmt\": \"1 = 2\""));
    assert!(!run_output.contains("\"index\": 2"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
}

#[test]
fn chain_fact_unknown_reports_failed_chain_step() {
    let source_code = "1 = 0 = 1";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("chain_fact_unknown_reports_failed_chain_step");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "chain fact fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"chain fact unknown\""));
    assert!(
        run_output.contains("\"failed_chain_step\": {"),
        "chain fact unknown should expose the failed chain step:\n{}",
        run_output
    );
    assert!(run_output.contains("\"stmt\": \"1 = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("unverified chain step"),
        "chain unknown output should not hide the failed step in a detail string:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"previous_error\": null"),
        "normal error output should omit empty previous_error fields:\n{}",
        run_output
    );
}

#[test]
fn forall_fact_unknown_reports_failed_prove() {
    let source_code = r#"
forall x R:
    x = 0
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_fact_unknown_reports_failed_prove");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall unknown\""));
    assert!(run_output.contains("\"params\": ["));
    assert!(run_output.contains("\"name\": \"x\""));
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"stmt\": \"~1x = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 1"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
}

#[test]
fn forall_chain_unknown_nests_failed_chain_step() {
    let source_code = r#"
forall x R:
    x = 0 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_chain_unknown_nests_failed_chain_step");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall-chain unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall unknown\""));
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"type\": \"chain fact unknown\""));
    assert!(run_output.contains("\"failed_chain_step\": {"));
    assert!(run_output.contains("\"stmt\": \"~1x = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(!run_output.contains("unverified chain step"));
    assert!(!run_output.contains("\"previous_error\": null"));
}

#[test]
fn detail_unknown_output_keeps_failed_part_position_metadata() {
    let source_code = r#"
forall x R:
    x = 0 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "detail_unknown_output_keeps_failed_part_position_metadata",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "detail forall-chain unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"index\": 1"));
    assert!(run_output.contains("\"count\": 1"));
    assert!(run_output.contains("\"failed_chain_step\": {"));
    assert!(run_output.contains("\"count\": 2"));
    assert!(run_output.contains("\"type\": \"atomic fact unknown\""));
}

#[test]
fn forall_iff_unknown_reports_failed_direction() {
    let source_code = r#"
forall x R:
    =>:
        x = 0
    <=>:
        x = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_iff_unknown_reports_failed_direction");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall iff unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall iff unknown\""));
    assert!(run_output.contains("\"failed_direction\": \"then to iff\""));
    assert!(run_output.contains("\"type\": \"forall unknown\""));
}

#[test]
fn proof_block_failure_has_structured_then_clause_fields() {
    let source_code = r#"
claim:
    ? forall:
        2 = 3
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("proof_block_failure_structured_then_clause");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded, "claim fixture should fail:\n{}", run_output);
    assert!(
        run_output.contains("\"failed_goal\": \"2 = 3\""),
        "claim failure should expose failed_goal:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"then_clause_index\": 1"),
        "normal claim failure should hide positional metadata:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"unknown_result\": {"),
        "claim failure should expose structured unknown_result:\n{}",
        run_output
    );
}

#[test]
fn detail_proof_block_failure_keeps_then_clause_position_metadata() {
    let source_code = r#"
claim:
    ? forall:
        2 = 3
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "detail_proof_block_failure_keeps_then_clause_position_metadata",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "detail claim fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"then_clause_index\": 1"));
    assert!(run_output.contains("\"then_clause_count\": 1"));
}

#[test]
fn by_cases_failure_reports_case_split_failure_context() {
    run_with_large_stack(
        "by_cases_failure_reports_case_split_failure_context",
        || {
            let source_code = r#"
by cases 1 = 1:
    case 1 = 2:
        do_nothing
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("by_cases_failure_context");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "non-covering case split should fail:\n{}",
                run_output
            );
            assert!(
                run_output.contains("by cases: cannot verify that all cases cover all situations"),
                "by cases failure should keep the case split failure message:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by cases\""),
                "by cases failure should identify the failing statement:\n{}",
                run_output
            );
        },
    );
}
