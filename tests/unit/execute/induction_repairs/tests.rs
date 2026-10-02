use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(code: &str, expected: &[bool]) -> Runtime {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = runtime.run_litex_code(code).expect("run input");
    assert!(
        run.session_error.is_none(),
        "{code}\n{:?}",
        run.session_error
    );
    let actual: Vec<_> = run
        .statement_results
        .iter()
        .map(|s| !s.is_failed())
        .collect();
    assert_eq!(actual, expected, "{code}");
    assert_eq!(runtime.execution_environments_stack.len(), 1, "{code}");
    runtime
}

#[test]
fn induction_nested_case_overlap_and_holes_reject_before_publication() {
    for keyword in ["have fn", "algo"] {
        let mut rt = check(&format!("{keyword} hole(n N) N by induc n from 0:\n    case n = 0:\n        case n = 0: 0\n        case n >= 0: 1\n    case n >= 1: 1\n0 = 1\n"), &[false, false]);
        assert!(!rt
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key("hole"));
        assert!(rt
            .run_litex_code("hole(0) = 0")
            .unwrap()
            .session_error
            .is_some());
        let rt = check(&format!("{keyword} hole(n N) N by induc n from 0:\n    case n = 0:\n        case n != 0: 0\n    case n >= 1: 1\n"), &[false]);
        assert!(!rt
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key("hole"));
    }
}

#[test]
fn induction_nested_cases_use_parent_guards_and_keep_chain_components() {
    check("have fn nested(n N) N by induc n from 0:\n    case n = 0:\n        case n = 0: 0\n    case n >= 1:\n        case 1 <= n < 2: 1\n        case n >= 2: nested(n - 1)\nnested(0) = 0\nnested(1) = 1\n", &[true, true, true]);
    check("have fn nested(n N) N by induc n from 0:\n    case n = 0:\n        case n = 0:\n            case n = 0: 0\n            case n >= 0: 1\n    case n >= 1: 1\n", &[false]);
}

#[test]
fn induction_goal_wd_uses_the_induction_domain_without_ih() {
    for keyword in ["induc", "strong_induc"] {
        check(
            &format!("have fn f(x N) N = x\nby {keyword} n from 0:\n    ? f(n) = f(n)\n"),
            &[true, true],
        );
        check(
            &format!("have fn f(x N) N = x\nby {keyword} n from -1:\n    ? f(n) = f(n)\n"),
            &[true, false],
        );
        check(
            &format!("by {keyword} n from 0:\n    ? n / n = n / n\n"),
            &[false],
        );
        check(
            &format!("by {keyword} n from 0.5:\n    ? n = n\n"),
            &[false],
        );
    }
}

#[test]
fn induction_ordinary_proof_statements_are_scoped_and_checked() {
    for keyword in ["induc", "strong_induc"] {
        let step = if keyword == "induc" {
            "induc"
        } else {
            "strong_induc"
        };
        let mut rt = check(
            &format!("by {keyword} n from 0:\n    ? n = n\n    have a N = 0\n    let b = a\n"),
            &[true],
        );
        assert!(!rt.top_exec_env().definitions.identifiers.contains_key("a"));
        assert!(!rt.top_exec_env().definitions.identifiers.contains_key("b"));
        assert!(rt.run_litex_code("b = 0").unwrap().session_error.is_some());
        check(&format!("prop same(x Z):\n    x = x\nby {keyword} n from 0:\n    ? $same(n)\n    ? from n = 0:\n        by def $same(0)\n    ? {step}:\n        by def $same(n + 1)\n"), &[true, true]);
        check(
            &format!("by {keyword} n from 0:\n    ? n = n\n    have a {{1}} = 0\n"),
            &[false],
        );
        let mut rt = check("0 = 0\n", &[true]);
        let run = rt
            .run_litex_code(&format!(
                "by {keyword} n from 0:\n    ? n = n\n    trust 0 = 0\n"
            ))
            .unwrap();
        assert!(!run.success);
        assert!(run.session_error.is_some());
    }
}

#[test]
fn induction_recovers_binders_inside_collections_functions_and_sets() {
    for obj in [
        "{n}",
        "(n, 0)",
        "{y Z: y = n}",
        "fn(x Z) Z {n}",
        "range(n, n + 1)",
        "finite_set_size({n})",
    ] {
        check(
            &format!("by induc n from 0:\n    ? {obj} = {obj}\n"),
            &[true],
        );
        check(
            &format!("by strong_induc n from 0:\n    ? {obj} = {obj}\n"),
            &[true],
        );
    }
}

#[test]
fn induction_constant_goals_preserve_proof_only_binders_and_allow_unused_ones() {
    for keyword in ["induc", "strong_induc"] {
        check(&format!("by {keyword} n from 0:\n    ? 0 = 0\n"), &[true]);
        check(&format!("by {keyword} n from 0:\n    ? 0 = 1\n"), &[false]);
        for body in [
            "let a = n",
            "have a Z = n",
            "claim:\n        ? forall u {n}:\n            u = u",
            "witness exist u Z st {u = n} from n",
        ] {
            check(
                &format!("by {keyword} n from 0:\n    ? 0 = 0\n    {body}\n"),
                &[true],
            );
        }
        check(&format!("prop same(x Z):\n    x = x\nby {keyword} n from 0:\n    ? 0 = 0\n    by def $same(n)\n"), &[true, true]);
    }
}

#[test]
fn induction_json_preserves_failed_stages_and_successful_case_evidence() {
    use crate::json_output::{project_stmt_detailed, project_stmt_normal};
    use crate::knowledge_base::JsonValue;
    for keyword in ["induc", "strong_induc"] {
        for (body, phase, subphase, index_key) in [
            ("? n > 0", "base", "goal", "goal_index"),
            ("? n = 0", "step", "goal", "goal_index"),
            (
                "? n = n\n    have a {1} = 0",
                "base",
                "proof_body",
                "step_index",
            ),
        ] {
            let mut rt = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            });
            let run = rt
                .run_litex_code(&format!("by {keyword} n from 0:\n    {body}\n"))
                .unwrap();
            assert!(run.session_error.is_none());
            let stmt = &run.statement_results[0];
            let detailed = project_stmt_detailed(stmt, &rt);
            let normal = project_stmt_normal(stmt, &rt);
            let reason = detailed.as_object().unwrap().get("failure").unwrap();
            let normal_reason = normal
                .as_object()
                .unwrap()
                .get("why_failed")
                .unwrap()
                .as_object()
                .unwrap()
                .get("failure")
                .unwrap();
            assert_eq!(reason, normal_reason);
            assert_eq!(
                reason
                    .as_object()
                    .unwrap()
                    .get("phase")
                    .unwrap()
                    .as_str()
                    .unwrap(),
                phase
            );
            let failure = reason
                .as_object()
                .unwrap()
                .get("failure")
                .unwrap()
                .as_object()
                .unwrap();
            assert_eq!(failure.get("phase").unwrap().as_str().unwrap(), subphase);
            assert_eq!(failure.get(index_key), Some(&JsonValue::Number(0.0)));
            assert!(failure.get("result").is_some());
        }
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = rt
            .run_litex_code(&format!(
                "by {keyword} n from 0:\n    ? n = n\n    have a N = 0\n"
            ))
            .unwrap();
        assert!(run.success);
        let detail = project_stmt_detailed(&run.statement_results[0], &rt);
        let body = detail
            .as_object()
            .unwrap()
            .get("body")
            .unwrap()
            .as_object()
            .unwrap();
        for case in ["base", "step"] {
            let case = body.get(case).unwrap().as_object().unwrap();
            assert_eq!(
                case.get("proof_steps").unwrap().as_array().unwrap().len(),
                1
            );
            assert_eq!(
                case.get("goals_verified")
                    .unwrap()
                    .as_array()
                    .unwrap()
                    .len(),
                1
            );
            assert!(case.get("local_env").is_none());
        }
    }
}

#[test]
fn induction_definition_json_keeps_nested_path_and_checks() {
    use crate::json_output::{project_stmt_detailed, project_stmt_normal};
    use crate::knowledge_base::JsonValue;
    for keyword in ["have fn", "algo"] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = rt.run_litex_code(&format!("{keyword} bad(n N) N by induc n from 0:\n    case n = 0:\n        case n = 0: 0\n        case n >= 0: 1\n    case n >= 1: 1\n")).unwrap();
        assert!(!run.success);
        let detail = project_stmt_detailed(&run.statement_results[0], &rt);
        let normal = project_stmt_normal(&run.statement_results[0], &rt);
        let failure = detail.as_object().unwrap().get("failure").unwrap();
        assert_eq!(
            normal
                .as_object()
                .unwrap()
                .get("why_failed")
                .unwrap()
                .as_object()
                .unwrap()
                .get("failure"),
            Some(failure)
        );
        let outer = failure.as_object().unwrap();
        assert_eq!(outer.get("phase").unwrap().as_str().unwrap(), "nested_case");
        assert_eq!(outer.get("case_index"), Some(&JsonValue::Number(0.0)));
        let inner = outer.get("failure").unwrap().as_object().unwrap();
        assert_eq!(inner.get("phase").unwrap().as_str().unwrap(), "disjoint");
        assert_eq!(inner.get("right_case_index"), Some(&JsonValue::Number(1.0)));
        let run = rt.run_litex_code(&format!("{keyword} good(n N) N by induc n from 0:\n    case n = 0:\n        case n = 0: 0\n    case n >= 1: 1\n")).unwrap();
        assert!(run.success);
        let detail = project_stmt_detailed(&run.statement_results[0], &rt);
        let mut result = detail.as_object().unwrap();
        if keyword == "algo" {
            result = result.get("define_fn").unwrap().as_object().unwrap();
        }
        let checks = result.get("case_checks").unwrap().as_object().unwrap();
        assert_eq!(checks.get("disjoint").unwrap().as_array().unwrap().len(), 1);
        let nested = checks.get("cases").unwrap().as_array().unwrap()[0]
            .as_object()
            .unwrap()
            .get("body")
            .unwrap()
            .as_object()
            .unwrap();
        assert!(nested.get("coverage").is_some());
        assert_eq!(nested.get("cases").unwrap().as_array().unwrap().len(), 1);
    }
}

#[test]
fn induction_examples_cover_the_maintained_acceptance_sources() {
    for path in [
        "examples/stmt_nodes/definition/inductive_nested_cases.lit",
        "examples/stmt_nodes/definition/template_inductive_arithmetic.lit",
        "examples/stmt_nodes/by/induction_domain_and_proof_actions.lit",
        "examples/stmt_nodes/by/induction_collection_binders.lit",
    ] {
        let source =
            std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path))
                .unwrap();
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{path}: {:?}",
            run.session_error
        );
        assert!(
            run.statement_results.iter().all(|s| !s.is_failed()),
            "{path}"
        );
    }
}

#[test]
fn induction_failure_details_survive_chinese_output_keys() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::Chinese,
    });
    let run = rt
        .run_litex_code("by induc n from 0:\n    ? n = 0\n")
        .unwrap();
    assert!(!run.success);
    let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let reason = normal
        .as_object()
        .unwrap()
        .get("失败原因")
        .unwrap()
        .as_object()
        .unwrap()
        .get("失败详情")
        .unwrap();
    assert_eq!(detailed.as_object().unwrap().get("失败详情"), Some(reason));
    assert_eq!(
        reason
            .as_object()
            .unwrap()
            .get("阶段")
            .unwrap()
            .as_str()
            .unwrap(),
        "归纳步"
    );
    let child = reason
        .as_object()
        .unwrap()
        .get("失败详情")
        .unwrap()
        .as_object()
        .unwrap();
    assert!(child.get("目标索引").is_some());
    assert_eq!(child.get("阶段").unwrap().as_str().unwrap(), "目标证明");
}

#[test]
fn induction_template_recursion_under_arithmetic_replays_the_exact_instance() {
    // The template parameter changes the result, exposing accidental instance reuse.
    check("template<B N>:\n    have fn shift_t(n N) N by induc n from 0:\n        case n = 0: B\n        case n >= 1: shift_t(n - 1) + 1\n\\shift_t<2>(1 - 1) = 2\n\\shift_t<2>(1) = \\shift_t<2>(1 - 1) + 1 = 3\n\\shift_t<7>(1 - 1) = 7\n\\shift_t<7>(1) = \\shift_t<7>(1 - 1) + 1 = 8\n\\shift_t<7>(1) = 3\n", &[true, true, true, true, true, false]);
    check("template<S set>:\n    have fn succ_t(n N) N by induc n from 0:\n        case n = 0: 0\n        case n >= 1: succ_t(n - 1) + 1\n\\succ_t<{0}>(0) = 0\n\\succ_t<{0}>(1 - 1) = 0\n\\succ_t<{0}>(1) = \\succ_t<{0}>(1 - 1) + 1 = 1\n\\succ_t<{1}>(1 - 1) = 0\n\\succ_t<{1}>(1) = \\succ_t<{1}>(1 - 1) + 1 = 1\n\\succ_t<{0}>(1) = 0\n", &[true, true, true, true, true, true, false]);
    check("template<S set>:\n    have fn bad(n N) N by induc n from 0:\n        case n = 0: 0\n        case n >= 1: bad(n) + 1\n", &[false]);
}
