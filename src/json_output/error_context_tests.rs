use crate::prelude::*;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(crate::launch_command::LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn field(value: &JsonValue, key: &str, language: OutputLanguage) -> JsonValue {
    value
        .as_object()
        .unwrap()
        .get(&super::json_keys::localize_key(key, language))
        .unwrap_or_else(|| panic!("missing {key}: {value:?}"))
        .clone()
}

#[test]
fn register_errors_keep_the_same_failure_in_normal_and_detailed() {
    for (property, law) in [
        ("reflexive", "forall x set:\n        $bad(x,x)"),
        ("symmetric", "forall x,y set:\n        $bad(x,y)\n        =>:\n            $bad(y,x)"),
        ("transitive", "forall x,y,z set:\n        $bad(x,y)\n        $bad(y,z)\n        =>:\n            $bad(x,z)"),
    ] {
        for (setup, phase, category) in [
            ("", "prop_not_defined", "name_not_found"),
            ("prop bad(x set):\n    x=x\n", "wrong_arity", "arity"),
            (if property == "symmetric" { "prop bad(x,y set):\n    x={}\n    y={1}\n" } else { "prop bad(x,y set):\n    x!=y\n" }, "forall", "proof_search"),
        ] {
            for lang in [OutputLanguage::English, OutputLanguage::Chinese] {
                let mut rt = runtime(lang);
                let run = rt.run_litex_code(&format!("{setup}register {property}:\n    ? {law}\n")).unwrap();
                assert!(!run.success && run.session_error.is_none());
                let result = run.statement_results.last().unwrap();
                let normal = super::project_stmt_normal(result, &rt);
                let detailed = super::project_stmt_detailed(result, &rt);
                let reason = field(&normal, "why_failed", lang);
                let failure = field(&reason, "failure", lang);
                assert_eq!(failure, field(&detailed, "failure", lang));
                assert_eq!(field(&failure, "phase", lang).as_str(), Ok(phase));
                assert_eq!(field(&field(&reason, "diagnostic", lang), "category", lang).as_str(), Ok(category));
                if phase == "wrong_arity" {
                    assert_eq!(field(&failure, "expected", lang), JsonValue::Number(2.0));
                    assert_eq!(field(&failure, "actual", lang), JsonValue::Number(1.0));
                }
                assert!(field(&normal, "stores", lang).as_array().unwrap().is_empty());
            }
        }
    }
}

#[test]
fn explicit_definition_reports_actual_requirements_and_keeps_context() {
    for lang in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(lang);
        assert!(
            rt.run_litex_code("prop positive(x R):\n    x > 0\n")
                .unwrap()
                .success
        );
        let run = rt.run_litex_code("by def $positive(0)").unwrap();
        assert!(!run.success && run.session_error.is_none());
        let normal = super::project_stmt_normal(&run.statement_results[0], &rt);
        let detailed = super::project_stmt_detailed(&run.statement_results[0], &rt);
        let failure = field(&field(&normal, "why_failed", lang), "failure", lang);
        assert_eq!(failure, field(&detailed, "failure", lang));
        assert_eq!(
            field(&failure, "phase", lang).as_str(),
            Ok("definition_requirement")
        );
        assert_eq!(field(&failure, "goal", lang).as_str(), Ok("0 > 0"));
        assert_eq!(field(&failure, "index", lang), JsonValue::Number(1.0));
        assert_eq!(
            field(&field(&failure, "diagnostic", lang), "obligation", lang).as_str(),
            Ok("0 > 0")
        );
        assert!(rt.run_litex_code("by def $positive(1)").unwrap().success);
        assert!(!rt.run_litex_code("$positive(0)").unwrap().success);

        assert!(
            rt.run_litex_code("abstract_prop opaque(x)")
                .unwrap()
                .success
        );
        let run = rt.run_litex_code("by def $opaque(1)").unwrap();
        let normal = super::project_stmt_normal(&run.statement_results[0], &rt);
        let diagnostic = field(&field(&normal, "why_failed", lang), "diagnostic", lang);
        assert_eq!(
            field(&diagnostic, "category", lang).as_str(),
            Ok("definition_proof_unavailable")
        );
    }
}

#[test]
fn builtin_definition_reports_the_failed_obligation() {
    let mut rt = runtime(OutputLanguage::English);
    let run = rt.run_litex_code("by def {1} $proper_subset {1}").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let normal = super::project_stmt_normal(&run.statement_results[0], &rt);
    let failure = field(
        &field(&normal, "why_failed", OutputLanguage::English),
        "failure",
        OutputLanguage::English,
    );
    assert_eq!(
        field(&failure, "phase", OutputLanguage::English).as_str(),
        Ok("definition_requirement")
    );
    assert_eq!(
        field(&failure, "goal", OutputLanguage::English).as_str(),
        Ok("{1} != {1}")
    );
    assert!(
        rt.run_litex_code("by def {1} $proper_subset {1, 2}")
            .unwrap()
            .success
    );
}

#[test]
fn eval_failure_categories_are_exhaustive_and_localized() {
    use crate::execute::{
        ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecStmtResult,
    };
    for lang in [
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
        let rt = runtime(lang);
        for (failed, cause, category) in [
            (
                ExecEvalStmtFailed::UnsupportedExpression,
                "unsupported_expression",
                "unsupported",
            ),
            (
                ExecEvalStmtFailed::EvaluationFailed,
                "evaluation_failed",
                "evaluation",
            ),
            (
                ExecEvalStmtFailed::AlgoDispatchFailed,
                "algo_dispatch_failed",
                "algorithm_dispatch",
            ),
            (
                ExecEvalStmtFailed::DepthExceeded,
                "depth_exceeded",
                "depth_limit",
            ),
            (
                ExecEvalStmtFailed::CyclicAlgoCall,
                "cyclic_algo_call",
                "cyclic_evaluation",
            ),
            (
                ExecEvalStmtFailed::AggregateBudgetExceeded,
                "aggregate_budget_exceeded",
                "aggregate_budget",
            ),
            (
                ExecEvalStmtFailed::AggregateRangeOverflow,
                "aggregate_range_overflow",
                "aggregate_range",
            ),
        ] {
            let result = ExecStmtResult::Command(ExecCommandStmtResult::Eval(
                ExecEvalStmtResult::Failed(failed),
            ));
            let normal = super::project_stmt_normal(&result, &rt);
            let detailed = super::project_stmt_detailed(&result, &rt);
            let reason = field(&normal, "why_failed", lang);
            let failure = field(&reason, "failure", lang);
            assert_eq!(field(&failure, "cause", lang).as_str(), Ok(cause));
            assert_eq!(field(&detailed, "cause", lang).as_str(), Ok(cause));
            let diagnostic = field(&reason, "diagnostic", lang);
            assert_eq!(diagnostic, field(&detailed, "diagnostic", lang));
            assert_eq!(field(&diagnostic, "category", lang).as_str(), Ok(category));
            assert!(!field(&diagnostic, "message", lang)
                .as_str()
                .unwrap()
                .is_empty());
        }
    }
}

#[test]
fn nested_failed_declaration_keeps_its_source_and_rolls_back() {
    for lang in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(lang);
        let run = rt
            .run_litex_code("claim:\n    ? 1 = 1\n    sketch:\n        have x {1} = 2\n")
            .unwrap();
        assert!(!run.success && run.session_error.is_none());
        for projected in [
            super::project_stmt_normal(&run.statement_results[0], &rt),
            super::project_stmt_detailed(&run.statement_results[0], &rt),
        ] {
            assert!(
                has_statement_source(&projected, "have x {1} = 2", 4, lang),
                "{}",
                projected.stringify()
            );
        }
        assert!(rt.run_litex_code("have x {1} = 1").unwrap().success);
    }
}

fn has_statement_source(
    value: &JsonValue,
    statement: &str,
    line: usize,
    lang: OutputLanguage,
) -> bool {
    match value {
        JsonValue::Object(fields) => {
            if let Some(JsonValue::String(text)) =
                fields.get(&super::json_keys::localize_key("statement", lang))
            {
                if text == statement {
                    if let Some(source) =
                        fields.get(&super::json_keys::localize_key("source_location", lang))
                    {
                        return field(source, "path", lang).as_str() == Ok("<eval>")
                            && field(source, "line", lang) == JsonValue::Number(line as f64);
                    }
                }
            }
            fields
                .iter()
                .any(|(_, child)| has_statement_source(child, statement, line, lang))
        }
        JsonValue::Array(values) => values
            .iter()
            .any(|child| has_statement_source(child, statement, line, lang)),
        _ => false,
    }
}
