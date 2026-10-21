//! Project ExecStmtResult → Compact JSON (see README).
//!
//! Accepted: `statement_result` + `statement` only.
//! Failure: same + `fail_reason` with `phase` and optional `goal`.

use super::helper::{
    object, output_language, run_result_value, session_termination_value, statement_result_value,
    string,
};
use super::json_keys::localize_key;
use super::project_normal::{project_run_statements_normal, project_stmt_normal, OutputDetail};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::OutputLanguage;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;
use std::path::Path;

/// Project one statement result at Compact detail.
pub fn project_stmt_compact(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    let lang = output_language(runtime);
    thin_to_compact(lang, &project_stmt_normal(result, runtime))
}

/// Build the Compact run envelope while Runtime still holds cited facts.
pub fn project_run_compact(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let lang = output_language(runtime);
    let normal = project_run_statements_normal(run, runtime);
    let (_, errors) = super::feedback::summarize_statements(normal.clone(), lang);
    let statement_results = normal
        .iter()
        .map(|stmt| thin_to_compact(lang, stmt))
        .collect();
    let path_value = match path {
        Some(p) => string(p.display().to_string()),
        None => JsonValue::Null,
    };
    let termination = match &run.session_error {
        None => JsonValue::Null,
        Some(err) => session_termination_value(err, lang),
    };
    object(
        lang,
        vec![
            ("kind", string("run")),
            ("run_result", run_result_value(run.success)),
            ("target", string(target)),
            ("path", path_value),
            ("detail", string(OutputDetail::Compact.as_str())),
            (
                "language",
                string(runtime.launch_command.output_language().as_str()),
            ),
            ("statement_results", JsonValue::Array(statement_results)),
            ("errors", JsonValue::Array(errors)),
            (
                "session_terminated",
                JsonValue::Bool(run.session_error.is_some()),
            ),
            ("termination", termination),
        ],
    )
}

fn thin_to_compact(lang: OutputLanguage, normal_stmt: &JsonValue) -> JsonValue {
    let Ok(map) = normal_stmt.as_object() else {
        return object(
            lang,
            vec![
                ("statement_result", statement_result_value(false)),
                ("statement", string("<invalid>")),
            ],
        );
    };
    let statement_result_key = localize_key("statement_result", lang);
    let statement_key = localize_key("statement", lang);
    let why_failed_key = localize_key("why_failed", lang);

    let statement_result = map
        .get(&statement_result_key)
        .cloned()
        .unwrap_or_else(|| statement_result_value(false));
    let statement = map
        .get(&statement_key)
        .cloned()
        .unwrap_or_else(|| string(""));

    if matches!(&statement_result, JsonValue::String(value) if value == "accepted") {
        return object(
            lang,
            vec![
                ("statement_result", statement_result),
                ("statement", statement),
            ],
        );
    }

    let fail_reason = match map.get(&why_failed_key) {
        Some(why) => thin_fail_reason(lang, why),
        None => object(lang, vec![("phase", string(default_fail_phase(lang)))]),
    };
    object(
        lang,
        vec![
            ("statement_result", statement_result),
            ("statement", statement),
            ("fail_reason", fail_reason),
        ],
    )
}

fn thin_fail_reason(lang: OutputLanguage, why: &JsonValue) -> JsonValue {
    let Ok(map) = why.as_object() else {
        return object(lang, vec![("phase", string(default_fail_phase(lang)))]);
    };
    let phase_key = localize_key("phase", lang);
    let goal_key = localize_key("goal", lang);
    let type_key = localize_key("type", lang);

    let mut entries: Vec<(&str, JsonValue)> = Vec::new();
    if let Some(phase) = map.get(&phase_key) {
        entries.push(("phase", phase.clone()));
    } else if let Some(type_tag) = map.get(&type_key) {
        entries.push(("phase", type_tag.clone()));
    } else {
        entries.push(("phase", string(default_fail_phase(lang))));
    }
    if let Some(goal) = map.get(&goal_key) {
        entries.push(("goal", goal.clone()));
    }
    object(lang, entries)
}

fn default_fail_phase(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "failed",
        OutputLanguage::ChineseTraditional => "失敗",
        OutputLanguage::French => "Échec",
        OutputLanguage::Russian => "Неудача",
        OutputLanguage::Spanish => "Fallo",
        OutputLanguage::Arabic => "فشل",
        OutputLanguage::Japanese => "失敗",
        OutputLanguage::Korean => "실패",
        OutputLanguage::Vietnamese => "Thất bại",

        OutputLanguage::Chinese => "失败",
    }
}
