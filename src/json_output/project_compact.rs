//! Project ExecStmtResult → Compact JSON (see README).
//!
//! Success: `success` + `statement` only.
//! Failure: same + `fail_reason` with `phase` and optional `goal`.

use super::helper::{bool_value, object, output_language, string};
use super::json_keys::localize_key;
use super::project_normal::{project_stmt_normal, OutputDetail};
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
    let statement_results: Vec<JsonValue> = run
        .statement_results
        .iter()
        .map(|stmt| project_stmt_compact(stmt, runtime))
        .collect();
    let path_value = match path {
        Some(p) => string(p.display().to_string()),
        None => JsonValue::Null,
    };
    let session_error = match &run.session_error {
        None => JsonValue::Null,
        Some(err) => string(format!("{err:?}")),
    };
    object(
        lang,
        vec![
            ("kind", string("run")),
            ("success", bool_value(run.success)),
            ("target", string(target)),
            ("path", path_value),
            ("detail", string(OutputDetail::Compact.as_str())),
            (
                "language",
                string(runtime.launch_command.output_language().as_str()),
            ),
            ("statement_results", JsonValue::Array(statement_results)),
            ("session_error", session_error),
        ],
    )
}

fn thin_to_compact(lang: OutputLanguage, normal_stmt: &JsonValue) -> JsonValue {
    let Ok(map) = normal_stmt.as_object() else {
        return object(
            lang,
            vec![
                ("success", bool_value(false)),
                ("statement", string("<invalid>")),
            ],
        );
    };
    let success_key = localize_key("success", lang);
    let statement_key = localize_key("statement", lang);
    let why_failed_key = localize_key("why_failed", lang);

    let success = map
        .get(&success_key)
        .cloned()
        .unwrap_or(JsonValue::Bool(false));
    let statement = map
        .get(&statement_key)
        .cloned()
        .unwrap_or_else(|| string(""));

    if matches!(success, JsonValue::Bool(true)) {
        return object(
            lang,
            vec![("success", success), ("statement", statement)],
        );
    }

    let fail_reason = match map.get(&why_failed_key) {
        Some(why) => thin_fail_reason(lang, why),
        None => object(
            lang,
            vec![("phase", string(default_fail_phase(lang)))],
        ),
    };
    object(
        lang,
        vec![
            ("success", success),
            ("statement", statement),
            ("fail_reason", fail_reason),
        ],
    )
}

fn thin_fail_reason(lang: OutputLanguage, why: &JsonValue) -> JsonValue {
    let Ok(map) = why.as_object() else {
        return object(
            lang,
            vec![("phase", string(default_fail_phase(lang)))],
        );
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
        OutputLanguage::Chinese => "失败",
    }
}
