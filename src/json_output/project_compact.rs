//! Project ExecStmtResult → Compact JSON (see README).
//!
//! Accepted: `statement_result` + `statement` only.
//! Failure: same + `fail_reason` with `phase` and optional `goal`.

use super::helper::{object, output_language, run_result_value, statement_result_value, string};
use super::json_keys::localize_key;
use super::project_normal::project_stmt_normal;
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

/// Build Compact feedback without projecting any successful statement.
pub fn project_run_compact(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    _target: &str,
    path: Option<&Path>,
) -> JsonValue {
    project_compact_runs(run, &[run], runtime, path)
}

pub(super) fn project_compact_runs(
    envelope: &RunLitexCodeResult,
    runs: &[&RunLitexCodeResult],
    runtime: &Runtime,
    path: Option<&Path>,
) -> JsonValue {
    let lang = output_language(runtime);
    let mut success = envelope.success;
    let mut errors = Vec::new();
    for run in runs {
        if !run.success {
            success = false;
            errors.extend(super::feedback::source_errors(run, runtime));
        }
    }
    if let Some(error) = &envelope.session_error {
        for diagnostic in super::feedback::session_errors(error, path, lang) {
            if !errors.contains(&diagnostic) {
                errors.push(diagnostic);
            }
        }
    }
    verdict(success, errors, lang)
}

pub(super) fn verdict(success: bool, errors: Vec<JsonValue>, lang: OutputLanguage) -> JsonValue {
    let mut fields = vec![("run_result", run_result_value(success))];
    if !success {
        fields.push(("errors", JsonValue::Array(errors)));
    }
    object(lang, fields)
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
