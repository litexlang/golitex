use crate::prelude::*;

use super::display_normalization::finalize_display_text_with_optional_strip;
use super::json_value::JsonValue;
use super::{render_runtime_error_json, render_statement_result_json};

#[deprecated(note = "use `render_statement_result_json`")]
pub fn display_stmt_result_json_v2(result: &StmtResult) -> String {
    render_statement_result_json(result)
}

#[deprecated(note = "use `render_statement_result_json`")]
pub fn display_stmt_exec_result_json(
    _runtime: &Runtime,
    result: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    finalize_display_text_with_optional_strip(
        render_statement_result_json(result),
        strip_free_param_tags,
    )
}

#[deprecated(note = "use `render_runtime_error_json`")]
pub fn display_runtime_error_json(
    runtime: &Runtime,
    error: &RuntimeError,
    strip_free_param_tags: bool,
) -> String {
    render_runtime_error_json(runtime, error, strip_free_param_tags)
}

#[deprecated(note = "the runtime parameter was unused; structured unknown rendering is internal")]
pub fn unknown_result_json_value(
    _runtime: &Runtime,
    unknown_result: &RuntimeErrorUnknownResult,
    output_detail: OutputDetail,
) -> JsonValue {
    super::runtime_error::render_unknown_result_json_value(unknown_result, output_detail)
}
