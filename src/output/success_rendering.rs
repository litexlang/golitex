use crate::prelude::{OutputStyle, Runtime, StmtResult};

use super::display_normalization::finalize_display_text_with_optional_strip;

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    result: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    display_stmt_exec_result_json_with_style(
        runtime,
        result,
        runtime.effective_output_style(),
        strip_free_param_tags,
    )
}

/// JSON v2 is the statement result itself, so compact/normal/detailed no
/// longer project three different semantic shapes. The style parameter stays
/// in this internal signature while callers migrate away from it.
pub fn display_stmt_exec_result_json_with_style(
    _runtime: &Runtime,
    result: &StmtResult,
    _output_style: OutputStyle,
    strip_free_param_tags: bool,
) -> String {
    let raw = super::display_stmt_result_json_v2(result);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}
