use crate::prelude::{Runtime, RuntimeError, StmtResult};

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    crate::output::display_stmt_exec_result_json(runtime, r, strip_free_param_tags)
}

pub fn display_runtime_error_json(
    runtime: &Runtime,
    error: &RuntimeError,
    strip_free_param_tags: bool,
) -> String {
    crate::output::display_runtime_error_json(runtime, error, strip_free_param_tags)
}
