//! Stateful statement-result renderer and public entrypoint.

use super::*;

/// Deterministic structural JSON for the recursive runtime result.
///
/// This visitor reads the result only. It does not query `Runtime`, infer a
/// proof rule from a diagnostic label, or flatten child results into a legacy
/// output DTO.
pub fn render_statement_result_json(result: &StmtResult) -> String {
    render_json_value(&StatementResultRenderer::default().stmt_result(result), 0)
}

#[derive(Default)]
pub(in super::super) struct StatementResultRenderer {
    pub(super) shared_fact_ids: HashMap<usize, String>,
    pub(super) next_shared_fact_id: usize,
    pub(super) shared_wd_obj_ids: HashMap<usize, String>,
    pub(super) next_shared_wd_obj_id: usize,
}
