//! Stateful JSON visitor model and public rendering entrypoint.

use super::*;

/// Deterministic structural JSON for the recursive runtime result.
///
/// This visitor reads the result only. It does not query `Runtime`, infer a
/// proof rule from a diagnostic label, or flatten child results into a legacy
/// output DTO.
pub fn display_stmt_result_json_v2(result: &StmtResult) -> String {
    render_json_value(&StmtResultJsonV2::default().stmt_result(result), 0)
}

#[derive(Default)]
pub(in super::super) struct StmtResultJsonV2 {
    pub(super) shared_fact_ids: HashMap<usize, String>,
    pub(super) next_shared_fact_id: usize,
    pub(super) shared_wd_obj_ids: HashMap<usize, String>,
    pub(super) next_shared_wd_obj_id: usize,
}
