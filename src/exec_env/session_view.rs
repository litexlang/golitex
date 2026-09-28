//! Session snapshot for a file-level ExecEnv (parse/exec stack index 0).

use crate::runtime::{CodeSource, GlobalIds};

/// Frozen view of the live Runtime session when a **file-level** ExecEnv opens.
///
/// Nested / statement-local ExecEnvs leave `ExecEnv.session_view = None` —
/// they inherit the file env's publication and id range context.
/// Merge never copies this.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecEnvSessionView {
    pub global_ids_at_enter: GlobalIds,
    pub global_ids_at_leave: Option<GlobalIds>,
    pub code_source: CodeSource,
}

impl ExecEnvSessionView {
    pub fn new(global_ids_at_enter: GlobalIds, code_source: CodeSource) -> Self {
        Self {
            global_ids_at_enter,
            global_ids_at_leave: None,
            code_source,
        }
    }

    pub fn stamp_leave(&mut self, global_ids: GlobalIds) {
        self.global_ids_at_leave = Some(global_ids);
    }
}
