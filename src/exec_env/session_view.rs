//! Session snapshot for litex_knowledge_base watermarks.

use crate::runtime::{CodeSource, GlobalIds};

/// Records GlobalIds (and CodeSource) when Runtime opens this file-level ExecEnv.
///
/// Nested / statement-local ExecEnvs leave `ExecEnv.session_view = None`.
/// Merge never copies this. Leave watermark is stamped when the file finishes.
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
