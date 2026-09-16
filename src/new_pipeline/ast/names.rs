//! Framework AST name shapes for new_pipeline.
//!
//! Qualified atoms use module/export **indices** (not surface alias strings):
//! `name` | `file_id::name` | `mod_id::file_id::name`
//! Surface `a::b` / `a::b::c` / `a:::b` are elaborated via GlobalModuleManager.
//!
//! Definition-side store keys remain unqualified `PlainName`.

use std::fmt;

/// Unqualified local name (`foo`). Alias of `String`.
pub type PlainName = String;

/// Qualified or plain atom name. Identity for quals is ids + `name`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomicName {
    Plain {
        name: PlainName,
    },
    /// Current module: `a::b` → export index + symbol.
    WithExportFileId {
        file_id: usize, // file index of that file in the litex.config of corresponding module
        name: PlainName,
    },
    /// Import: `a::b::c` / elaborated `a:::b` → global mod index + export index + symbol.
    WithModAndExportFileId {
        mod_id: usize,  // index of that module inside global module manager
        file_id: usize, // file index of that file in the litex.config of corresponding module
        name: PlainName,
    },
}

impl AtomicName {
    /// Placeholder spelling for IR/debug without a module table.
    /// Prefer display through `GlobalModuleManager` when showing to users.
    pub fn display_string(&self) -> String {
        match self {
            AtomicName::Plain { name } => name.clone(),
            AtomicName::WithExportFileId { file_id, name } => format!("f{file_id}::{name}"),
            AtomicName::WithModAndExportFileId {
                mod_id,
                file_id,
                name,
            } => format!("m{mod_id}::f{file_id}::{name}"),
        }
    }

    pub fn plain(name: PlainName) -> Self {
        AtomicName::Plain { name }
    }
}

impl fmt::Display for AtomicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_string())
    }
}
