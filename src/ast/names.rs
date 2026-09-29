//! Framework AST name shapes.
//!
//! Qualified atoms use **indices** (not surface alias strings). Two id spaces:
//!
//! - `export_file_id` — index in **that module's own** `LitexConfig.exports`
//!   (order fixed by the imported/current module's config).
//! - `global_mod_id` — index in **this run's** `GlobalModuleManager.imports`
//!   (order fixed by the global mount table).
//!
//! Surface `a::b` / `a::b::c` / `a:::b` are elaborated via GlobalModuleManager.
//! Definition-side store keys remain unqualified `PlainName`.
//! Plain object/binder occurrences carry [`BoundName`] / `IdentifierId`.

use std::fmt;

use crate::runtime::runtime_ids::IdentifierId;

/// Unqualified local name (`foo`). Alias of `String`.
pub type PlainName = String;

/// Local binder / defined plain name with a parse-allocated occurrence id.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundName {
    pub id: IdentifierId,
    pub name: PlainName,
}

impl BoundName {
    pub fn new(id: IdentifierId, name: PlainName) -> Self {
        Self { id, name }
    }

    pub fn ir_string(&self) -> String {
        format!("#{}#{}", self.id.value(), self.name)
    }
}

impl fmt::Display for BoundName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// Qualified or plain atom name. Identity for equals is ids + `name`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomicName {
    Plain {
        name: PlainName,
    },

    /// `a::b` in the **current** module.
    ///
    /// `export_file_id` = index in **current** module's `LitexConfig.exports`
    /// (that module's config decides the numbering; not the global MM).
    WithExportFileId {
        export_file_id: usize,
        name: PlainName,
    },

    /// `a::b::c` or elaborated `a:::b` — reference into an **imported** module.
    ///
    /// - `global_mod_id` = index in `GlobalModuleManager.imports` (this run's
    ///   global table assigns the number; local alias `T`/`G` both map here).
    /// - `export_file_id` = index in **that imported module's**
    ///   `LitexConfig.exports` (that module's config assigns the number).
    WithModAndExportFileId {
        global_mod_id: usize,
        export_file_id: usize,
        name: PlainName,
    },
}

impl AtomicName {
    /// Placeholder spelling for IR/debug without a module table.
    /// Prefer display through `GlobalModuleManager` when showing to users.
    pub fn display_string(&self) -> String {
        match self {
            AtomicName::Plain { name } => name.clone(),
            AtomicName::WithExportFileId {
                export_file_id,
                name,
            } => format!("f{export_file_id}::{name}"),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => format!("m{global_mod_id}::f{export_file_id}::{name}"),
        }
    }

    pub fn plain(name: PlainName) -> Self {
        AtomicName::Plain { name }
    }

    // Unqualified local spelling shared by Plain and file-root qualified forms.
    pub fn local_name(&self) -> &str {
        match self {
            AtomicName::Plain { name } => name.as_str(),
            AtomicName::WithExportFileId { name, .. } => name.as_str(),
            AtomicName::WithModAndExportFileId { name, .. } => name.as_str(),
        }
    }
}

impl fmt::Display for AtomicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_string())
    }
}
