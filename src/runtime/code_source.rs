//! Where the currently running code came from (new_pipeline live session).

/// Live provenance of the code being parsed/executed.
///
/// Drives outermost (parse-scope-0) symbol qualification:
/// - `Eval` / `Repl` / `StandaloneFile` → stay `Plain` (no publication stamp)
/// - `RootExport` / `ImportedExport` → `WithExportFileId` / `WithModAndExportFileId`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CodeSource {
    /// `-e <code>`: virtual Eval buffer, no source `.lit`.
    Eval,
    /// Bare REPL: interactive session, no source `.lit`.
    Repl,
    /// `-f` real file that is not an export slot (isolated / extra after exports).
    StandaloneFile,
    /// Root module `LitexConfig.exports[export_file_id]`.
    RootExport { export_file_id: usize },
    /// Imported module `exports[export_file_id]`.
    ImportedExport {
        global_mod_id: usize,
        export_file_id: usize,
    },
}

impl CodeSource {
    pub fn promotes_outermost_symbols(&self) -> bool {
        match self {
            CodeSource::RootExport { .. } | CodeSource::ImportedExport { .. } => true,
            CodeSource::Eval | CodeSource::Repl | CodeSource::StandaloneFile => false,
        }
    }

    pub fn is_live_root_export(&self, export_file_id: usize) -> bool {
        match self {
            CodeSource::RootExport {
                export_file_id: live,
            } => *live == export_file_id,
            _ => false,
        }
    }

    pub fn is_live_imported_export(&self, global_mod_id: usize, export_file_id: usize) -> bool {
        match self {
            CodeSource::ImportedExport {
                global_mod_id: live_mod,
                export_file_id: live_export,
            } => *live_mod == global_mod_id && *live_export == export_file_id,
            _ => false,
        }
    }
}
