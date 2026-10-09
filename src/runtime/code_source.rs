//! Source path and publication identity of parsed/executed code.

use std::fmt;
use std::path::PathBuf;

/// One source value for diagnostics, AST locations and symbol qualification.
///
/// Drives outermost (parse-scope-0) symbol qualification:
/// - `Eval` / `Repl` / `Real` → stay `Plain` (no publication stamp)
/// - `RootExport` / `ImportedExport` → `WithExportFileId` / `WithModAndExportFileId`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CodeSource {
    /// `-e <code>`: virtual Eval buffer, no source `.lit`.
    Eval,
    /// Bare REPL: interactive session, no source `.lit`.
    Repl,
    /// `-f` real file that is not an export slot (isolated / extra after exports).
    Real(PathBuf),
    /// Root module `LitexConfig.exports[export_file_id]`.
    RootExport {
        path: PathBuf,
        export_file_id: usize,
    },
    /// Imported module `exports[export_file_id]`.
    ImportedExport {
        path: PathBuf,
        global_mod_id: usize,
        export_file_id: usize,
    },
}

impl CodeSource {
    pub fn display_path(&self) -> PathBuf {
        match self {
            Self::Real(path)
            | Self::RootExport { path, .. }
            | Self::ImportedExport { path, .. } => path.clone(),
            Self::Eval => PathBuf::from("<eval>"),
            Self::Repl => PathBuf::from("<repl>"),
        }
    }

    pub fn name(&self) -> String {
        let path = self.display_path();
        path.file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
            .unwrap_or_else(|| path.to_string_lossy().into_owned())
    }

    pub fn promotes_outermost_symbols(&self) -> bool {
        match self {
            CodeSource::RootExport { .. } | CodeSource::ImportedExport { .. } => true,
            CodeSource::Eval | CodeSource::Repl | CodeSource::Real(_) => false,
        }
    }

    pub fn is_live_root_export(&self, export_file_id: usize) -> bool {
        match self {
            CodeSource::RootExport {
                export_file_id: live,
                ..
            } => *live == export_file_id,
            _ => false,
        }
    }

    pub fn is_live_imported_export(&self, global_mod_id: usize, export_file_id: usize) -> bool {
        match self {
            CodeSource::ImportedExport {
                global_mod_id: live_mod,
                export_file_id: live_export,
                ..
            } => *live_mod == global_mod_id && *live_export == export_file_id,
            _ => false,
        }
    }
}

impl fmt::Display for CodeSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Real(path)
            | Self::RootExport { path, .. }
            | Self::ImportedExport { path, .. } => {
                write!(f, "{}", path.display())
            }
            Self::Eval => write!(f, "<eval>"),
            Self::Repl => write!(f, "<repl>"),
        }
    }
}
