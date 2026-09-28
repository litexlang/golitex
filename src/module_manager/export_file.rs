//! Completed export file + its top-level ExecEnv.

use crate::exec_env::exec_env::ExecEnv;
use std::path::PathBuf;

/// One finished export `.lit` and the env it produced.
///
/// Index in `root_exports` or `ImportedModule.export_files_and_their_env`
/// is that module's `file_id`.
pub struct ExportFileAndItsExecEnv {
    pub name: String,
    pub path: PathBuf,
    pub exec_env: Box<ExecEnv>,
}

impl ExportFileAndItsExecEnv {
    pub fn new(name: String, path: PathBuf, exec_env: Box<ExecEnv>) -> Self {
        Self {
            name,
            path,
            exec_env,
        }
    }
}
