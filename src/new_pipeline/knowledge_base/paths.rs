//! On-disk paths for `__litex_knowledge_base__/`.

use std::path::{Path, PathBuf};

pub const KB_DIR_NAME: &str = "__litex_knowledge_base__";
pub const MANIFEST_FILE_NAME: &str = "manifest.json";
pub const EXPORTS_DIR_NAME: &str = "exports";
pub const DEFINITIONS_FILE_NAME: &str = "definitions.json";

/// Litex KB on-disk ABI. Bump when wire/manifest layout changes incompatibly.
pub const KB_ABI: &str = "1";

pub fn kb_dir(module_root: &Path) -> PathBuf {
    module_root.join(KB_DIR_NAME)
}

pub fn manifest_path(module_root: &Path) -> PathBuf {
    kb_dir(module_root).join(MANIFEST_FILE_NAME)
}

pub fn export_definitions_path(module_root: &Path, export_file_id: usize) -> PathBuf {
    kb_dir(module_root)
        .join(EXPORTS_DIR_NAME)
        .join(export_file_id.to_string())
        .join(DEFINITIONS_FILE_NAME)
}
