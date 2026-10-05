//! On-disk paths for `__litex_knowledge_base__/`.

use std::path::{Path, PathBuf};

pub const KB_DIR_NAME: &str = "__litex_knowledge_base__";
pub const MANIFEST_FILE_NAME: &str = "manifest.json";
pub const EXPORTS_DIR_NAME: &str = "exports";
pub const DEFINITIONS_FILE_NAME: &str = "definitions.json";

/// Litex KB compatibility revision. Bump for incompatible layout or verifier
/// corrections that invalidate previously checked definition/theorem products.
// Revision 5 invalidates products checked with weak function-space membership
// or Cartesian construction dimensions. The existing wire format is unchanged;
// old products must be checked again under the complete-domain contract.
pub const KB_ABI: &str = "5";

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
