//! On-disk paths for `__litex_knowledge_base__/`.

use std::path::{Path, PathBuf};

pub const KB_DIR_NAME: &str = "__litex_knowledge_base__";
pub const MANIFEST_FILE_NAME: &str = "manifest.json";
pub const EXPORTS_DIR_NAME: &str = "exports";
pub const DEFINITIONS_FILE_NAME: &str = "definitions.json";

/// Litex KB compatibility revision. Bump for incompatible layout or verifier
/// corrections that invalidate previously checked definition/theorem products.
// Revision 8 rechecks products that still parsed retired tuple/cart shape
// predicates, dimensions, projections or square-bracket object indexing.
// Revision 7 rechecks products carrying retired tuple shape/index inferences
// or struct bridges, so warm imports cannot revive the old producers.
// Revision 6 also invalidates products proved by the old empty-domain graph
// nonemptiness and unguarded constant-image rules. Revision 5 corrected weak
// function-space membership and Cartesian dimensions. The wire format is
// unchanged; old products must be checked again under all domain contracts.
pub const KB_ABI: &str = "8";

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
