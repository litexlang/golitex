//! Repository discovery targets.

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RepositoryFileTarget {
    Module(ModuleId),
    File {
        module_id: ModuleId,
        file_id: FileId,
    },
}
