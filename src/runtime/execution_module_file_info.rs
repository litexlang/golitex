use crate::module_system::{FileId, ModuleId};
use std::rc::Rc;

/// Identifies the registered module file executed by an [`ExecutionFrame`](super::ExecutionFrame).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionModuleFileInfo {
    pub module_id: ModuleId,
    pub file_id: FileId,
    pub source_path: Rc<str>,
}

impl ExecutionModuleFileInfo {
    pub fn new(module_id: ModuleId, file_id: FileId, source_path: Rc<str>) -> Self {
        Self {
            module_id,
            file_id,
            source_path,
        }
    }
}
