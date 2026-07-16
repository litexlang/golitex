use crate::prelude::*;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionLayer {
    Main,
    File(FileId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionMode {
    Verified,
    Trusted,
}

#[derive(Clone)]
pub struct ExecutionFrame {
    pub module_id: ModuleId,
    pub layer: ExecutionLayer,
    pub source_path: Rc<str>,
    pub execution_mode: ExecutionMode,
    pub local_environment_stack: Vec<Box<Environment>>,
}

impl ExecutionFrame {
    pub fn new(module_id: ModuleId, layer: ExecutionLayer, source_path: &str) -> Self {
        Self::new_with_mode(module_id, layer, source_path, ExecutionMode::Verified)
    }

    pub fn new_with_mode(
        module_id: ModuleId,
        layer: ExecutionLayer,
        source_path: &str,
        execution_mode: ExecutionMode,
    ) -> Self {
        ExecutionFrame {
            module_id,
            layer,
            source_path: Rc::from(source_path),
            execution_mode,
            local_environment_stack: vec![],
        }
    }
}
