use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionMode {
    RequireVerification,
    Trusted,
}

#[derive(Clone)]
pub struct ExecutionFrame {
    pub module_file_info: ExecutionModuleFileInfo,
    pub execution_mode: ExecutionMode,
    pub local_environment_stack: Vec<Box<Environment>>,
}

impl ExecutionFrame {
    pub fn new(module_file_info: ExecutionModuleFileInfo) -> Self {
        Self::new_with_mode(module_file_info, ExecutionMode::RequireVerification)
    }

    pub fn new_with_mode(
        module_file_info: ExecutionModuleFileInfo,
        execution_mode: ExecutionMode,
    ) -> Self {
        ExecutionFrame {
            module_file_info,
            execution_mode,
            local_environment_stack: vec![],
        }
    }
}
