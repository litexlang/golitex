use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionMode {
    Verified,
    Trusted,
}

#[derive(Clone)]
pub struct ExecutionFrame {
    pub module_file_info: ExecutionModuleFileInfo,
    pub execution_mode: ExecutionMode,
    pub local_environment_stack: Vec<Box<Environment>>,
    pub parse_context: ParseContext,
    /// A per-source, validated unique index. Qualified names and field names
    /// deliberately bypass it.
    pub bare_symbols: HashMap<String, BareSymbol>,
}

impl ExecutionFrame {
    pub fn new(module_file_info: ExecutionModuleFileInfo) -> Self {
        Self::new_with_mode(module_file_info, ExecutionMode::Verified)
    }

    pub fn new_with_mode(
        module_file_info: ExecutionModuleFileInfo,
        execution_mode: ExecutionMode,
    ) -> Self {
        ExecutionFrame {
            module_file_info,
            execution_mode,
            local_environment_stack: vec![],
            parse_context: ParseContext::new(),
            bare_symbols: HashMap::new(),
        }
    }
}
