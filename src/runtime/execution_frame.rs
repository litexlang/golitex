use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionLayer {
    Builtin,
    Main,
    File(FileEnvId),
}

#[derive(Clone)]
pub struct ExecutionFrame {
    pub module_id: Option<ModuleId>,
    pub layer: ExecutionLayer,
    pub source_path: Rc<str>,
    pub local_environment_stack: Vec<Box<Environment>>,
    pub active_local_imports: HashMap<String, ImportTarget>,
}

impl ExecutionFrame {
    pub fn new_builtin() -> Self {
        ExecutionFrame {
            module_id: None,
            layer: ExecutionLayer::Builtin,
            source_path: Rc::from(BUILTIN_CODE_PATH),
            local_environment_stack: vec![],
            active_local_imports: HashMap::new(),
        }
    }

    pub fn new(module_id: ModuleId, layer: ExecutionLayer, source_path: &str) -> Self {
        ExecutionFrame {
            module_id: Some(module_id),
            layer,
            source_path: Rc::from(source_path),
            local_environment_stack: vec![],
            active_local_imports: HashMap::new(),
        }
    }
}
