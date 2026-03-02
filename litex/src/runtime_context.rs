use crate::module_manager::ModuleManager;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a ModuleManager<'a>,
}