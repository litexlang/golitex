use std::fmt;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use std::collections::HashMap;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefSetTemplateStmt;
use crate::define_algorithm_stmt::DefineAlgorithmStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,

    pub defined_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_set_templates: HashMap<String, DefSetTemplateStmt>,
    pub defined_algorithms: HashMap<String, DefineAlgorithmStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a mut ModuleManager<'a>, environments: Vec<Box<Environment>>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefineAlgorithmStmt>) -> Self {
        RuntimeContext { module_manager, environments, defined_objs: objs, defined_props: props, defined_set_templates: set_templates, defined_algorithms: algorithms }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{\n")?;
        write!(f, "    module_manager: {}\n", self.module_manager)?;
        write!(f, "    environments: {:?}\n", self.environments.len())?;
        write!(f, "    objs: {:?}\n", self.defined_objs.len())?;
        write!(f, "    props: {:?}\n", self.defined_props.len())?;
        write!(f, "    set_templates: {:?}\n", self.defined_set_templates.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "}}")
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn top_level_env(&mut self) -> &mut Environment {
        self.environments.last_mut().unwrap()
    }
}