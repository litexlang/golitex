use std::fmt;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use std::collections::HashMap;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefSetTemplateStmt;
use crate::define_algorithm_stmt::DefineAlgorithmStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,
    pub objs: HashMap<String, ()>,
    pub props: HashMap<String, DefPropStmt>,
    pub set_templates: HashMap<String, DefSetTemplateStmt>,
    pub algorithms: HashMap<String, DefineAlgorithmStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a ModuleManager<'a>, environments: Vec<Box<Environment>>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefineAlgorithmStmt>) -> Self {
        RuntimeContext { module_manager, environments, objs, props, set_templates, algorithms }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{")?;
        write!(f, "module_manager: {}", self.module_manager)?;
        write!(f, "environments: {:?}", self.environments.len())?;
        write!(f, "objs: {:?}", self.objs.len())?;
        write!(f, "props: {:?}", self.props.len())?;
        write!(f, "set_templates: {:?}", self.set_templates.len())?;
        write!(f, "algorithms: {:?}", self.algorithms.len())?;
        write!(f, "}}")
    }
}