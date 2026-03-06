use std::fmt;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use std::collections::HashMap;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefStructStmt;
use crate::define_algorithm_stmt::DefAlgoStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,

    pub defined_atom_names: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_structs: HashMap<String, DefStructStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a mut ModuleManager<'a>, environments: Vec<Box<Environment>>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, structs: HashMap<String, DefStructStmt>, algorithms: HashMap<String, DefAlgoStmt>) -> Self {
        RuntimeContext { module_manager, environments, defined_atom_names: objs, defined_props: props, defined_structs: structs, defined_algorithms: algorithms }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{\n")?;
        write!(f, "    module_manager: {}\n", self.module_manager)?;
        write!(f, "    environments: {:?}\n", self.environments.len())?;
        write!(f, "    objs: {:?}\n", self.defined_atom_names.len())?;
        write!(f, "    props: {:?}\n", self.defined_props.len())?;
        write!(f, "    structs: {:?}\n", self.defined_structs.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "}}")
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn top_level_env(&mut self) -> &mut Environment {
        self.environments.last_mut().unwrap()
    }
}
