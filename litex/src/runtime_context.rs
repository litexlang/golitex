use std::fmt;
use crate::keywords;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use std::collections::HashMap;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefSetTemplateStmt;
use crate::define_algorithm_stmt::DefAlgoStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,

    pub defined_atom_names: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_set_templates: HashMap<String, DefSetTemplateStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a mut ModuleManager<'a>, environments: Vec<Box<Environment>>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefAlgoStmt>) -> Self {
        RuntimeContext { module_manager, environments, defined_atom_names: objs, defined_props: props, defined_set_templates: set_templates, defined_algorithms: algorithms }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{\n")?;
        write!(f, "    module_manager: {}\n", self.module_manager)?;
        write!(f, "    environments: {:?}\n", self.environments.len())?;
        write!(f, "    objs: {:?}\n", self.defined_atom_names.len())?;
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

impl<'a> RuntimeContext<'a> {
    pub fn is_unused_valid_atom_name(&self, atom_name: &str) -> bool {
        // 没被定义过
        // 不是 keyword 的 atom name 才能被使用
        // 开头不能是数字，且只能全是字母或数字或下划线
        !self.defined_atom_names.contains_key(atom_name) && !keywords::is_keyword(atom_name) && atom_name.chars().next().unwrap().is_alphabetic() && atom_name.chars().all(|c| c.is_alphanumeric() || c == '_')
    }
}