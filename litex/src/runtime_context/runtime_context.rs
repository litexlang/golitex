use std::fmt;
use std::collections::HashMap;
use crate::obj::Identifier;
use crate::common::keywords::MOD_NAME_SEPARATOR;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use crate::stmt::definition_stmt::DefPropStmt;
use crate::stmt::definition_stmt::DefStructStmt;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,
    pub builtin_environment: Box<Environment>,

    pub defined_identifier_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_structs: HashMap<String, DefStructStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a mut ModuleManager<'a>, environments: Vec<Box<Environment>>, builtin_environment: Box<Environment>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, structs: HashMap<String, DefStructStmt>, algorithms: HashMap<String, DefAlgoStmt>) -> Self {
        RuntimeContext { module_manager, environments, builtin_environment, defined_identifier_objs: objs, defined_props: props, defined_structs: structs, defined_algorithms: algorithms }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{\n")?;
        write!(f, "    module_manager: {}\n", self.module_manager)?;
        write!(f, "    environments: {:?}\n", self.environments.len())?;
        write!(f, "    builtin_environment: {}\n", self.builtin_environment)?;
        write!(f, "    objs: {:?}\n", self.defined_identifier_objs.len())?;
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

// 从env或者builtin_environment中获取 predicate 定义
impl<'a> RuntimeContext<'a> {
    /// 只读查找：用 predicate 名称从当前环境或 builtin 中取定义（供 Verifier 等 &self 场景使用）
    pub fn get_predicate_definition_by_name(&self, predicate_name: &str) -> Option<&DefPropStmt> {
        // 按 separator 拆分
        let parts = predicate_name.split(MOD_NAME_SEPARATOR).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }
        
        let result = self.environments.last().unwrap().defined_props.get(predicate_name);
        if result.is_some() {
            return result;
        }
        self.builtin_environment.defined_props.get(predicate_name)
    }

    pub fn is_identifier_defined(&self, identifier: &Identifier) -> bool {
        self.defined_identifier_objs.contains_key(&identifier.name)
    }
}
