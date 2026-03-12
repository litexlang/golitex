use std::fmt;
use std::collections::HashMap;
use crate::obj::Identifier;
use crate::common::keywords::MOD_SIGN;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use crate::stmt::definition_stmt::DefPropStmt;
use crate::stmt::definition_stmt::DefStructStmt;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::DefPropWithoutMeaningStmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,
    pub builtin_environment: Box<Environment>,

    pub defined_identifier_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_props_without_meaning: HashMap<String, DefPropWithoutMeaningStmt>,
    pub defined_structs: HashMap<String, DefStructStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new(module_manager: &'a mut ModuleManager<'a>, environments: Vec<Box<Environment>>, builtin_environment: Box<Environment>, objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, props_without_meaning: HashMap<String, DefPropWithoutMeaningStmt>, structs: HashMap<String, DefStructStmt>, algorithms: HashMap<String, DefAlgoStmt>) -> Self {
        RuntimeContext { module_manager, environments, builtin_environment, defined_identifier_objs: objs, defined_props: props, defined_structs: structs, defined_algorithms: algorithms, defined_props_without_meaning: props_without_meaning }
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
        let result = self.environments.last_mut();
        match result {
            Some(e) => e,
            None => unreachable!("no top level environment"),
        }
    }
}

// 从env或者builtin_environment中获取 predicate 定义
impl<'a> RuntimeContext<'a> {
    /// 只读查找：用 predicate 名称从当前环境或 builtin 中取定义（供 Verifier 等 &self 场景使用）
    pub fn get_predicate_definition_by_name(&self, predicate_name: &str) -> Option<&DefPropStmt> {
        // 按 separator 拆分
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        let top_environment = match self.environments.last() {
            Some(environment) => environment,
            None => unreachable!("no top level environment"),
        };

        if let Some(definition) = top_environment.defined_props.get(predicate_name) {
            return Some(definition);
        }

        self.builtin_environment.defined_props.get(predicate_name)
    }

    pub fn get_set_struct_definition_by_name(&self, set_struct_name: &str) -> Option<&DefStructStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        let top_environment = match self.environments.last() {
            Some(environment) => environment,
            None => unreachable!("no top level environment"),
        };

        if let Some(definition) = top_environment.defined_structs.get(set_struct_name) {
            return Some(definition);
        }

        self.builtin_environment.defined_structs.get(set_struct_name)
    }

    pub fn is_defined_identifier_obj(&self, identifier: &Identifier) -> bool {
        self.defined_identifier_objs.contains_key(&identifier.name)
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        self.defined_identifier_objs.contains_key(name) || self.defined_props.contains_key(name) || self.defined_props_without_meaning.contains_key(name) || self.defined_structs.contains_key(name) || self.defined_algorithms.contains_key(name)
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn new_env(&mut self) {
        let new_env = Box::new(Environment::new_empty_env());
        self.environments.push(new_env);
    }

    pub fn delete_env(&mut self) {
        let last_env = self.environments.last();

        match last_env {
            None => {unreachable!("no top level environment")}
            Some(last_env) => {
                for defined_identifier_obj in last_env.defined_identifier_objs.iter() {
                    self.defined_identifier_objs.remove(defined_identifier_obj.0);
                }
                for defined_prop in last_env.defined_props.iter() {
                    self.defined_props.remove(defined_prop.0);
                }
                for defined_prop_without_meaning in last_env.defined_props_without_meaning.iter() {
                    self.defined_props_without_meaning.remove(defined_prop_without_meaning.0);
                }
                for defined_struct in last_env.defined_structs.iter() {
                    self.defined_structs.remove(defined_struct.0);
                }
                for defined_algorithm in last_env.defined_algorithms.iter() {
                    self.defined_algorithms.remove(defined_algorithm.0);
                }
                
                self.environments.pop();
            }
        }
    }
}