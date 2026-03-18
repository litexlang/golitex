use std::fmt;
use std::collections::HashMap;
use crate::obj::{Identifier, Atom};
use crate::common::keywords::{MOD_SIGN, is_builtin_identifier_obj};
use crate::error::StmtError;
use crate::infer::InferResult;
use crate::result::NonErrStmtExecResult;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use crate::stmt::definition_stmt::DefPropStmt;
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::DefPropWithoutMeaningStmt;
use crate::obj::FnSetObj;
use crate::common::defaults::DEFAULT_LINE_FILE;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environments: Vec<Box<Environment>>,
    pub builtin_environment: &'a mut Environment,

    pub defined_identifier_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_props_without_meaning: HashMap<String, DefPropWithoutMeaningStmt>,
    pub defined_structs_with_fields: HashMap<String, DefStructWithFieldsStmt>,
    pub defined_structs_with_no_field: HashMap<String, DefStructWithNoFieldStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,
}

impl<'a> RuntimeContext<'a> {
    pub fn new_empty_runtime_context_with_one_env(module_manager: &'a mut ModuleManager<'a>, builtin_environment: &'a mut Environment) -> Self {
        let new_env = Box::new(Environment::new_empty_env());
        RuntimeContext { module_manager, environments: vec![new_env], builtin_environment, defined_identifier_objs: HashMap::new(), defined_props: HashMap::new(), defined_props_without_meaning: HashMap::new(), defined_structs_with_fields: HashMap::new(), defined_structs_with_no_field: HashMap::new(), defined_algorithms: HashMap::new() }
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
        write!(f, "    structs_with_fields: {:?}\n", self.defined_structs_with_fields.len())?;
        write!(f, "    structs_with_no_field: {:?}\n", self.defined_structs_with_no_field.len())?;
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

impl<'a> RuntimeContext<'a> {
    pub fn get_predicate_definition_by_name(&self, predicate_name: &str) -> Option<&DefPropStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_props.get(predicate_name) {
                return Some(definition);
            }
        }

        self.builtin_environment.defined_props.get(predicate_name)
    }

    /// Look up predicate definition without meaning by name from current env or builtin.
    pub fn get_predicate_without_meaning_definition_by_name(&self, predicate_name: &str) -> Option<&DefPropWithoutMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_props_without_meaning.get(predicate_name) {
                return Some(definition);
            }
        }

        self.builtin_environment.defined_props_without_meaning.get(predicate_name)
    }

    pub fn get_set_struct_with_fields_definition_by_name(&self, set_struct_name: &str) -> Option<&DefStructWithFieldsStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs_with_fields.get(set_struct_name) {
                return Some(definition);
            }
        }

        self.builtin_environment.defined_structs_with_fields.get(set_struct_name)
    }

    pub fn get_set_struct_with_no_field_definition_by_name(&self, set_struct_name: &str) -> Option<&DefStructWithNoFieldStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs_with_no_field.get(set_struct_name) {
                return Some(definition);
            }
        }

        self.builtin_environment.defined_structs_with_no_field.get(set_struct_name)
    }

    pub fn is_defined_identifier_obj(&self, identifier: &Identifier) -> bool {
        if is_builtin_identifier_obj(&identifier.name) {
            return true;
        }
        
        self.defined_identifier_objs.contains_key(&identifier.name)
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        self.defined_identifier_objs.contains_key(name) || self.defined_props.contains_key(name) || self.defined_props_without_meaning.contains_key(name) || self.defined_structs_with_fields.contains_key(name) || self.defined_structs_with_no_field.contains_key(name) || self.defined_algorithms.contains_key(name)
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
                for defined_struct_with_fields in last_env.defined_structs_with_fields.iter() {
                    self.defined_structs_with_fields.remove(defined_struct_with_fields.0);
                }
                for defined_struct_with_no_field in last_env.defined_structs_with_no_field.iter() {
                    self.defined_structs_with_no_field.remove(defined_struct_with_no_field.0);
                }
                for defined_algorithm in last_env.defined_algorithms.iter() {
                    self.defined_algorithms.remove(defined_algorithm.0);
                }
                
                self.environments.pop();
            }
        }
    }

    // TODO: PREDICATE WITH MOD NAME IS NOT IMPLEMENTED YET
    pub fn get_all_objs_equal_to_arg(&self, given: &str) -> Vec<String> {
        let mut result = vec![];       
        for env in self.iter_environments_from_top() {
            if let Some(known_equality) = env.known_equality.get(given) {
                for obj in known_equality.iter() {
                    result.push(obj.to_string());
                }
            }
        }

        if let Some(known_equality) = self.builtin_environment.known_equality.get(given) {
            for obj in known_equality.iter() {
                result.push(obj.to_string());
            }
        }
        
        result
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn iter_environments_from_top(&self) -> impl Iterator<Item = &Environment> {
        self.environments.iter().rev().map(|env| env.as_ref())
    }

    pub fn find_fn_definition_for_atom(&self, atom: &Atom) -> Option<&FnSetObj> {
        let key = atom.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_fn_in_fn_set.get(&key) {
                return Some(definition);
            }
        }

        self.builtin_environment.known_fn_in_fn_set.get(&key)
    }

    pub fn cache_well_defined_obj_contains(&self, key: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.cache_well_defined_obj.contains_key(key) {
                return true;
            }
        }
        self.builtin_environment.cache_well_defined_obj.contains_key(key)
    }

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, (usize, usize)) {
        for env in self.iter_environments_from_top() {
            if let Some(line_file) = env.cache_known_fact.get(key) {
                return (true, *line_file);
            }
        }
        if let Some(line_file) = self.builtin_environment.cache_known_fact.get(key) {
            return (true, *line_file);
        }
        (false, DEFAULT_LINE_FILE)
    }
}

impl<'a> RuntimeContext<'a> {
    fn format_line_file(&self, line: usize, file_index: usize) -> String {
        if file_index == 0 {
            format!("line {}", line)
        } else {
            let path = match self.module_manager.run_file_paths.get(file_index) {
                Some(s) => s.as_str(),
                None => "",
            };
            format!("line {}, file {}", line, path)
        }
    }

    fn format_infer_block(infer_result: &InferResult) -> String {
        if infer_result.infer_facts.is_empty() {
            return String::new();
        }
        format!("\n\ninfer:\n{}", infer_result.infer_facts.join("\n"))
    }

    pub fn display_result(&self, result: &NonErrStmtExecResult) -> String {
        match result {
            NonErrStmtExecResult::NonFactualStmtSuccess(x) => {
                let location = if x.line_file_index == DEFAULT_LINE_FILE { "Success:\n".to_string() } else { format!("Success on {}:\n", self.format_line_file(x.line_file_index.0, x.line_file_index.1)) };
                let msg = format!("{}{}", x.stmt, Self::format_infer_block(&x.infers));
                format!("{}{}", location, msg)
            }
            NonErrStmtExecResult::FactVerifiedByFact(x) => {
                let location = if x.line_file_index == DEFAULT_LINE_FILE { "Success:\n".to_string() } else { format!("Success on {}:\n", self.format_line_file(x.line_file_index.0, x.line_file_index.1)) };
                let verified_by_suffix = if x.verified_by_line_file == DEFAULT_LINE_FILE { String::new() } else { format!("{}", self.format_line_file(x.verified_by_line_file.0, x.verified_by_line_file.1)) };
                let msg = format!("{}\nverified by {}\n{}{}", x.fact, verified_by_suffix, x.verified_by , Self::format_infer_block(&x.infers));
                format!("{}{}", location, msg)
            }
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(x) => {
                let location = if x.line_file_index == DEFAULT_LINE_FILE { "Success:\n".to_string() } else { format!("Success on {}:\n", self.format_line_file(x.line_file_index.0, x.line_file_index.1)) };
                let msg = format!("{}\nverified by\n{}{}", x.fact, x.verified_by , Self::format_infer_block(&x.infers));
                format!("{}{}", location, msg)
            }
            NonErrStmtExecResult::StmtUnknown(x) => x.to_string(),
        }
    }

    /// Format error: when line_file is not (0,0), "{Label} on line N" (or "{Label} on line N, file PATH"); otherwise body only.
    pub fn display_error(&self, error: &StmtError) -> String {
        let body = error.error_body();
        let (line, file_index) = error.line_file();
        if (line, file_index) != DEFAULT_LINE_FILE {
            let label = error.display_label();
            let location = if file_index == 0 {
                format!("{} on line {}", label, line)
            } else {
                let path: &str = match self.module_manager.run_file_paths.get(file_index) {
                    Some(s) => s.as_str(),
                    None => "",
                };
                format!("{} on line {}, file {}", label, line, path)
            };
            format!("{}\n{}", location, body)
        } else {
            body
        }
    }
}
