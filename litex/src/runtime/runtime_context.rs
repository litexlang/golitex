use crate::common::defaults::DEFAULT_FIRST_FILE_INDEX_FOR_USER;
use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::common::keywords::{is_builtin_identifier_obj, is_builtin_predicate, MOD_SIGN};
use crate::environment::Environment;
use crate::error::RuntimeError;
use crate::infer::InferResult;
use crate::module_manager::ModuleManager;
use crate::obj::FnSetObj;
use crate::obj::Number;
use crate::obj::{Atom, Cart};
use crate::result::{
    FactVerifiedByBuiltinRules, FactVerifiedByFact, NonErrStmtExecResult, NonFactualStmtSuccess,
};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::DefPropWithMeaningStmt;
use crate::stmt::definition_stmt::DefPropWithoutMeaningStmt;
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use std::fmt;

pub struct RuntimeContext<'a> {
    pub module_manager: &'a mut ModuleManager<'a>,
    pub environment_stack: Vec<Box<Environment>>,
    pub builtin_environment: &'a mut Environment,
}

impl<'a> RuntimeContext<'a> {
    pub fn new_empty_runtime_context_with_one_env(
        module_manager: &'a mut ModuleManager<'a>,
        builtin_environment: &'a mut Environment,
    ) -> Self {
        let new_env = Box::new(Environment::new_empty_env());
        RuntimeContext {
            module_manager,
            environment_stack: vec![new_env],
            builtin_environment,
        }
    }
}

impl<'a> fmt::Display for RuntimeContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RuntimeContext {{\n")?;
        write!(f, "    module_manager: {}\n", self.module_manager)?;
        write!(f, "    environments: {:?}\n", self.environment_stack.len())?;
        write!(f, "    builtin_environment: {}\n", self.builtin_environment)?;
        write!(f, "}}")
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn top_level_env(&mut self) -> &mut Environment {
        let result = self.environment_stack.last_mut();
        match result {
            Some(e) => e,
            None => unreachable!("no top level environment"),
        }
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn get_predicate_with_meaning_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropWithMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_props_with_meaning.get(predicate_name) {
                return Some(definition);
            }
        }

        self.builtin_environment
            .defined_props_with_meaning
            .get(predicate_name)
    }

    /// Look up predicate definition without meaning by name from current env or builtin.
    pub fn get_predicate_without_meaning_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropWithoutMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_props_without_meaning
                .get(predicate_name)
            {
                return Some(definition);
            }
        }

        self.builtin_environment
            .defined_props_without_meaning
            .get(predicate_name)
    }

    pub fn get_set_struct_with_fields_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<&DefStructWithFieldsStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs_with_fields.get(set_struct_name) {
                return Some(definition);
            }
        }

        self.builtin_environment
            .defined_structs_with_fields
            .get(set_struct_name)
    }

    pub fn get_algo_definition_by_name(&self, algo_name: &str) -> Option<&DefAlgoStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_algorithms.get(algo_name) {
                return Some(definition);
            }
        }
        self.builtin_environment.defined_algorithms.get(algo_name)
    }

    pub fn get_set_struct_with_no_field_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<&DefStructWithNoFieldStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            panic!("NOT IMPLEMENTED YET");
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_structs_with_no_field
                .get(set_struct_name)
            {
                return Some(definition);
            }
        }

        self.builtin_environment
            .defined_structs_with_no_field
            .get(set_struct_name)
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        if self.is_name_used_for_identifier(name) {
            return true;
        }

        if self.is_name_used_for_predicate_with_meaning(name) {
            return true;
        }

        if self.is_name_used_for_predicate_without_meaning(name) {
            return true;
        }

        if self.is_name_used_for_struct_with_fields(name) {
            return true;
        }

        if self.is_name_used_for_struct_with_no_field(name) {
            return true;
        }

        return self.is_name_used_for_algo(name);
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn push_env(&mut self) {
        let new_env = Box::new(Environment::new_empty_env());
        self.environment_stack.push(new_env);
    }

    pub fn pop_env(&mut self) {
        let last_env = self.environment_stack.last();

        match last_env {
            None => {
                unreachable!("no top level environment")
            }
            Some(_) => {
                self.environment_stack.pop();
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
        self.environment_stack.iter().rev().map(|env| env.as_ref())
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
        self.builtin_environment
            .cache_well_defined_obj
            .contains_key(key)
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
    pub(in crate::runtime) fn format_line_file_location_string(
        &self,
        line: usize,
        file_index: usize,
    ) -> String {
        if file_index == DEFAULT_FIRST_FILE_INDEX_FOR_USER {
            format!("on line {}", line)
        } else {
            let path = match self.module_manager.run_file_paths.get(file_index) {
                Some(s) => s.as_str(),
                None => "",
            };
            format!("on line {}, file {}", line, path)
        }
    }

    pub(in crate::runtime) fn format_infer_block(infer_result: &InferResult) -> String {
        if infer_result.infer_facts.is_empty() {
            return String::new();
        }
        format!("\n\ninfer:\n{}", infer_result.infer_facts.join("\n"))
    }

    pub(in crate::runtime) fn format_inside_results_block(
        &self,
        inside_results: &Vec<NonErrStmtExecResult>,
    ) -> String {
        if inside_results.is_empty() {
            return String::new();
        }
        let mut display_lines: Vec<String> = Vec::new();
        for inside_result in inside_results.iter() {
            display_lines.push(self.display_result(inside_result));
        }
        format!("\n\ninside results:\n{}", display_lines.join("\n"))
    }

    fn success_prefix_by_line_file(&self, line_file: (usize, usize)) -> String {
        if line_file == DEFAULT_LINE_FILE {
            "Success:\n".to_string()
        } else {
            format!(
                "Success on {}:\n",
                self.format_line_file_location_string(line_file.0, line_file.1)
            )
        }
    }

    fn display_non_factual_stmt_success(
        &self,
        non_factual_stmt_success_result: &NonFactualStmtSuccess,
    ) -> String {
        let success_prefix =
            self.success_prefix_by_line_file(non_factual_stmt_success_result.stmt.line_file());
        let message_body = format!(
            "{}{}{}",
            non_factual_stmt_success_result.stmt,
            Self::format_infer_block(&non_factual_stmt_success_result.infers),
            self.format_inside_results_block(&non_factual_stmt_success_result.inside_results)
        );
        format!("{}{}", success_prefix, message_body)
    }

    fn display_fact_verified_by_fact(
        &self,
        fact_verified_by_fact_result: &FactVerifiedByFact,
    ) -> String {
        let success_prefix =
            self.success_prefix_by_line_file(fact_verified_by_fact_result.fact.line_file());
        let verified_by_suffix =
            if fact_verified_by_fact_result.verified_by_line_file == DEFAULT_LINE_FILE {
                String::new()
            } else {
                format!(
                    "fact known/verified/inferred {}",
                    self.format_line_file_location_string(
                        fact_verified_by_fact_result.verified_by_line_file.0,
                        fact_verified_by_fact_result.verified_by_line_file.1
                    )
                )
            };
        let message_body = format!(
            "{}\nverified by {}\n{}{}",
            fact_verified_by_fact_result.fact,
            verified_by_suffix,
            fact_verified_by_fact_result.verified_by,
            Self::format_infer_block(&fact_verified_by_fact_result.infers)
        );
        format!("{}{}", success_prefix, message_body)
    }

    fn display_fact_verified_by_builtin_rules(
        &self,
        fact_verified_by_builtin_rules_result: &FactVerifiedByBuiltinRules,
    ) -> String {
        let success_prefix = self
            .success_prefix_by_line_file(fact_verified_by_builtin_rules_result.fact.line_file());
        let message_body = format!(
            "{}\nverified by\n{}{}",
            fact_verified_by_builtin_rules_result.fact,
            fact_verified_by_builtin_rules_result.verified_by,
            Self::format_infer_block(&fact_verified_by_builtin_rules_result.infers)
        );
        format!("{}{}", success_prefix, message_body)
    }

    pub fn display_result_non_json(&self, result: &NonErrStmtExecResult) -> String {
        match result {
            NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_stmt_success_result) => {
                self.display_non_factual_stmt_success(non_factual_stmt_success_result)
            }
            NonErrStmtExecResult::FactVerifiedByFact(fact_verified_by_fact_result) => {
                self.display_fact_verified_by_fact(fact_verified_by_fact_result)
            }
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                fact_verified_by_builtin_rules_result,
            ) => self.display_fact_verified_by_builtin_rules(fact_verified_by_builtin_rules_result),
            NonErrStmtExecResult::StmtUnknown(stmt_unknown_result) => {
                stmt_unknown_result.to_string()
            }
        }
    }

    pub fn display_result(&self, result: &NonErrStmtExecResult) -> String {
        self.display_result_non_json(result)
    }

    pub fn display_error(&self, error: &RuntimeError) -> String {
        let location_string =
            self.format_line_file_location_string(error.line_file().0, error.line_file().1);

        match error {
            RuntimeError::ArithmeticError(_) => {
                format!("ArithmeticError: {}", location_string)
            }
            RuntimeError::NewAtomicFactError(_) => {
                format!("NewAtomicFactError: {}", location_string)
            }
            RuntimeError::StoreFactError(_) => {
                format!("StoreFactError: {}", location_string)
            }
            RuntimeError::ParseBlockError(_) => {
                format!("ParseBlockError: {}", location_string)
            }
            RuntimeError::ParsingError(_) => {
                format!("ParsingError: {}", location_string)
            }
            RuntimeError::ExecStmtError(_) => {
                format!("ExecStmtError: {}", location_string)
            }
            RuntimeError::UnknownError(_) => {
                format!("UnknownError: {}", location_string)
            }
            RuntimeError::WellDefinedError(_) => {
                format!("WellDefinedError: {}", location_string)
            }
            RuntimeError::VerifyError(_) => {
                format!("VerifyError: {}", location_string)
            }
            RuntimeError::VerifyUnknownError(_) => {
                format!("VerifyUnknownError: {}", location_string)
            }
            RuntimeError::InferError(_) => {
                format!("InferError: {}", location_string)
            }
            RuntimeError::NameAlreadyUsedError(_) => {
                format!("NameAlreadyUsedError: {}", location_string)
            }
        }
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn get_tuple_obj_is_in_what_cart(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some(cart) = env.known_tuple_obj_in_what_cart.get(name) {
                return Some(cart.clone());
            }
        }
        self.builtin_environment
            .known_tuple_obj_in_what_cart
            .get(name)
            .cloned()
    }

    pub fn get_normalized_calculated_value_of_obj(&self, obj_str: &str) -> Option<Number> {
        for env in self.iter_environments_from_top() {
            if let Some(calculated_value) =
                env.known_normalized_calculated_value_of_obj.get(obj_str)
            {
                return Some(calculated_value.clone());
            }
        }
        self.builtin_environment
            .known_normalized_calculated_value_of_obj
            .get(obj_str)
            .cloned()
    }
}

impl<'a> RuntimeContext<'a> {
    pub fn is_name_used_for_identifier(&self, name: &str) -> bool {
        if is_builtin_identifier_obj(name) {
            return true;
        }

        for env in self.iter_environments_from_top() {
            if env.defined_identifier_objs.contains_key(name) {
                return true;
            }
        }

        self.builtin_environment
            .defined_identifier_objs
            .contains_key(name)
    }

    pub fn is_name_used_for_predicate_with_meaning(&self, name: &str) -> bool {
        return self
            .get_predicate_with_meaning_definition_by_name(name)
            .is_some();
    }

    pub fn is_name_used_for_predicate_without_meaning(&self, name: &str) -> bool {
        if is_builtin_predicate(name) {
            return true;
        }

        return self
            .get_predicate_without_meaning_definition_by_name(name)
            .is_some();
    }

    pub fn is_name_used_for_struct_with_fields(&self, name: &str) -> bool {
        return self
            .get_set_struct_with_fields_definition_by_name(name)
            .is_some();
    }

    pub fn is_name_used_for_struct_with_no_field(&self, name: &str) -> bool {
        return self
            .get_set_struct_with_no_field_definition_by_name(name)
            .is_some();
    }

    pub fn is_name_used_for_algo(&self, name: &str) -> bool {
        return self.get_algo_definition_by_name(name).is_some();
    }
}
