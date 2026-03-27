use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::common::keywords::{is_builtin_identifier_obj, is_builtin_predicate, MOD_SIGN};
use crate::environment::Environment;
use crate::obj::FnSetObj;
use crate::obj::Number;
use crate::obj::{Atom, Cart, Tuple};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::DefPropWithMeaningStmt;
use crate::stmt::definition_stmt::DefPropWithoutMeaningStmt;
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};

use crate::common::is_valid_litex_name::is_valid_litex_name;
use crate::common::keywords::BUILTIN_CODE;
use crate::error::ParseBlockError;
use crate::module_manager::ModuleManager;
use crate::obj::{Add, Div, Mod, Mul, Obj, Pow, Sub};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

pub struct Runtime {
    pub module_manager: ModuleManager,
    pub environment_stack: Vec<Box<Environment>>,
    pub parsing_time_name_scope_stack: Vec<HashMap<String, (usize, usize)>>,
}

impl Runtime {
    pub fn new() -> Self {
        let module_manager = ModuleManager::new_empty_module_manager(BUILTIN_CODE);
        let new_environment = Box::new(Environment::new_empty_env());

        Runtime {
            module_manager,
            environment_stack: vec![new_environment],
            parsing_time_name_scope_stack: vec![HashMap::new()],
        }
    }

    pub fn get_known_normalized_calculated_value_for_obj(&self, obj: &Obj) -> Option<Number> {
        if let Some(number) = obj.calculate_arithmetic_value_and_normalize() {
            return Some(number);
        }
        self.get_normalized_calculated_value_of_obj(&obj.to_string())
    }

    pub fn obj_with_runtime_known_numbers_substituted_for_verification(&self, obj: &Obj) -> Obj {
        match obj {
            Obj::Number(number) => Obj::Number(number.clone()),
            Obj::Add(add) => {
                let result = Obj::Add(Add::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&add.left),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&add.right),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Sub(sub) => {
                let result = Obj::Sub(Sub::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&sub.left),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&sub.right),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Mul(mul) => {
                let result = Obj::Mul(Mul::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&mul.left),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&mul.right),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Mod(mod_obj) => {
                let result = Obj::Mod(Mod::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&mod_obj.left),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(
                        &mod_obj.right,
                    ),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Pow(pow) => {
                let result = Obj::Pow(Pow::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&pow.base),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&pow.exponent),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Div(div) => {
                let result = Obj::Div(Div::new(
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&div.left),
                    self.obj_with_runtime_known_numbers_substituted_for_verification(&div.right),
                ));
                let calculated_result = result.calculate_arithmetic_value_and_normalize();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Identifier(_)
            | Obj::IdentifierWithMod(_)
            | Obj::FieldAccess(_)
            | Obj::FieldAccessWithMod(_)
            | Obj::FnObj(_) => {
                if let Some(number) = self.get_known_normalized_calculated_value_for_obj(obj) {
                    Obj::Number(number)
                } else {
                    obj.clone()
                }
            }
            Obj::Count(count) => match &*count.set {
                Obj::ListSet(list_set) => Obj::Number(Number::new(list_set.list.len().to_string())),
                _ => obj.clone(),
            },
            Obj::TupleDim(dim) => match &*dim.arg {
                Obj::Tuple(tuple) => Obj::Number(Number::new(tuple.args.len().to_string())),
                _ => obj.clone(),
            },
            Obj::CartDim(cart_dim) => match &*cart_dim.set {
                Obj::Cart(cart) => Obj::Number(Number::new(cart.args.len().to_string())),
                _ => obj.clone(),
            },
            Obj::Proj(proj) => match &*proj.set {
                Obj::Cart(cart) => {
                    let projection_index_number =
                        self.get_known_normalized_calculated_value_for_obj(&proj.dim);
                    if let Some(projection_index_number) = projection_index_number {
                        let projection_index_parsed_result =
                            projection_index_number.normalized_value.parse::<usize>();
                        if let Ok(projection_index_one_based) = projection_index_parsed_result {
                            if projection_index_one_based >= 1
                                && projection_index_one_based <= cart.args.len()
                            {
                                return (*cart.args[projection_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_cart_obj = self.get_known_cart_obj_of_obj(&proj.set.to_string());
                    if let Some(known_cart_obj) = known_cart_obj {
                        let projection_index_number =
                            self.get_known_normalized_calculated_value_for_obj(&proj.dim);
                        if let Some(projection_index_number) = projection_index_number {
                            let projection_index_parsed_result =
                                projection_index_number.normalized_value.parse::<usize>();
                            if let Ok(projection_index_one_based) = projection_index_parsed_result {
                                if projection_index_one_based >= 1
                                    && projection_index_one_based <= known_cart_obj.args.len()
                                {
                                    return (*known_cart_obj.args[projection_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            Obj::ObjAtIndex(obj_at_index) => match &*obj_at_index.obj {
                Obj::Tuple(tuple) => {
                    let tuple_index_number =
                        self.get_known_normalized_calculated_value_for_obj(&obj_at_index.index);
                    if let Some(tuple_index_number) = tuple_index_number {
                        let tuple_index_parsed_result =
                            tuple_index_number.normalized_value.parse::<usize>();
                        if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                            if tuple_index_one_based >= 1
                                && tuple_index_one_based <= tuple.args.len()
                            {
                                return (*tuple.args[tuple_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_tuple_obj =
                        self.get_known_tuple_obj_of_obj(&obj_at_index.obj.to_string());
                    if let Some(known_tuple_obj) = known_tuple_obj {
                        let tuple_index_number =
                            self.get_known_normalized_calculated_value_for_obj(&obj_at_index.index);
                        if let Some(tuple_index_number) = tuple_index_number {
                            let tuple_index_parsed_result =
                                tuple_index_number.normalized_value.parse::<usize>();
                            if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                                if tuple_index_one_based >= 1
                                    && tuple_index_one_based <= known_tuple_obj.args.len()
                                {
                                    return (*known_tuple_obj.args[tuple_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            _ => obj.clone(),
        }
    }
}

impl Runtime {
    pub fn push_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.push(HashMap::new());
    }

    pub fn validate_name(
        &mut self,
        name: &str,
        current_line_file: (usize, usize),
    ) -> Result<(), ParseBlockError> {
        if let Err(invalid_name_message) = is_valid_litex_name(name) {
            return Err(ParseBlockError::InvalidName(invalid_name_message));
        }

        for names_in_scope in self.parsing_time_name_scope_stack.iter().rev() {
            if let Some(name_already_defined_on_line_file) = names_in_scope.get(name) {
                return Err(ParseBlockError::NameAlreadyUsed {
                    name: name.to_string(),
                    name_already_used_on_line_file: *name_already_defined_on_line_file,
                    line_file: current_line_file,
                });
            }
        }

        if self.is_name_used(name) {
            return Err(ParseBlockError::NameAlreadyUsed {
                name: name.to_string(),
                name_already_used_on_line_file: DEFAULT_LINE_FILE,
                line_file: current_line_file,
            });
        }

        Ok(())
    }

    pub fn pop_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.pop();
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
        line_file: (usize, usize),
    ) -> Result<(), ParseBlockError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(name, line_file)?;
        }
        Ok(())
    }

    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        (line, file): (usize, usize),
    ) -> Result<(), ParseBlockError> {
        self.validate_name(name, (line, file))?;
        if let Some(names_in_top_scope) = self.parsing_time_name_scope_stack.last_mut() {
            names_in_top_scope.insert(name.to_string(), (line, file));
        }
        Ok(())
    }
}

impl Runtime {
    pub fn generate_a_random_unused_name(&self) -> String {
        let available_chars: Vec<char> = "abcdefghijklmnopqrstuvwxyz0123456789".chars().collect();
        let first_char_candidates: Vec<char> = "abcdefghijklmnopqrstuvwxyz".chars().collect();
        let mut try_index: usize = 0;
        loop {
            let current_time_nanos: u128 = match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(current_duration) => current_duration.as_nanos(),
                Err(_) => 0,
            };
            let mixed_seed_value: u128 =
                current_time_nanos ^ ((try_index as u128 + 1) * 0x9e3779b97f4a7c15u128);
            let generated_name_length: usize = 8 + (mixed_seed_value as usize % 17);

            let mut generated_chars: Vec<char> = Vec::new();
            let first_char_index = ((mixed_seed_value >> 1) as usize) % first_char_candidates.len();
            generated_chars.push(first_char_candidates[first_char_index]);

            let mut current_state_value: u128 = mixed_seed_value;
            for character_index in 1..generated_name_length {
                current_state_value = current_state_value
                    .wrapping_mul(6364136223846793005u128)
                    .wrapping_add(1442695040888963407u128 + character_index as u128);
                let available_char_index = (current_state_value as usize) % available_chars.len();
                generated_chars.push(available_chars[available_char_index]);
            }

            let candidate_name: String = generated_chars.into_iter().collect();
            if is_valid_litex_name(&candidate_name).is_err() {
                try_index += 1;
                continue;
            }
            if self.is_name_used(&candidate_name) {
                try_index += 1;
                continue;
            }
            let mut used_in_parsing_time_name_scope = false;
            for names_in_scope in self.parsing_time_name_scope_stack.iter() {
                if names_in_scope.contains_key(&candidate_name) {
                    used_in_parsing_time_name_scope = true;
                    break;
                }
            }
            if used_in_parsing_time_name_scope {
                try_index += 1;
                continue;
            }
            return candidate_name;
        }
    }

    pub fn new_file_path_new_env_new_name_scope(&mut self, path: &str) {
        self.module_manager.run_file_paths.push(path.to_string());
        self.module_manager.current_file_index += 1;
        self.push_parsing_time_name_scope();
        self.push_env();
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        self.parsing_time_name_scope_stack
            .iter()
            .any(|scope| scope.contains_key(name))
    }
}

impl Runtime {
    pub fn top_level_env(&mut self) -> &mut Environment {
        let result = self.environment_stack.last_mut();
        match result {
            Some(environment) => environment,
            None => unreachable!("no top level environment"),
        }
    }

    pub fn get_predicate_with_meaning_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropWithMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_props_with_meaning.get(predicate_name) {
                return Some(definition);
            }
        }

        None
    }

    /// Look up predicate definition without meaning by name from current env or builtin.
    pub fn get_predicate_without_meaning_definition_by_name(
        &self,
        predicate_name: &str,
    ) -> Option<&DefPropWithoutMeaningStmt> {
        let parts = predicate_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_props_without_meaning
                .get(predicate_name)
            {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_set_struct_with_fields_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<DefStructWithFieldsStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs_with_fields.get(set_struct_name) {
                return Some(definition.clone());
            }
        }

        None
    }

    pub fn get_set_struct_with_fields_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<&DefStructWithFieldsStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_structs_with_fields.get(set_struct_name) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_algo_definition_by_name(&self, algo_name: &str) -> Option<&DefAlgoStmt> {
        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment.defined_algorithms.get(algo_name) {
                return Some(definition);
            }
        }
        None
    }

    pub fn get_set_struct_with_no_field_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<&DefStructWithNoFieldStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_structs_with_no_field
                .get(set_struct_name)
            {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_set_struct_with_no_field_definition_by_name(
        &self,
        set_struct_name: &str,
    ) -> Option<DefStructWithNoFieldStmt> {
        let parts = set_struct_name.split(MOD_SIGN).collect::<Vec<&str>>();
        if parts.len() != 1 {
            unimplemented!();
        }

        for environment in self.iter_environments_from_top() {
            if let Some(definition) = environment
                .defined_structs_with_no_field
                .get(set_struct_name)
            {
                return Some(definition.clone());
            }
        }

        None
    }
}

impl Runtime {
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

        result
    }
}

impl Runtime {
    pub fn iter_environments_from_top(&self) -> impl Iterator<Item = &Environment> {
        self.environment_stack.iter().rev().map(|env| env.as_ref())
    }

    pub fn get_fn_set_where_fn_belongs_to(&self, atom: &Atom) -> Option<&FnSetObj> {
        let key = atom.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_fn_in_fn_set.get(&key) {
                return Some(definition);
            }
        }

        None
    }

    pub fn cache_well_defined_obj_contains(&self, key: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.cache_well_defined_obj.contains_key(key) {
                return true;
            }
        }
        false
    }

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, (usize, usize)) {
        for env in self.iter_environments_from_top() {
            if let Some(line_file) = env.cache_known_fact.get(key) {
                return (true, *line_file);
            }
        }
        (false, DEFAULT_LINE_FILE)
    }
}

impl Runtime {
    pub fn get_known_cart_obj_of_obj(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some((known_cart_obj, _)) = env.known_cart_objs.get(name) {
                return Some(known_cart_obj.clone());
            }
            if let Some((_, Some(known_cart_obj), _)) = env.known_tuple_objs.get(name) {
                return Some(known_cart_obj.clone());
            }
        }
        None
    }

    pub fn get_known_tuple_obj_of_obj(&self, name: &str) -> Option<Tuple> {
        for env in self.iter_environments_from_top() {
            if let Some((Some(known_tuple_obj), _, _)) = env.known_tuple_objs.get(name) {
                return Some(known_tuple_obj.clone());
            }
        }
        None
    }

    pub fn get_tuple_obj_is_in_what_cart(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some(cart) = env.known_tuple_objs.get(name) {
                return cart.1.clone();
            }
        }
        None
    }

    pub fn get_normalized_calculated_value_of_obj(&self, obj_str: &str) -> Option<Number> {
        for env in self.iter_environments_from_top() {
            if let Some(calculated_value) =
                env.known_normalized_calculated_value_of_obj.get(obj_str)
            {
                return Some(calculated_value.clone());
            }
        }
        None
    }
}

impl Runtime {
    pub fn is_name_used_for_identifier_and_field_access(&self, name: &str) -> bool {
        if is_builtin_identifier_obj(name) {
            return true;
        }

        for env in self.iter_environments_from_top() {
            if env.defined_identifier_and_field_access.contains_key(name) {
                return true;
            }
        }

        false
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

impl Runtime {
    pub fn new_file_and_update_runtime_with_file_content(&mut self, path: &str) {
        self.module_manager.run_file_paths.push(path.to_string());
        self.module_manager.current_file_index = self.module_manager.run_file_paths.len() - 1;
    }

    pub fn change_file_index_to(&mut self, file_index: usize) {
        self.module_manager.current_file_index = file_index;
    }
}

impl Runtime {
    pub fn store_tuple_obj_and_cart(
        &mut self,
        name: &str,
        tuple: Option<Tuple>,
        cart: Option<Cart>,
        line_file: (usize, usize),
    ) {
        let known_tuple_objs = &mut self.top_level_env().known_tuple_objs;
        let old_tuple_and_cart = known_tuple_objs.get(name).cloned();

        let merged_tuple = match (tuple, old_tuple_and_cart.as_ref()) {
            (Some(new_tuple), _) => Some(new_tuple),
            (None, Some((old_tuple, _, _))) => old_tuple.clone(),
            (None, None) => None,
        };
        let merged_cart = match (cart, old_tuple_and_cart.as_ref()) {
            (Some(new_cart), _) => Some(new_cart),
            (None, Some((_, old_cart, _))) => old_cart.clone(),
            (None, None) => None,
        };
        let merged_line_file = line_file;

        known_tuple_objs.insert(
            name.to_string(),
            (merged_tuple, merged_cart, merged_line_file),
        );
    }

    pub fn store_known_cart_obj(&mut self, name: &str, cart: Cart, line_file: (usize, usize)) {
        self.top_level_env()
            .known_cart_objs
            .insert(name.to_string(), (cart, line_file));
    }
}
