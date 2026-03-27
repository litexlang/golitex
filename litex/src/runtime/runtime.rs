use super::RuntimeContext;
use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::common::is_valid_litex_name::is_valid_litex_name;
use crate::common::keywords::BUILTIN_CODE;
use crate::error::ParseBlockError;
use crate::module_manager::ModuleManager;
use crate::obj::{Add, Div, Mod, Mul, Number, Obj, Pow, Sub};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

pub struct Runtime {
    pub runtime_context: RuntimeContext,
    pub parsing_time_name_scope_stack: Vec<HashMap<String, (usize, usize)>>,
}

impl Runtime {
    pub fn new() -> Self {
        let module_manager = ModuleManager::new_empty_module_manager(BUILTIN_CODE);
        let runtime_context =
            RuntimeContext::new_empty_runtime_context_with_one_env(module_manager);

        Runtime {
            runtime_context,
            parsing_time_name_scope_stack: vec![HashMap::new()],
        }
    }

    pub fn get_known_normalized_calculated_value_for_obj(&self, obj: &Obj) -> Option<Number> {
        if let Some(number) = obj.calculate_arithmetic_value_and_normalize() {
            return Some(number);
        }
        self.runtime_context
            .get_normalized_calculated_value_of_obj(&obj.to_string())
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
        self.runtime_context
            .module_manager
            .run_file_paths
            .push(path.to_string());
        self.runtime_context.module_manager.current_file_index += 1;
        self.push_parsing_time_name_scope();
        self.runtime_context.push_env();
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        self.parsing_time_name_scope_stack
            .iter()
            .any(|scope| scope.contains_key(name))
    }
}
