use super::RuntimeContext;
use crate::common::is_valid_litex_name::is_valid_litex_name;
use crate::error::ParseBlockError;
use std::collections::HashMap;
use std::fmt;
use std::time::{SystemTime, UNIX_EPOCH};

pub struct Runtime<'a> {
    pub runtime_context: &'a mut RuntimeContext<'a>,
    pub parsing_time_name_scope_stack: Vec<HashMap<String, ()>>,
}

impl<'a> Runtime<'a> {
    pub fn new(runtime_context: &'a mut RuntimeContext<'a>) -> Self {
        Runtime {
            runtime_context,
            parsing_time_name_scope_stack: vec![HashMap::new()],
        }
    }

    pub fn line_file_string(&self, line: usize, file_index: usize) -> String {
        format!(
            "line {}, file {}",
            line, self.runtime_context.module_manager.run_file_paths[file_index]
        )
    }
}

impl<'a> fmt::Display for Runtime<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Executor {{ runtime_context: {} }}",
            self.runtime_context
        )
    }
}

impl<'a> Runtime<'a> {
    pub fn push_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.push(HashMap::new());
    }

    pub fn validate_name(&mut self, name: &str) -> Result<(), ParseBlockError> {
        if let Err(e) = is_valid_litex_name(name) {
            return Err(ParseBlockError::InvalidName(e));
        }

        if self.runtime_context.is_name_used(name) {
            return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
        }

        for names_in_scope in self.parsing_time_name_scope_stack.iter() {
            if names_in_scope.contains_key(name) {
                return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
            }
        }
        Ok(())
    }

    pub fn pop_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.pop();
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
    ) -> Result<(), ParseBlockError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(name)?;
        }
        Ok(())
    }

    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
    ) -> Result<(), ParseBlockError> {
        self.validate_name(name)?;
        if let Some(names_in_top_scope) = self.parsing_time_name_scope_stack.last_mut() {
            names_in_top_scope.insert(name.to_string(), ());
        }
        Ok(())
    }
}

impl<'a> Runtime<'a> {
    pub fn generate_an_unused_name(&self) -> String {
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
            if self.runtime_context.is_name_used(&candidate_name) {
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
}
