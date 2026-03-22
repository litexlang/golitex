use super::RuntimeContext;
use crate::common::is_valid_litex_name::is_valid_litex_name;
use crate::error::ParseBlockError;
use std::collections::HashMap;
use std::fmt;

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
