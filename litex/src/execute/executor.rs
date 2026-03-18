use std::fmt;
use std::collections::HashMap;
use crate::runtime_context::RuntimeContext;
use crate::error::ParseBlockError;
use crate::common::is_valid_litex_name::is_valid_litex_name;

pub struct Executor<'a> {
    pub runtime_context: &'a mut RuntimeContext<'a>,
    pub parsing_names_blocks: Vec<HashMap<String, ()>>,
}

impl<'a> Executor<'a> {
    pub fn new(runtime_context: &'a mut RuntimeContext<'a>) -> Self {
        Executor { runtime_context , parsing_names_blocks: vec![HashMap::new()] }
    }

    pub fn line_file_string(&self, line: usize, file_index: usize) -> String {
        format!("line {}, file {}", line, self.runtime_context.module_manager.run_file_paths[file_index])
    }
}

impl<'a> fmt::Display for Executor<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Executor {{ runtime_context: {} }}", self.runtime_context)
    }
}

impl<'a> Executor<'a> {
    pub fn new_parsing_names_block(&mut self) {
        self.parsing_names_blocks.push(HashMap::new());
    }

    pub fn validate_name(&mut self, name: &str) -> Result<(), ParseBlockError> {
        if let Err(e) = is_valid_litex_name(name) {
            return Err(ParseBlockError::InvalidName(e));
        }
        
        if self.runtime_context.is_name_used(name) {
            return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
        }
        
        for name_block in self.parsing_names_blocks.iter() {
            if name_block.contains_key(name) {
                return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
            }
        }
        Ok(())
    }

    pub fn delete_parsing_names_block(&mut self) {
        self.parsing_names_blocks.pop();
    }

    pub fn validate_names_and_put_into_parsing_names_block(&mut self, names: &Vec<String>) -> Result<(), ParseBlockError> {
        for name in names {
            self.validate_name_and_put_into_parsing_names_block(name)?;
        }
        Ok(())
    }

    pub fn validate_name_and_put_into_parsing_names_block(&mut self, name: &str) -> Result<(), ParseBlockError> {
        self.validate_name(name)?;
        if let Some(name_block) = self.parsing_names_blocks.last_mut() {
            name_block.insert(name.to_string(), ());
        }
        Ok(())
    }
}