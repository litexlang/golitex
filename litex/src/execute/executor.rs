use std::fmt;
use std::collections::HashMap;
use crate::runtime_context::RuntimeContext;
use crate::error::ParseBlockError;

pub struct Executor<'a> {
    pub runtime_context: &'a mut RuntimeContext<'a>,
    pub name_blocks: Vec<HashMap<String, ()>>,
}

impl<'a> Executor<'a> {
    pub fn new(runtime_context: &'a mut RuntimeContext<'a>) -> Self {
        Executor { runtime_context , name_blocks: vec![HashMap::new()] }
    }

    pub fn line_file_index_string(&self, line: usize, file_index: usize) -> String {
        format!("line {}, file {}", line, self.runtime_context.module_manager.run_file_paths[file_index])
    }
}

impl<'a> fmt::Display for Executor<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Executor {{ runtime_context: {} }}", self.runtime_context)
    }
}

impl<'a> Executor<'a> {
    pub fn new_name_block(&mut self) {
        self.name_blocks.push(HashMap::new());
    }

    pub fn return_error_when_name_is_used(&mut self, name: &str) -> Result<(), ParseBlockError> {
        if self.runtime_context.is_name_used(name) {
            return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
        }
        
        for name_block in self.name_blocks.iter() {
            if name_block.contains_key(name) {
                return Err(ParseBlockError::NameAlreadyUsed(name.to_string()));
            }
        }
        Ok(())
    }

    pub fn delete_name_block(&mut self) {
        self.name_blocks.pop();
    }

    pub fn new_names(&mut self, names: &Vec<String>) -> Result<(), ParseBlockError> {
        for name in names {
            self.return_error_when_name_is_used(name)?;
            if let Some(name_block) = self.name_blocks.last_mut() {
                name_block.insert(name.to_string(), ());
            }
        }
        Ok(())
    }
}