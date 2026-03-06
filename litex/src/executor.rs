use crate::runtime_context::RuntimeContext;
use std::fmt;

pub struct Executor<'a> {
    pub runtime_context: &'a mut RuntimeContext<'a>,
}

impl<'a> Executor<'a> {
    pub fn new(runtime_context: &'a mut RuntimeContext<'a>) -> Self {
        Executor { runtime_context }
    }

    pub fn line_file_index_string(&self, line: usize, file_index: usize) -> String {
        format!("line {}, file {}", line, self.runtime_context.module_manager.run_file_paths[file_index])
    }
}

impl<'a> fmt::Display for Executor<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Executor {{\n")?;
        write!(f, "    runtime_context: {}\n", self.runtime_context)?;
        write!(f, "}}")
    }
}