use crate::runtime_context::RuntimeContext;
use crate::error::StmtError;
use crate::result::NonErrStmtResult;

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

    pub fn display_result(&self, result: &NonErrStmtResult) -> String {
        (&*self.runtime_context).display_result(result)
    }

    pub fn display_error(&self, error: &StmtError) -> String {
        (&*self.runtime_context).display_error(error)
    }
}
