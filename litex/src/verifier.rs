use crate::runtime_context::RuntimeContext;

pub struct Verifier<'a> {
    pub runtime_context: &'a RuntimeContext<'a>,
}

impl<'a> Verifier<'a> {
    pub fn new(runtime_context: &'a RuntimeContext<'a>) -> Self {
        Verifier { runtime_context }
    }

    pub fn line_file_index_string(&self, line: usize, file_index: usize) -> String {
        format!("line {}, file {}", line, self.runtime_context.module_manager.run_file_paths[file_index])
    }
}

