use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ReleaseThmStmt {
    pub call: TheoremCall,
    pub line_file: LineFile,
}

impl ReleaseThmStmt {
    pub fn new(name: AtomicName, args: Vec<Obj>, line_file: LineFile) -> Self {
        Self::new_with_call(TheoremCall::parenthesized(name, args), line_file)
    }

    pub fn new_with_call(call: TheoremCall, line_file: LineFile) -> Self {
        Self { call, line_file }
    }

    pub fn name(&self) -> &AtomicName {
        &self.call.name
    }

    pub fn args(&self) -> &[Obj] {
        self.call.args()
    }

    pub fn parenthesized_args_mut(&mut self) -> Option<&mut Vec<Obj>> {
        self.call.parenthesized_args_mut()
    }

    pub fn store_reason() -> &'static str {
        "theorem instantiation"
    }
}

impl fmt::Display for ReleaseThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", RELEASE, THM, self.call)
    }
}
