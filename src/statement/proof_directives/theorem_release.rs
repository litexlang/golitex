use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ReleaseThmStmt {
    pub name: AtomicName,
    pub args: Vec<Obj>,
    pub line_file: LineFile,
}

impl ReleaseThmStmt {
    pub fn new(name: AtomicName, args: Vec<Obj>, line_file: LineFile) -> Self {
        Self {
            name,
            args,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "theorem instantiation"
    }
}

impl fmt::Display for ReleaseThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {}{}",
            RELEASE,
            THM,
            self.name,
            braced_vec_to_string(&self.args)
        )
    }
}
