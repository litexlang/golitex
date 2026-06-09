use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByThmStmt {
    pub name: AtomicName,
    pub args: Vec<Obj>,
    pub line_file: LineFile,
}

impl ByThmStmt {
    pub fn new(name: AtomicName, args: Vec<Obj>, line_file: LineFile) -> Self {
        ByThmStmt {
            name,
            args,
            line_file,
        }
    }
}

impl fmt::Display for ByThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{}",
            BY,
            THM,
            self.name,
            braced_vec_to_string(&self.args)
        )
    }
}
