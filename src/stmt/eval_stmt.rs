use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line_file: LineFile,
}

impl fmt::Display for EvalStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", EVAL, self.obj_to_eval)
    }
}

impl EvalStmt {
    pub fn new(obj_to_eval: Obj, line_file: LineFile) -> Self {
        EvalStmt {
            obj_to_eval,
            line_file,
        }
    }
}
