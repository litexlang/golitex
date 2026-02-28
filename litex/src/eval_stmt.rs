use std::fmt;
use crate::consts::EVAL;
use crate::obj::Obj;

pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line: u32,
    pub file_index: usize,
}

impl fmt::Display for EvalStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", EVAL, self.obj_to_eval)
    }
}

impl EvalStmt {
    pub fn new(obj_to_eval: Obj, line: u32, file_index: usize) -> Self {
        EvalStmt { obj_to_eval, line, file_index }
    }
}