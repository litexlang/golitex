use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct EvalByStmt {
    pub lhs: Obj,
    pub rhs: Obj,
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

    pub fn store_reason() -> &'static str {
        "evaluation result"
    }
}

impl EvalByStmt {
    pub fn new(lhs: Obj, rhs: Obj, line_file: LineFile) -> Self {
        EvalByStmt {
            lhs,
            rhs,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        EvalStmt::store_reason()
    }
}

impl fmt::Display for EvalByStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", EVAL, self.lhs, FROM, self.rhs)
    }
}
