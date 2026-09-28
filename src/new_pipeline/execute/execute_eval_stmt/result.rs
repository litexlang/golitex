//! Result types for `eval expr`.

use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::EvalStmt;

pub enum ExecCommandStmtResult {
    Eval(ExecEvalStmtResult),
}

pub enum ExecEvalStmtResult {
    Success(ExecEvalStmtSuccess),
    Failed(ExecEvalStmtFailed),
}

// Success fields follow exec_eval_stmt stage order: statement → value.
pub struct ExecEvalStmtSuccess {
    pub statement: EvalStmt,
    pub source_object: Obj,
    pub evaluated_object: Obj,
}

pub enum ExecEvalStmtFailed {
    UnsupportedExpression,
}

impl ExecCommandStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Eval(r) => r.is_failed(),
        }
    }
}

impl ExecEvalStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
