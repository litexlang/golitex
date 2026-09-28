//! `eval expr` — evaluate a supported object for display (no proof fact).

mod exec_eval_stmt;
mod helper;
mod result;

pub(in crate::new_pipeline::execute) use exec_eval_stmt::exec_eval_stmt;
pub use result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
