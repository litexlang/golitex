//! `eval expr` — display evaluation (no proof fact).
//!
//! Pipeline: closed-numeric equal rewrite → recursive evaluate
//! (closed numeric simplify, and Identifier FnObj → stored algo).

mod dispatch_algo;
mod evaluate_closed_numeric;
mod evaluate_obj;
mod exec_eval_stmt;
mod helper;
mod result;

#[cfg(test)]
mod exec_eval_stmt_tests;

pub(in crate::new_pipeline::execute) use exec_eval_stmt::exec_eval_stmt;
pub use result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
