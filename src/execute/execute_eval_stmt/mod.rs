//! `eval expr` — display evaluation (no proof fact).
//!
//! Pipeline: closed-numeric equal rewrite → recursive evaluate
//! (closed numeric simplify, and Identifier FnObj → stored algo).

mod evaluate_finite_objects;
mod dispatch_algo;
pub(crate) mod aggregate_evaluation_result;
pub(in crate::execute) mod evaluate_aggregate;
mod evaluate_closed_numeric;
pub(in crate::execute) mod evaluate_obj;
mod exec_eval_stmt;
pub(in crate::execute) mod helper;
mod result;

#[cfg(test)]
mod exec_eval_stmt_tests;

pub(in crate::execute) use exec_eval_stmt::exec_eval_stmt;
pub use result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
