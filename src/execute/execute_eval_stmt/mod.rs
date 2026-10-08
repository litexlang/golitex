//! `eval expr` — exact evaluation followed by checked equality publication.
//!
//! Pipeline: closed-numeric equal rewrite → recursive evaluate
//! (closed numeric simplify, and Identifier FnObj → stored algo).

pub(crate) mod aggregate_evaluation_result;
mod dispatch_algo;
pub(in crate::execute) mod evaluate_aggregate;
mod evaluate_closed_numeric;
mod evaluate_finite_objects;
pub(in crate::execute) mod evaluate_obj;
mod exec_eval_stmt;
pub(in crate::execute) mod helper;
mod result;
mod verify_evaluated_algo_calls;

#[cfg(test)]
mod exec_eval_stmt_tests;

pub(in crate::execute) use exec_eval_stmt::exec_eval_stmt;
pub use result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
