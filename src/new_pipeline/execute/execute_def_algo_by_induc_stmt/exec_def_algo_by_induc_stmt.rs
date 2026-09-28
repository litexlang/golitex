//! `algo f(…) R by induc measure from lower:` — define fn and store executable algo.
//!
//! Example:
//!   algo countdown(n N) N by induc n from 0:
//!       case n = 0: 0
//!       case n >= 1: countdown(n - 1)

use crate::new_pipeline::ast::stmt::{DefAlgoByInducStmt, HaveFnByInducStmt};
use crate::new_pipeline::exec_env::StoredDefAlgo;
use crate::new_pipeline::execute::execute_have_fn_by_induc_stmt::ExecHaveFnByInducStmtResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::result::{
    ExecDefAlgoByInducStmtFailed, ExecDefAlgoByInducStmtResult,
    ExecDefAlgoByInducStmtSuccessResult,
};

pub fn exec_def_algo_by_induc_stmt(
    runtime: &mut Runtime,
    stmt: &DefAlgoByInducStmt,
) -> RuntimeResult<ExecDefAlgoByInducStmtResult> {
    if runtime.def_algo_visible_in_stack(&stmt.name).is_some() {
        return Ok(ExecDefAlgoByInducStmtResult::Failed(
            ExecDefAlgoByInducStmtFailed::AlgoAlreadyDefined,
        ));
    }

    let have_stmt = HaveFnByInducStmt {
        name: stmt.name.clone(),
        fn_set_clause: stmt.fn_set_clause.clone(),
        measure: stmt.measure.clone(),
        lower_bound: stmt.lower_bound.clone(),
        cases: stmt.cases.clone(),
        line_file: stmt.line_file.clone(),
    };

    match runtime.exec_have_fn_by_induc_stmt(&have_stmt)? {
        ExecHaveFnByInducStmtResult::Failed(failed) => Ok(ExecDefAlgoByInducStmtResult::Failed(
            ExecDefAlgoByInducStmtFailed::DefineFn(failed),
        )),
        ExecHaveFnByInducStmtResult::Success(define_fn) => {
            runtime
                .top_exec_env_mut()
                .store_def_algo(StoredDefAlgo::ByInduc(stmt.clone()));
            Ok(ExecDefAlgoByInducStmtResult::Success(
                ExecDefAlgoByInducStmtSuccessResult {
                    statement: stmt.clone(),
                    define_fn,
                },
            ))
        }
    }
}
