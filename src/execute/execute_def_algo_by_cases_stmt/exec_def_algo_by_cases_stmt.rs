//! `algo f(…) R by cases:` — define fn (same strength as `have fn … by cases`) and store algo.
//!
//! Example:
//!   algo nonzero_flag(x R) R by cases:
//!       case x = 0: 0
//!       case x != 0: 1

use crate::ast::stmt::{DefAlgoByCasesStmt, HaveFnEqualCaseByCaseStmt};
use crate::exec_env::StoredDefAlgo;
use crate::execute::execute_have_fn_equal_case_by_case_stmt::ExecHaveFnEqualCaseByCaseStmtResult;
use crate::runtime::{Runtime, RuntimeResult};

use super::result::{
    ExecDefAlgoByCasesStmtFailed, ExecDefAlgoByCasesStmtResult, ExecDefAlgoByCasesStmtSuccessResult,
};

pub fn exec_def_algo_by_cases_stmt(
    runtime: &mut Runtime,
    stmt: &DefAlgoByCasesStmt,
) -> RuntimeResult<ExecDefAlgoByCasesStmtResult> {
    if runtime.def_algo_visible_in_stack(&stmt.name.name).is_some() {
        return Ok(ExecDefAlgoByCasesStmtResult::Failed(
            ExecDefAlgoByCasesStmtFailed::AlgoAlreadyDefined,
        ));
    }

    let have_stmt = HaveFnEqualCaseByCaseStmt {
        name: stmt.name.clone(),
        fn_set_clause: stmt.fn_set_clause.clone(),
        cases: stmt.cases.clone(),
        equal_tos: stmt.equal_tos.clone(),
        line_file: stmt.line_file.clone(),
    };

    match runtime.exec_have_fn_equal_case_by_case_stmt(&have_stmt)? {
        ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed) => Ok(
            ExecDefAlgoByCasesStmtResult::Failed(ExecDefAlgoByCasesStmtFailed::DefineFn(failed)),
        ),
        ExecHaveFnEqualCaseByCaseStmtResult::Success(define_fn) => {
            runtime
                .top_exec_env_mut()
                .store_def_algo(StoredDefAlgo::ByCases(stmt.clone()));
            Ok(ExecDefAlgoByCasesStmtResult::Success(
                ExecDefAlgoByCasesStmtSuccessResult {
                    statement: stmt.clone(),
                    define_fn,
                },
            ))
        }
    }
}
