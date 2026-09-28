mod exec_def_algo_by_cases_stmt;
mod result;

#[cfg(test)]
mod exec_def_algo_by_cases_stmt_tests;

pub use exec_def_algo_by_cases_stmt::exec_def_algo_by_cases_stmt;
pub use result::{
    ExecDefAlgoByCasesStmtFailed, ExecDefAlgoByCasesStmtResult,
    ExecDefAlgoByCasesStmtSuccessResult,
};
