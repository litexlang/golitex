use crate::ast::stmt::DefAlgoByCasesStmt;
use crate::execute::execute_have_fn_equal_case_by_case_stmt::{
    ExecHaveFnEqualCaseByCaseStmtFailed, ExecHaveFnEqualCaseByCaseStmtSuccessResult,
};

pub enum ExecDefAlgoByCasesStmtResult {
    Success(ExecDefAlgoByCasesStmtSuccessResult),
    Failed(ExecDefAlgoByCasesStmtFailed),
}

pub struct ExecDefAlgoByCasesStmtSuccessResult {
    pub statement: DefAlgoByCasesStmt,
    pub define_fn: ExecHaveFnEqualCaseByCaseStmtSuccessResult,
}

pub enum ExecDefAlgoByCasesStmtFailed {
    AlgoAlreadyDefined,
    DefineFn(ExecHaveFnEqualCaseByCaseStmtFailed),
}

impl ExecDefAlgoByCasesStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl std::fmt::Debug for ExecDefAlgoByCasesStmtFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlgoAlreadyDefined => write!(f, "AlgoAlreadyDefined"),
            Self::DefineFn(_) => write!(f, "DefineFn"),
        }
    }
}
