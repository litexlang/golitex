use crate::ast::stmt::DefAlgoByInducStmt;
use crate::execute::execute_have_fn_by_induc_stmt::{
    ExecHaveFnByInducStmtFailed, ExecHaveFnByInducStmtSuccessResult,
};

pub enum ExecDefAlgoByInducStmtResult {
    Success(ExecDefAlgoByInducStmtSuccessResult),
    Failed(ExecDefAlgoByInducStmtFailed),
}

pub struct ExecDefAlgoByInducStmtSuccessResult {
    pub statement: DefAlgoByInducStmt,
    pub define_fn: ExecHaveFnByInducStmtSuccessResult,
}

pub enum ExecDefAlgoByInducStmtFailed {
    AlgoAlreadyDefined,
    DefineFn(ExecHaveFnByInducStmtFailed),
}

impl ExecDefAlgoByInducStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl std::fmt::Debug for ExecDefAlgoByInducStmtFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlgoAlreadyDefined => write!(f, "AlgoAlreadyDefined"),
            Self::DefineFn(_) => write!(f, "DefineFn"),
        }
    }
}
