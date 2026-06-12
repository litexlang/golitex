use crate::prelude::*;

#[derive(Debug)]
pub enum DefInterfaceStmtResult {
    DefTemplateStmt(NonFactualStmtSuccess),
    DefStructStmt(NonFactualStmtSuccess),
}

impl DefInterfaceStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(_)) => {
                DefInterfaceStmtResult::DefTemplateStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(_)) => {
                DefInterfaceStmtResult::DefStructStmt(success)
            }
            _ => panic!("expected def interface stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }
}
