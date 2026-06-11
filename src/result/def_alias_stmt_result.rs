use crate::prelude::*;

#[derive(Debug)]
pub enum DefAliasStmtResult {
    AliasPropStmt(NonFactualStmtSuccess),
    AliasThmStmt(NonFactualStmtSuccess),
}

impl DefAliasStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::DefAliasStmt(DefAliasStmt::AliasPropStmt(_)) => {
                DefAliasStmtResult::AliasPropStmt(success)
            }
            Stmt::DefAliasStmt(DefAliasStmt::AliasThmStmt(_)) => {
                DefAliasStmtResult::AliasThmStmt(success)
            }
            _ => panic!("expected def alias stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            DefAliasStmtResult::AliasPropStmt(success)
            | DefAliasStmtResult::AliasThmStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            DefAliasStmtResult::AliasPropStmt(success)
            | DefAliasStmtResult::AliasThmStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            DefAliasStmtResult::AliasPropStmt(success)
            | DefAliasStmtResult::AliasThmStmt(success) => success,
        }
    }
}
