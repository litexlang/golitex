use crate::prelude::*;

#[derive(Debug)]
pub enum DefInterfaceStmtResult {
    DefPropStmt(NonFactualStmtSuccess),
    DefAbstractPropStmt(NonFactualStmtSuccess),
    AliasPropStmt(NonFactualStmtSuccess),
    AliasThmStmt(NonFactualStmtSuccess),
    DefTemplateStmt(NonFactualStmtSuccess),
    DefAlgoStmt(NonFactualStmtSuccess),
    DefThmStmt(NonFactualStmtSuccess),
    DefStrategyStmt(NonFactualStmtSuccess),
    DefStructStmt(NonFactualStmtSuccess),
}

impl DefInterfaceStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefPropStmt(_)) => {
                DefInterfaceStmtResult::DefPropStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefAbstractPropStmt(_)) => {
                DefInterfaceStmtResult::DefAbstractPropStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::AliasPropStmt(_)) => {
                DefInterfaceStmtResult::AliasPropStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::AliasThmStmt(_)) => {
                DefInterfaceStmtResult::AliasThmStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(_)) => {
                DefInterfaceStmtResult::DefTemplateStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefAlgoStmt(_)) => {
                DefInterfaceStmtResult::DefAlgoStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefThmStmt(_)) => {
                DefInterfaceStmtResult::DefThmStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStrategyStmt(_)) => {
                DefInterfaceStmtResult::DefStrategyStmt(success)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(_)) => {
                DefInterfaceStmtResult::DefStructStmt(success)
            }
            _ => panic!("expected def interface stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefPropStmt(success)
            | DefInterfaceStmtResult::DefAbstractPropStmt(success)
            | DefInterfaceStmtResult::AliasPropStmt(success)
            | DefInterfaceStmtResult::AliasThmStmt(success)
            | DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefAlgoStmt(success)
            | DefInterfaceStmtResult::DefThmStmt(success)
            | DefInterfaceStmtResult::DefStrategyStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefPropStmt(success)
            | DefInterfaceStmtResult::DefAbstractPropStmt(success)
            | DefInterfaceStmtResult::AliasPropStmt(success)
            | DefInterfaceStmtResult::AliasThmStmt(success)
            | DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefAlgoStmt(success)
            | DefInterfaceStmtResult::DefThmStmt(success)
            | DefInterfaceStmtResult::DefStrategyStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            DefInterfaceStmtResult::DefPropStmt(success)
            | DefInterfaceStmtResult::DefAbstractPropStmt(success)
            | DefInterfaceStmtResult::AliasPropStmt(success)
            | DefInterfaceStmtResult::AliasThmStmt(success)
            | DefInterfaceStmtResult::DefTemplateStmt(success)
            | DefInterfaceStmtResult::DefAlgoStmt(success)
            | DefInterfaceStmtResult::DefThmStmt(success)
            | DefInterfaceStmtResult::DefStrategyStmt(success)
            | DefInterfaceStmtResult::DefStructStmt(success) => success,
        }
    }
}
