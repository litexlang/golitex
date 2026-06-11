use crate::prelude::*;

#[derive(Debug)]
pub enum DefPredicateStmtResult {
    DefPropStmt(NonFactualStmtSuccess),
    DefAbstractPropStmt(NonFactualStmtSuccess),
}

impl DefPredicateStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => {
                DefPredicateStmtResult::DefPropStmt(success)
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(_)) => {
                DefPredicateStmtResult::DefAbstractPropStmt(success)
            }
            _ => panic!("expected def predicate stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            DefPredicateStmtResult::DefPropStmt(success)
            | DefPredicateStmtResult::DefAbstractPropStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            DefPredicateStmtResult::DefPropStmt(success)
            | DefPredicateStmtResult::DefAbstractPropStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            DefPredicateStmtResult::DefPropStmt(success)
            | DefPredicateStmtResult::DefAbstractPropStmt(success) => success,
        }
    }
}
