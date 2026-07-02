use crate::prelude::*;

#[derive(Debug)]
pub enum DefObjStmtResult {
    HaveObjInNonemptySetStmt(NonFactualStmtSuccess),
    HaveObjEqualStmt(NonFactualStmtSuccess),
    HaveObjByExistFactsStmt(NonFactualStmtSuccess),
    HaveByExistStmt(NonFactualStmtSuccess),
    HaveByPreimageStmt(NonFactualStmtSuccess),
    HaveFnEqualStmt(NonFactualStmtSuccess),
    HaveFnEqualCaseByCaseStmt(NonFactualStmtSuccess),
    HaveFnByInducStmt(NonFactualStmtSuccess),
    HaveFnByForallExistUniqueStmt(NonFactualStmtSuccess),
    HaveTupleStmt(NonFactualStmtSuccess),
    HaveCartStmt(NonFactualStmtSuccess),
    HaveSeqStmt(NonFactualStmtSuccess),
    HaveFiniteSeqStmt(NonFactualStmtSuccess),
    HaveMatrixStmt(NonFactualStmtSuccess),
}

impl DefObjStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(_)) => {
                DefObjStmtResult::HaveObjInNonemptySetStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(_)) => {
                DefObjStmtResult::HaveObjEqualStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(_)) => {
                DefObjStmtResult::HaveObjByExistFactsStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(_)) => {
                DefObjStmtResult::HaveByExistStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByPreimageStmt(_)) => {
                DefObjStmtResult::HaveByPreimageStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(_)) => {
                DefObjStmtResult::HaveFnEqualStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(_)) => {
                DefObjStmtResult::HaveFnEqualCaseByCaseStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(_)) => {
                DefObjStmtResult::HaveFnByInducStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(_)) => {
                DefObjStmtResult::HaveFnByForallExistUniqueStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveTupleStmt(_)) => {
                DefObjStmtResult::HaveTupleStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveCartStmt(_)) => {
                DefObjStmtResult::HaveCartStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveSeqStmt(_)) => DefObjStmtResult::HaveSeqStmt(success),
            Stmt::DefObjStmt(DefObjStmt::HaveFiniteSeqStmt(_)) => {
                DefObjStmtResult::HaveFiniteSeqStmt(success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveMatrixStmt(_)) => {
                DefObjStmtResult::HaveMatrixStmt(success)
            }
            _ => panic!("expected def obj stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            DefObjStmtResult::HaveObjInNonemptySetStmt(success)
            | DefObjStmtResult::HaveObjEqualStmt(success)
            | DefObjStmtResult::HaveObjByExistFactsStmt(success)
            | DefObjStmtResult::HaveByExistStmt(success)
            | DefObjStmtResult::HaveByPreimageStmt(success)
            | DefObjStmtResult::HaveFnEqualStmt(success)
            | DefObjStmtResult::HaveFnEqualCaseByCaseStmt(success)
            | DefObjStmtResult::HaveFnByInducStmt(success)
            | DefObjStmtResult::HaveFnByForallExistUniqueStmt(success)
            | DefObjStmtResult::HaveTupleStmt(success)
            | DefObjStmtResult::HaveCartStmt(success)
            | DefObjStmtResult::HaveSeqStmt(success)
            | DefObjStmtResult::HaveFiniteSeqStmt(success)
            | DefObjStmtResult::HaveMatrixStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            DefObjStmtResult::HaveObjInNonemptySetStmt(success)
            | DefObjStmtResult::HaveObjEqualStmt(success)
            | DefObjStmtResult::HaveObjByExistFactsStmt(success)
            | DefObjStmtResult::HaveByExistStmt(success)
            | DefObjStmtResult::HaveByPreimageStmt(success)
            | DefObjStmtResult::HaveFnEqualStmt(success)
            | DefObjStmtResult::HaveFnEqualCaseByCaseStmt(success)
            | DefObjStmtResult::HaveFnByInducStmt(success)
            | DefObjStmtResult::HaveFnByForallExistUniqueStmt(success)
            | DefObjStmtResult::HaveTupleStmt(success)
            | DefObjStmtResult::HaveCartStmt(success)
            | DefObjStmtResult::HaveSeqStmt(success)
            | DefObjStmtResult::HaveFiniteSeqStmt(success)
            | DefObjStmtResult::HaveMatrixStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            DefObjStmtResult::HaveObjInNonemptySetStmt(success)
            | DefObjStmtResult::HaveObjEqualStmt(success)
            | DefObjStmtResult::HaveObjByExistFactsStmt(success)
            | DefObjStmtResult::HaveByExistStmt(success)
            | DefObjStmtResult::HaveByPreimageStmt(success)
            | DefObjStmtResult::HaveFnEqualStmt(success)
            | DefObjStmtResult::HaveFnEqualCaseByCaseStmt(success)
            | DefObjStmtResult::HaveFnByInducStmt(success)
            | DefObjStmtResult::HaveFnByForallExistUniqueStmt(success)
            | DefObjStmtResult::HaveTupleStmt(success)
            | DefObjStmtResult::HaveCartStmt(success)
            | DefObjStmtResult::HaveSeqStmt(success)
            | DefObjStmtResult::HaveFiniteSeqStmt(success)
            | DefObjStmtResult::HaveMatrixStmt(success) => success,
        }
    }
}
