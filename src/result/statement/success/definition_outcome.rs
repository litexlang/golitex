//! Top-level successful definition statement outcome.

use crate::prelude::*;

pub enum SuccessDefinitionStmtResult {
    LetObjStmt(Box<SuccessLetObjStmtResult>),
    HaveObjInNonemptySetStmt(Box<SuccessHaveObjInNonemptySetStmtResult>),
    HaveObjEqualStmt(Box<SuccessHaveObjEqualStmtResult>),
    HaveObjByExistFactsStmt(Box<SuccessHaveObjByExistFactsStmtResult>),
    ObtainObjFromExistFact(Box<SuccessObtainObjFromExistFactResult>),
    ObtainObjFromAtomicFact(Box<SuccessObtainObjFromAtomicFactResult>),
    ObtainObjFromThm(Box<SuccessObtainObjFromThmResult>),
    HaveByPreimageStmt(Box<SuccessHaveByPreimageStmtResult>),
    HaveFnEqualStmt(Box<SuccessHaveFnEqualStmtResult>),
    HaveFnEqualCaseByCaseStmt(Box<SuccessHaveFnEqualCaseByCaseStmtResult>),
    HaveFnByInducStmt(Box<SuccessHaveFnByInducStmtResult>),
    HaveFnByForallExistUniqueStmt(Box<SuccessHaveFnByForallExistUniqueStmtResult>),
    HaveTupleStmt(Box<SuccessHaveTupleStmtResult>),
    HaveCartStmt(Box<SuccessHaveCartStmtResult>),
    HaveSeqStmt(Box<SuccessHaveSeqStmtResult>),
    HaveFiniteSeqStmt(Box<SuccessHaveFiniteSeqStmtResult>),
    HaveMatrixStmt(Box<SuccessHaveMatrixStmtResult>),
    DefPropStmt(Box<SuccessDefPropStmtResult>),
    DefAbstractPropStmt(Box<SuccessDefAbstractPropStmtResult>),
    DefSettingStmt(Box<SuccessDefSettingStmtResult>),
    DefTemplateStmt(Box<SuccessDefTemplateStmtResult>),
    DefStructStmt(Box<SuccessDefStructStmtResult>),
    DefAlgoStmt(Box<SuccessDefAlgoStmtResult>),
    DefThmStmt(Box<SuccessDefThmStmtResult>),
    AxiomStmt(Box<SuccessAxiomStmtResult>),
    DefStrategyStmt(Box<SuccessDefStrategyStmtResult>),
}
