//! Successful object binding and existential-elimination outcomes.

use crate::prelude::*;

pub struct SuccessLetObjStmtResult {
    pub statement: LetObjStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessHaveObjInNonemptySetStmtResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyObjectChoiceResult>,
}

pub struct SuccessHaveObjEqualStmtResult {
    pub statement: HaveObjEqualStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyHaveObjEqualResult>,
}

pub struct SuccessHaveObjByExistFactsStmtResult {
    pub statement: HaveObjByExistFactsStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromExistFactResult {
    pub statement: ObtainObjFromExistFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromAtomicFactResult {
    pub statement: ObtainObjFromAtomicFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromThmResult {
    pub statement: ObtainObjFromThm,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessHaveByPreimageStmtResult {
    pub statement: HaveByPreimageStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyPreimageResult>,
}
