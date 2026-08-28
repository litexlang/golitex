//! Successful function-existence, tuple, sequence, and matrix definitions.

use crate::prelude::*;

pub struct SuccessHaveFnByForallExistUniqueStmtResult {
    pub statement: HaveFnByForallExistUniqueStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyFunctionFromUniqueExistenceResult>,
}

pub struct SuccessHaveTupleStmtResult {
    pub statement: HaveTupleStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
}

pub struct SuccessHaveCartStmtResult {
    pub statement: HaveCartStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
}

pub struct SuccessHaveSeqStmtResult {
    pub statement: HaveSeqStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}

pub struct SuccessHaveFiniteSeqStmtResult {
    pub statement: HaveFiniteSeqStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}

pub struct SuccessHaveMatrixStmtResult {
    pub statement: HaveMatrixStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}
