//! Successful function-existence, tuple, sequence, and matrix definitions.

use crate::prelude::*;

pub struct SuccessHaveFnByForallExistUniqueStmtResult {
    pub statement: HaveFnByForallExistUniqueStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyFunctionFromUniqueExistenceResult>,
    /// Recursive WD evidence for the pointwise property published after the
    /// chosen function enters the environment.  This application does not
    /// exist while the source `forall ... exist!` proof is checked, so its
    /// evidence must be retained from the later publication phase.
    pub published_property_well_definedness: Option<WellDefinedFactResult>,
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
