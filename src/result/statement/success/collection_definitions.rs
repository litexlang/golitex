//! Successful function-existence definitions.

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

