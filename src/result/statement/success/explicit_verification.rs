//! Successful explicit proof-method outcomes.

use crate::prelude::*;

pub struct SuccessByCasesStmtResult {
    pub statement: ByCasesStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByCasesResult>,
}

pub struct SuccessByContraStmtResult {
    pub statement: ByContraStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByContraResult>,
}

pub struct SuccessByEnumerateFiniteSetStmtResult {
    pub statement: ByEnumerateFiniteSetStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateFiniteSetResult>,
}

pub struct SuccessByFiniteSetInducStmtResult {
    pub statement: ByFiniteSetInducStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByInducResult>,
}

pub struct SuccessByInducStmtResult {
    pub statement: ByInducStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByInducResult>,
}

pub struct SuccessByForStmtResult {
    pub statement: ByForStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByForResult>,
}

pub struct SuccessByExtensionStmtResult {
    pub statement: ByExtensionStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByExtensionResult>,
}

pub struct SuccessByEnumerateRangeStmtResult {
    pub statement: ByEnumerateRangeStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateRangeResult>,
}

pub struct SuccessByClosedRangeAsCasesStmtResult {
    pub statement: ByClosedRangeAsCasesStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateRangeResult>,
}

pub struct SuccessByTransitivePropStmtResult {
    pub statement: ByTransitivePropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessBySymmetricPropStmtResult {
    pub statement: BySymmetricPropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByReflexivePropStmtResult {
    pub statement: ByReflexivePropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByAntisymmetricPropStmtResult {
    pub statement: ByAntisymmetricPropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByZornLemmaStmtResult {
    pub statement: ByZornLemmaStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByAxiomOfChoiceStmtResult {
    pub statement: ByAxiomOfChoiceStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByRegularityAxiomStmtResult {
    pub statement: ByRegularityAxiomStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByDefStmtResult {
    pub statement: ByDefStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByDefinitionResult>,
}

pub struct SuccessByStructDefStmtResult {
    pub statement: ByStructDefStmt,
    pub common: SuccessStmtCommonResult,
    pub membership_check: Option<Box<StmtResult>>,
}

pub struct SuccessByThmStmtResult {
    pub statement: ByThmStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByTheoremSelectionResult>,
}

pub struct SuccessReleaseThmStmtResult {
    pub statement: ReleaseThmStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTheoremApplicationResult>,
}

pub enum SuccessByStmtResult {
    ByCasesStmt(Box<SuccessByCasesStmtResult>),
    ByContraStmt(Box<SuccessByContraStmtResult>),
    ByEnumerateFiniteSetStmt(Box<SuccessByEnumerateFiniteSetStmtResult>),
    ByFiniteSetInducStmt(Box<SuccessByFiniteSetInducStmtResult>),
    ByInducStmt(Box<SuccessByInducStmtResult>),
    ByForStmt(Box<SuccessByForStmtResult>),
    ByExtensionStmt(Box<SuccessByExtensionStmtResult>),
    ByEnumerateRangeStmt(Box<SuccessByEnumerateRangeStmtResult>),
    ByClosedRangeAsCasesStmt(Box<SuccessByClosedRangeAsCasesStmtResult>),
    ByTransitivePropStmt(Box<SuccessByTransitivePropStmtResult>),
    BySymmetricPropStmt(Box<SuccessBySymmetricPropStmtResult>),
    ByReflexivePropStmt(Box<SuccessByReflexivePropStmtResult>),
    ByAntisymmetricPropStmt(Box<SuccessByAntisymmetricPropStmtResult>),
    ByZornLemmaStmt(Box<SuccessByZornLemmaStmtResult>),
    ByAxiomOfChoiceStmt(Box<SuccessByAxiomOfChoiceStmtResult>),
    ByRegularityAxiomStmt(Box<SuccessByRegularityAxiomStmtResult>),
    ByDefStmt(Box<SuccessByDefStmtResult>),
    ByStructDefStmt(Box<SuccessByStructDefStmtResult>),
    ByThmStmt(Box<SuccessByThmStmtResult>),
}
