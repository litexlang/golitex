//! By-statement results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn by_stmt(&mut self, result: &SuccessByStmtResult) -> JsonValue {
        match result {
            SuccessByStmtResult::ByCasesStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.by_cases_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByCasesStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByContraStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.by_contra_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByContraStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByEnumerateFiniteSetStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        by_enumerate_finite_set_verification_value(self, verification)
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByEnumerateFiniteSetStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByFiniteSetInducStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_induc_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByFiniteSetInducStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByInducStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_induc_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByInducStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByForStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_for_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByForStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByExtensionStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_extension_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByExtensionStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByEnumerateRangeStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_enumerate_range_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByEnumerateRangeStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByClosedRangeAsCasesStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_enumerate_range_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByClosedRangeAsCasesStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByTransitivePropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByTransitivePropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::BySymmetricPropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "BySymmetricPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByReflexivePropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByReflexivePropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByAntisymmetricPropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByAntisymmetricPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByZornLemmaStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByZornLemmaStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByAxiomOfChoiceStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByAxiomOfChoiceStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByRegularityAxiomStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByRegularityAxiomStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByDefStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_definition_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByDefStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByStructDefStmt(result) => {
                let membership_check = result
                    .membership_check
                    .as_ref()
                    .map(|check| self.stmt_result(check))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByStructDefStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("membership_check".to_string(), membership_check)],
                )
            }
            SuccessByStmtResult::ByThmStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| theorem_selection_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByThmStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
        }
    }
}
