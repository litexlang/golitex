//! Claim and theorem verification.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn claim_verification(
        &mut self,
        result: &SuccessVerifyClaimResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyClaimResult::Forall(result) => object(vec![
                string_field("kind", "SuccessVerifyClaimForallResult"),
                string_field("forall_fact", result.forall_fact.to_string()),
                (
                    "well_definedness".to_string(),
                    self.fact_well_definedness(&result.well_definedness),
                ),
                (
                    "proof_scope".to_string(),
                    self.local_proof_scope(&result.proof_scope),
                ),
                (
                    "proof_steps".to_string(),
                    self.stmt_results(&result.proof_steps),
                ),
                (
                    "conclusion_checks".to_string(),
                    self.stmt_results(&result.conclusion_checks),
                ),
            ]),
            SuccessVerifyClaimResult::Fact(result) => object(vec![
                string_field("kind", "SuccessVerifyClaimFactResult"),
                string_field("fact", result.fact.to_string()),
                (
                    "well_definedness".to_string(),
                    self.fact_well_definedness(&result.well_definedness),
                ),
                (
                    "proof_scope".to_string(),
                    self.local_proof_scope(&result.proof_scope),
                ),
                (
                    "proof_steps".to_string(),
                    self.stmt_results(&result.proof_steps),
                ),
                (
                    "conclusion_check".to_string(),
                    self.stmt_result(&result.conclusion_check),
                ),
            ]),
        }
    }

    pub(in super::super) fn theorem_verification(
        &mut self,
        result: &SuccessVerifyTheoremResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyTheoremResult"),
            string_field("name", result.name.clone()),
            string_field("forall_fact", result.forall_fact.to_string()),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            (
                "proof_scope".to_string(),
                self.local_proof_scope(&result.proof_scope),
            ),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            (
                "conclusion_checks".to_string(),
                self.stmt_results(&result.conclusion_checks),
            ),
        ])
    }
}
