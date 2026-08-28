//! Proof block results.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn proof_block_stmt(
        &mut self,
        result: &SuccessProofBlockStmtResult,
    ) -> JsonValue {
        match result {
            SuccessProofBlockStmtResult::ClaimStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.claim_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ClaimStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessProofBlockStmtResult::ExampleStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.claim_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ExampleStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessProofBlockStmtResult::SketchStmt(result) => {
                let proof = result
                    .proof
                    .as_ref()
                    .map(|proof| {
                        object(vec![
                            string_field("kind", "SuccessSketchProofResult"),
                            (
                                "proof_scope".to_string(),
                                self.local_proof_scope(&proof.proof_scope),
                            ),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&proof.proof_steps),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "SketchStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("proof".to_string(), proof)],
                )
            }
            SuccessProofBlockStmtResult::TryStmt(result) => {
                let proof = result
                    .proof
                    .as_ref()
                    .map(|proof| {
                        object(vec![
                            string_field("kind", "SuccessTryProofResult"),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&proof.proof_steps),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "TryStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("proof".to_string(), proof)],
                )
            }
        }
    }
}
