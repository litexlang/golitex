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
                let execution = match &result.execution {
                    TryStmtExecutionResult::Committed(proof) => object(vec![
                        string_field("kind", "Committed"),
                        (
                            "proof_steps".to_string(),
                            self.stmt_results(&proof.proof_steps),
                        ),
                    ]),
                    TryStmtExecutionResult::RolledBack(error) => object(vec![
                        string_field("kind", "RolledBack"),
                        ("error".to_string(), self.try_rollback_error(error)),
                    ]),
                    TryStmtExecutionResult::SkippedByTrustedExecution => {
                        object(vec![string_field("kind", "SkippedByTrustedExecution")])
                    }
                };
                self.non_fact_stmt(
                    "TryStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("execution".to_string(), execution)],
                )
            }
        }
    }

    fn try_rollback_error(&mut self, error: &RuntimeError) -> JsonValue {
        let details = runtime_error_details(error);
        let output = details.output.as_ref();
        let unknown_result = output
            .unknown_result
            .as_ref()
            .map(|unknown| match unknown {
                RuntimeErrorUnknownResult::Generic(unknown) => unknown.to_string(),
                RuntimeErrorUnknownResult::Fact(unknown) => unknown.to_string(),
            })
            .map(JsonValue::JsonString)
            .unwrap_or(JsonValue::Null);
        object(vec![
            string_field("error_type", error.display_label()),
            string_field("message", error.trace_message()),
            ("line".to_string(), JsonValue::Number(details.line_file.0)),
            string_field("file", details.line_file.1.to_string()),
            (
                "statement".to_string(),
                details
                    .statement
                    .as_ref()
                    .map(|statement| JsonValue::JsonString(statement.to_string()))
                    .unwrap_or(JsonValue::Null),
            ),
            (
                "inside_results".to_string(),
                self.stmt_results(&details.inside_results),
            ),
            (
                "failed_step".to_string(),
                output
                    .failed_step
                    .as_ref()
                    .map(|statement| JsonValue::JsonString(statement.to_string()))
                    .unwrap_or(JsonValue::Null),
            ),
            (
                "failed_goal".to_string(),
                output
                    .failed_goal
                    .as_ref()
                    .map(|goal| JsonValue::JsonString(goal.to_string()))
                    .unwrap_or(JsonValue::Null),
            ),
            ("unknown_result".to_string(), unknown_result),
            (
                "phases".to_string(),
                optional_trace(details.execution_trace.as_ref()),
            ),
            (
                "previous_error".to_string(),
                details
                    .previous_error
                    .as_ref()
                    .map(|previous| self.try_rollback_error(previous))
                    .unwrap_or(JsonValue::Null),
            ),
        ])
    }
}

fn runtime_error_details(error: &RuntimeError) -> &RuntimeErrorStruct {
    match error {
        RuntimeError::ArithmeticError(details)
        | RuntimeError::NewFactError(details)
        | RuntimeError::StoreFactError(details)
        | RuntimeError::ParseError(details)
        | RuntimeError::ExecStmtError(details)
        | RuntimeError::WellDefinedError(details)
        | RuntimeError::VerifyError(details)
        | RuntimeError::UnknownError(details)
        | RuntimeError::InferError(details)
        | RuntimeError::NameAlreadyUsedError(details)
        | RuntimeError::DefineParamsError(details)
        | RuntimeError::InstantiateError(details) => details,
    }
}
