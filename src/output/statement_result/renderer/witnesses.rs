//! Witness statements and existential/atomic witness verification.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn witness_stmt(
        &mut self,
        result: &SuccessWitnessStmtResult,
    ) -> JsonValue {
        match result {
            SuccessWitnessStmtResult::WitnessExistFact(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.witness_exist_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessExistFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessWitnessStmtResult::WitnessAtomicFact(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.witness_atomic_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessAtomicFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessWitnessStmtResult::WitnessNonemptySet(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyWitnessNonemptySetResult"),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "nonempty_check".to_string(),
                                self.stmt_result(&verification.nonempty_check),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessNonemptySet",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
        }
    }

    pub(in super::super) fn witness_exist_verification(
        &mut self,
        result: &SuccessVerifyWitnessExistResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyWitnessExistResult"),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            (
                "parameter_checks".to_string(),
                array(
                    result
                        .parameter_checks
                        .iter()
                        .map(|result| {
                            result
                                .as_ref()
                                .map(|result| self.stmt_result(result))
                                .unwrap_or(JsonValue::Null)
                        })
                        .collect(),
                ),
            ),
            (
                "body_checks".to_string(),
                self.stmt_results(&result.body_checks),
            ),
            (
                "uniqueness_check".to_string(),
                result
                    .uniqueness_check
                    .as_ref()
                    .map(|result| self.stmt_result(result))
                    .unwrap_or(JsonValue::Null),
            ),
        ])
    }

    pub(in super::super) fn witness_atomic_verification(
        &mut self,
        result: &SuccessVerifyWitnessAtomicFactResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyWitnessAtomicFactResult"),
            string_field("definition", result.definition.to_string()),
            string_field(
                "instantiated_existential",
                result.instantiated_existential.to_string(),
            ),
            (
                "definition_parameter_verification".to_string(),
                args_satisfy_param_def_verification_value(
                    self,
                    &result.definition_parameter_verification,
                ),
            ),
            (
                "witness_verification".to_string(),
                self.witness_exist_verification(&result.witness_verification),
            ),
        ])
    }
}
