//! Statement outcome dispatch, common fields, lists, and unknown results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn stmt_result(&mut self, result: &StmtResult) -> JsonValue {
        match result {
            StmtResult::Success(success) => object(vec![
                string_field("outcome", "success"),
                ("result".to_string(), self.success_stmt(success)),
            ]),
            StmtResult::Unknown(unknown) => object(vec![
                string_field("outcome", "unknown"),
                ("result".to_string(), self.unknown_stmt(unknown)),
            ]),
        }
    }

    pub(in super::super) fn success_stmt(&mut self, success: &SuccessStmtResult) -> JsonValue {
        match success {
            SuccessStmtResult::Fact(result) => self.success_fact_stmt(result),
            SuccessStmtResult::UnsafeStmt(result) => match result {
                SuccessUnsafeStmtResult::TrustStmt(result) => self.non_fact_stmt(
                    "TrustStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
                SuccessUnsafeStmtResult::TrustHaveStmt(result) => self.non_fact_stmt(
                    "TrustHaveStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
            },
            SuccessStmtResult::Definition(result) => self.definition_stmt(result),
            SuccessStmtResult::ReleaseThmStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| theorem_application_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ReleaseThmStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessStmtResult::By(result) => self.by_stmt(result),
            SuccessStmtResult::Witness(result) => self.witness_stmt(result),
            SuccessStmtResult::ProofBlock(result) => self.proof_block_stmt(result),
            SuccessStmtResult::Command(result) => self.command_stmt(result),
        }
    }

    pub(in super::super) fn non_fact_stmt(
        &mut self,
        kind: &str,
        statement: String,
        common: &SuccessStmtCommonResult,
        mut specific_fields: Vec<(String, JsonValue)>,
    ) -> JsonValue {
        let mut fields = vec![
            string_field("kind", kind),
            string_field("statement", statement),
            ("common".to_string(), self.common(common)),
        ];
        fields.append(&mut specific_fields);
        object(fields)
    }

    pub(in super::super) fn common(&mut self, common: &SuccessStmtCommonResult) -> JsonValue {
        object(vec![(
            "infers".to_string(),
            infer_result_value(&common.infers),
        )])
    }

    pub(in super::super) fn stmt_results(&mut self, results: &[StmtResult]) -> JsonValue {
        array(
            results
                .iter()
                .map(|result| self.stmt_result(result))
                .collect(),
        )
    }

    pub(in super::super) fn unknown_stmt(&mut self, unknown: &UnknownStmtResult) -> JsonValue {
        match unknown {
            UnknownStmtResult::Generic(result) => object(vec![
                string_field("kind", "Generic"),
                (
                    "detail".to_string(),
                    optional_strings(result.detail.as_ref()),
                ),
            ]),
            UnknownStmtResult::Fact(result) => object(vec![
                string_field("kind", unknown_fact_kind(result)),
                string_field("goal", result.goal().to_string()),
                ("detail".to_string(), optional_strings(result.detail())),
            ]),
        }
    }
}
